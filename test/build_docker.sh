#!/bin/sh

# Set FORCEBUILD to cause a build to unconditionally occur (even if it looks
#   like we don't need to).

cd "$(realpath $(dirname $0))"

. ./build_common.sh

# Variable determining if we need to rebuild; DON'T MODIFY HERE
NEEDBUILD=0

[ -n "$FORCEBUILD" ] && NEEDREBUILD=1

# Returns the date that image $1 was created as seconds since UNIX epoch
imagecreatedate() {
    date -u -d "$(docker inspect --format='{{.Created}}' $1)" +%s
}


# Returns the date that image $1 was last tagged as seconds since UNIX epoch
imagetagdate() {
    # We're stripping off the human-readable timezone spec ("EST" for me)
    date -u -d "$(docker inspect --format='{{.Metadata.LastTagTime}}' $1 | sed -r 's/ [A-Z]*$//g')" +%s
}

# Returns the date that file $1 was last modified as seconds since UNIX epoch
filedate() {
    stat -c "%Y" "$1"
}

# When the image was last updated
olddate="$(imagetagdate freqhorn-test)"

# Check modification times of relevant files; if newer, we need to build
for file in $0 ./context/files/get-head.sh ./context/files/do-build.sh $(find ./context/tests -type f)
do
    if [ $(filedate $file) -gt $olddate ]
    then
        NEEDBUILD=1
        break
    fi
done

# Build 'shared' stage
shared_iid_file="$(mktemp)"
docker build --target shared --iidfile "$shared_iid_file" -f Dockerfile ./context
shared="$(cat "$shared_iid_file")"
shareddate="$(imagecreatedate $shared)"
[ $shareddate -gt $olddate ] && NEEDBUILD=1

# Build 'build' stage
build_iid_file="$(mktemp)"
docker build --target build --iidfile "$build_iid_file" -f Dockerfile ./context
build="$(cat "$build_iid_file")"
builddate="$(imagecreatedate $build)"
[ $builddate -gt $olddate ] && NEEDBUILD=1

# Cleanup
rm "$shared_iid_file" "$build_iid_file"

# Check to see if a commit has happened since last build
oldsha="$(docker inspect --format='{{.Config.Labels.commitsha}}' freqhorn-test)"
newsha="$(cat ./context/files/commitsha)"
[ "$oldsha" != "$newsha" ] && NEEDBUILD=1

if [ "$NEEDBUILD" = "1" ]
then
    build_cid_file="$(mktemp -u)"
    docker run --cidfile "$build_cid_file" --cap-add=CAP_SYS_ADMIN --device /dev/fuse -v "$(realpath ../.git):/freqhorn.git:ro" $build /do-build.sh
    freqhornbuild_con="$(cat "$build_cid_file")"
    rm "$build_cid_file"

    freqhornbin="$(mktemp)"
    docker cp $freqhornbuild_con:/freqhorn-build/tools/deep/freqhorn "$freqhornbin"
    docker rm $freqhornbuild_con > /dev/null

    run_con="$(docker run -d $shared)"
    docker cp "$freqhornbin" $run_con:/usr/bin/freqhorn
    rm "$freqhornbin"
    docker cp ./context/tests $run_con:/freqhorn-test
    docker cp ./context/files/commitsha $run_con:/commitsha
    docker commit -c "WORKDIR /freqhorn-test" -c "CMD run_tests.sh" -c 'ENV PATH="$PATH:/freqhorn-test"' -c "LABEL commitsha=$(cat ./context/files/commitsha)" $run_con freqhorn-test:latest
    docker rm $run_con > /dev/null
fi
