#!/bin/sh

cd "$(realpath $(dirname $0))"

. ./build_common.sh

shared_iid_file="$(mktemp)"
docker build --target shared --iidfile "$shared_iid_file" -f Dockerfile ./context
shared="$(cat "$shared_iid_file")"
build_iid_file="$(mktemp)"
docker build --target build --iidfile "$build_iid_file" -f Dockerfile ./context
build="$(cat "$build_iid_file")"
rm "$shared_iid_file" "$build_iid_file"

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
docker commit -c "WORKDIR /freqhorn-test" -c "CMD partial_test.sh" -c 'ENV PATH="$PATH:/freqhorn-test"' -c "LABEL commitsha=$(cat ./context/files/commitsha)" $run_con freqhorn-test:latest
docker rm $run_con > /dev/null
