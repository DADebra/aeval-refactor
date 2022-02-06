FROM alpine:latest AS shared

RUN apk --no-cache add boost boost-coroutine boost-context boost-system gmp fuse z3 diffutils

FROM shared AS build

RUN apk --no-cache add cmake g++ make z3-dev boost-dev gmp-dev git fuse-dev libgit2-dev patch

COPY files/git-fs.patch files/makefile.patch /
ARG gitfscommit=2d03125b05bc9c6f55f25647d9cb92a34ebe958b
RUN git clone 'https://github.com/webconverger/git-fs' -o $gitfscommit --depth 1 /git-fs && cd /git-fs && patch git-fs.c /git-fs.patch && patch Makefile /makefile.patch && make && cp /git-fs/git-fs /usr/bin/git-fs

COPY files/do-build.sh files/get-head.sh /

FROM build AS freqhorn-build
COPY files/commitsha /
RUN /do-build.sh

FROM shared AS run

# NOTE: Any time anything below here is updated, you HAVE to update
# build_docker.sh as well!

COPY --from=freqhorn-build /freqhorn-build/tools/deep/freqhorn /usr/bin/freqhorn
COPY --from=freqhorn-build /freqhorn-build/bench_horn /bench_horn
COPY --from=freqhorn-build /freqhorn-build/grammars /grammars
COPY files/commitsha /
COPY tests /freqhorn-test

WORKDIR /freqhorn-test
ENV PATH="$PATH:/freqhorn-test"
ENV BENCHDIR="/bench_horn"
ENV GRAMDIR="/grammars"
CMD run_tests.sh
