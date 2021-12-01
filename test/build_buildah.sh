#!/bin/sh

cd "$(realpath $(dirname $0))"

. ./build_common.sh

exec buildah bud --cap-add=CAP_SYS_ADMIN --device /dev/fuse --layers -f Dockerfile -t freqhorn-test:latest -v "$(realpath ../.git):/freqhorn.git:ro" --label "commitsha=$head" ./context
