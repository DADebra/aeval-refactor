#!/bin/sh

set -e

head="$(/get-head.sh /freqhorn.git)"

mkdir -p /freqhorn /freqhorn-build
git-fs -o "rev=$head" /freqhorn.git /freqhorn
cd /freqhorn-build
cmake -DZ3_ROOT=/usr -DBoost_USE_STATIC_LIBS=OFF -DBoost_USE_STATIC_RUNTIME=OFF -DCMAKE_BUILD_TYPE=Release /freqhorn
cp -a /freqhorn/bench_horn ./
cp -a /freqhorn/grammars ./
make -j$(nproc) freqhorn
fusermount -u /freqhorn
