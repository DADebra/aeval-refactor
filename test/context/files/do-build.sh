#!/bin/sh

head="$(/get-head.sh /freqhorn.git)"

mkdir -p /freqhorn /freqhorn-build && git-fs -o "rev=$head" /freqhorn.git /freqhorn && cd /freqhorn-build && cmake -DZ3_ROOT=/usr -DBoost_USE_STATIC_LIBS=OFF -DBoost_USE_STATIC_RUNTIME=OFF /freqhorn && make -j4 freqhorn && fusermount -u /freqhorn
