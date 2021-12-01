#!/bin/sh

head="$(./context/files/get-head.sh ../.git)"
cp ../.git/refs/heads/$head ./context/files/commitsha
