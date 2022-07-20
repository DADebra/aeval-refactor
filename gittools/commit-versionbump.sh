#!/bin/sh

cd "$(dirname "$0")/.."

git add $(ls .git/modules)
{
  echo 'Version Bump'
  echo
  git diff --submodule=log --staged | grep -v 'untracked content'
} | git commit -F -
