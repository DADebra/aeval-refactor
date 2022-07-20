#!/bin/sh

cd "$(dirname "$0")/.."

git pull origin master
for module in $(ls .git/modules)
do
  branch=$(git config -f .gitmodules submodule.$module.branch)
  git -C $module pull origin $branch
  git -C $module checkout $branch
done
