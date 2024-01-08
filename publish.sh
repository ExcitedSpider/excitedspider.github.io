#!/bin/bash
set -e

branch_name="pub"

# Check if the branch exists
if git rev-parse --verify "$branch_name" >/dev/null 2>&1; then
  # Switch to the existing branch
  git checkout "$branch_name"
else
  # Create and switch to a new branch
  git checkout -b "$branch_name"
fi

git reset --hard master
bundle exec jekyll build
git add .
git commit -m "chore: generate a static site"
git push --set-upstream origin pub

rm -rf docs
git checkout master