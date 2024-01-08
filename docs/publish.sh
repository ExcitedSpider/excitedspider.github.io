git checkout -b pub
git reset --hard master
bundle exec jekyll build
git add .
git commit -m "chore: generate a static site"
git push --set-upstream origin pub

rm -rf docs
git checkout master