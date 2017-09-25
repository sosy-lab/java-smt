#!/bin/bash
set -e # exit with nonzero exit code if anything fails

rm -rf gh-pages || true
mkdir -p gh-pages/api
cp -r website/* gh-pages
cp -r Javadoc/* gh-pages/api
cp bin/org/sosy_lab/java_smt/ConfigurationOptions.txt gh-pages/

cd gh-pages
git init

# inside this git repo we'll pretend to be a new user
git config user.name "${GIT_NAME}"
git config user.email "${GIT_EMAIL2}"

# The first and only commit to this new Git repo contains all the
# files present with the commit message "Deploy to GitHub Pages".
git add .
git commit -m "Deploy to GitHub Pages"

# Force push from the current repo's master branch to the remote
# repo's gh-pages branch. (All previous history on the gh-pages branch
# will be lost, since we are overwriting it.) We redirect any output to
# /dev/null to hide any sensitive credential data that might otherwise be exposed.
git push --force --quiet "https://${GH_TOKEN}@${GH_REF}" master:gh-pages > /dev/null 2>&1
