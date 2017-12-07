#!/bin/bash
set -e # exit with nonzero exit code if anything fails

COVERAGE_FILE=junit/coverage.xml

if ! [ -f "$COVERAGE_FILE" ] ; then
  echo "Missing file $COVERAGE_FILE" >&2
  exit 1
fi

# From https://github.com/codacy/codacy-coverage-reporter#travis-ci
CODACY_COVERAGE_REPORTER_RELEASE="$(curl -H "Authorization: token ${GH_TOKEN}" https://api.github.com/repos/codacy/codacy-coverage-reporter/releases/latest)"
CODACY_COVERAGE_REPORTER_URL="$(echo $CODACY_COVERAGE_REPORTER_RELEASE | jq -r .assets[0].browser_download_url)"
if [ "$CODACY_COVERAGE_REPORTER_URL" = "null" ]; then
  echo "Failed to get information about coday coverage reporter from GitHub:"
  echo "$CODACY_COVERAGE_REPORTER_RELEASE"
  exit 1
fi

echo "Downloading Codacy Coverage Reporter from $CODACY_COVERAGE_REPORTER_URL"
wget -O codacy-coverage-reporter-assembly-latest.jar "$CODACY_COVERAGE_REPORTER_URL"

# Show version
java -cp codacy-coverage-reporter-assembly-latest.jar com.codacy.CodacyCoverageReporter --help | head -n 1

java -cp codacy-coverage-reporter-assembly-latest.jar com.codacy.CodacyCoverageReporter -l Java -r "$COVERAGE_FILE"
