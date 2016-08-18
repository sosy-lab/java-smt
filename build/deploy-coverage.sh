#!/bin/bash
set -e # exit with nonzero exit code if anything fails

COVERAGE_FILE=junit/coverage.xml

if ! [ -f "$COVERAGE_FILE" ] ; then
  echo "Missing file $COVERAGE_FILE" >&2
  exit 1
fi

# From https://github.com/codacy/codacy-coverage-reporter#setup and
# https://www.jpm4j.org/#!/md/linux
curl -sL https://github.com/jpm4j/jpm4j.installers/raw/master/dist/biz.aQute.jpm.run.jar > jpm4j.jar

java -jar jpm4j.jar -u init

~/jpm/bin/jpm install com.codacy:codacy-coverage-reporter:assembly

# Show version
~/jpm/bin/codacy-coverage-reporter --help | head -n 1

~/jpm/bin/codacy-coverage-reporter -l Java -r "$COVERAGE_FILE"
