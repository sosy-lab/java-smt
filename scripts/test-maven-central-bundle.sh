#!/usr/bin/env bash

#
# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0
#

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Extensions to check for each base file
EXTENSIONS=("" ".asc" ".md5" ".sha1" ".sha256" ".sha512")

# Ensure script is run from project root
if [[ ! -f "build.xml" ]]; then
    echo -e "${RED}Error: This script must be run from the project root.${NC}"
    exit 1
fi

verify_bundle() {
    local COMPONENT=$1
    local VERSION=$2
    local FULL_NAME=$3
    local EXPECTED_DEP_STATUS=$4 # "none", "compile", or "compile+optional"
    shift 4
    local BASE_FILES=("$@")

    local REL_DIR="org/sosy-lab/${FULL_NAME}/${VERSION}"
    local ZIP_FILE="dist/maven-central-bundle/${COMPONENT}-${VERSION}-bundle.zip"
    local TEMP_DIR=$(mktemp -d)
    local POM_FILE="${TEMP_DIR}/${REL_DIR}/${FULL_NAME}-${VERSION}.pom"

    echo -e "${BLUE}------------------------------------------------------------${NC}"
    echo -e "${YELLOW}Testing component: ${COMPONENT} (version: ${VERSION})${NC}"
    echo -e "${BLUE}------------------------------------------------------------${NC}"

    # Cleanup local bundle dir for this component if it exists
    rm -rf "dist/maven-central-bundle/${REL_DIR}"

    # Execute ant command
    echo -e "${BLUE}Executing ant publish-to-maven-central...${NC}"
    ant publish-to-maven-central -Dpublish.component="${COMPONENT}" -Dpublish.version="${VERSION}" -Dpublish.upload=false
    echo -e "${BLUE}------------------------------------------------------------${NC}"

    # Check if zip file exists
    if [[ ! -f "${ZIP_FILE}" ]]; then
        echo -e "${RED}Error: Zip file ${ZIP_FILE} was not created.${NC}"
        exit 1
    fi

    # Unzip to temp directory
    echo -e "${BLUE}Unzipping bundle for verification...${NC}"
    unzip -q "${ZIP_FILE}" -d "${TEMP_DIR}"

    # Verify file structure
    echo -e "${BLUE}Verifying file structure in the zip bundle...${NC}"

    local EXPECTED_FILES_FILE="${TEMP_DIR}/expected_files.txt"
    local ACTUAL_FILES_FILE="${TEMP_DIR}/actual_files.txt"

    # Generate expected files list
    for base in "${BASE_FILES[@]}"; do
        for ext in "${EXTENSIONS[@]}"; do
            echo "${REL_DIR}/${base}${ext}" >> "${EXPECTED_FILES_FILE}"
        done
    done
    sort -o "${EXPECTED_FILES_FILE}" "${EXPECTED_FILES_FILE}"

    # Generate actual files list
    find "${TEMP_DIR}/${REL_DIR}" -type f | sed "s|^${TEMP_DIR}/||" | sort > "${ACTUAL_FILES_FILE}"

    # Compare lists
    local DIFF=$(diff -u "${EXPECTED_FILES_FILE}" "${ACTUAL_FILES_FILE}" || true)

    local FAILED=0
    if [[ -n "${DIFF}" ]]; then
        echo -e "${RED}Verification failed for ${COMPONENT}!${NC}"
        echo "Differences found:"
        echo "${DIFF}"
        FAILED=1
    fi

    # Verify POM content (dependencies)
    echo -e "${BLUE}Verifying POM content (dependencies) for ${COMPONENT}...${NC}"
    if [[ "$EXPECTED_DEP_STATUS" == "none" ]]; then
        if grep -q "<dependencies>" "$POM_FILE"; then
            echo -e "${RED}Error: POM for ${COMPONENT} should not have dependencies.${NC}"
            FAILED=1
        fi
    elif [[ "$EXPECTED_DEP_STATUS" == "compile" ]]; then
        if ! grep -q "<scope>compile</scope>" "$POM_FILE"; then
            echo -e "${RED}Error: POM for ${COMPONENT} should have compile dependencies.${NC}"
            FAILED=1
        fi
        if grep -q "<optional>true</optional>" "$POM_FILE"; then
            echo -e "${RED}Error: POM for ${COMPONENT} should not have optional dependencies.${NC}"
            FAILED=1
        fi
    elif [[ "$EXPECTED_DEP_STATUS" == "compile+optional" ]]; then
        if ! grep -q "<scope>compile</scope>" "$POM_FILE"; then
            echo -e "${RED}Error: POM for ${COMPONENT} should have compile dependencies.${NC}"
            FAILED=1
        fi
        if ! grep -q "<optional>true</optional>" "$POM_FILE"; then
            echo -e "${RED}Error: POM for ${COMPONENT} should have optional dependencies.${NC}"
            FAILED=1
        fi
    fi

    rm -rf "${TEMP_DIR}"
    if [[ $FAILED -eq 0 ]]; then
        echo -e "${GREEN}Verification successful for ${COMPONENT}!${NC}"
        return 0
    else
        return 1
    fi
}

# Cleanup all bundles before starting
echo -e "${YELLOW}Cleaning up dist/ directory...${NC}"
rm -rf dist/maven-central-bundle

FAILED_TESTS=0

# Test case: Z3
Z3_VERSION="4.16.0"
Z3_FULL_NAME="javasmt-solver-z3"
Z3_BASE_FILES=(
    "${Z3_FULL_NAME}-${Z3_VERSION}.jar"
    "${Z3_FULL_NAME}-${Z3_VERSION}.pom"
    "${Z3_FULL_NAME}-${Z3_VERSION}-javadoc.jar"
    "${Z3_FULL_NAME}-${Z3_VERSION}-sources.jar"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3-arm64.dll"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3-arm64.dylib"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3-arm64.so"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3-x64.dll"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3-x64.dylib"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3-x64.so"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3java-arm64.dll"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3java-arm64.dylib"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3java-arm64.so"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3java-x64.dll"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3java-x64.dylib"
    "${Z3_FULL_NAME}-${Z3_VERSION}-libz3java-x64.so"
)

if ! verify_bundle "javasmt-solver-z3" "${Z3_VERSION}" "${Z3_FULL_NAME}" "none" "${Z3_BASE_FILES[@]}"; then
    FAILED_TESTS=$((FAILED_TESTS + 1))
fi

# Test case: MathSAT
MATHSAT_VERSION="5.6.10"
MATHSAT_FULL_NAME="javasmt-solver-mathsat"
MATHSAT_BASE_FILES=(
    "${MATHSAT_FULL_NAME}-${MATHSAT_VERSION}-libmathsat5j.so"
    "${MATHSAT_FULL_NAME}-${MATHSAT_VERSION}-mathsat.dll"
    "${MATHSAT_FULL_NAME}-${MATHSAT_VERSION}-mathsat5j.dll"
    "${MATHSAT_FULL_NAME}-${MATHSAT_VERSION}-mpir.dll"
    "${MATHSAT_FULL_NAME}-${MATHSAT_VERSION}.pom"
)

if ! verify_bundle "javasmt-solver-mathsat" "${MATHSAT_VERSION}" "${MATHSAT_FULL_NAME}" "none" "${MATHSAT_BASE_FILES[@]}"; then
    FAILED_TESTS=$((FAILED_TESTS + 1))
fi

# Test case: JavaSMT-bindings for Yices2
YICES_VERSION="6.0.0-141-g04134287c"
YICES_FULL_NAME="javasmt-yices2"
YICES_BASE_FILES=(
    "${YICES_FULL_NAME}-${YICES_VERSION}.jar"
    "${YICES_FULL_NAME}-${YICES_VERSION}.pom"
    "${YICES_FULL_NAME}-${YICES_VERSION}-sources.jar"
)

if ! verify_bundle "javasmt-yices2" "${YICES_VERSION}" "${YICES_FULL_NAME}" "compile+optional" "${YICES_BASE_FILES[@]}"; then
    FAILED_TESTS=$((FAILED_TESTS + 1))
fi

# Test case: JavaSMT (Core)
JAVASMT_VERSION="5.0.0"
JAVASMT_FULL_NAME="java-smt"
JAVASMT_BASE_FILES=(
    "${JAVASMT_FULL_NAME}-${JAVASMT_VERSION}.jar"
    "${JAVASMT_FULL_NAME}-${JAVASMT_VERSION}.pom"
    "${JAVASMT_FULL_NAME}-${JAVASMT_VERSION}-sources.jar"
)

if ! verify_bundle "java-smt" "${JAVASMT_VERSION}" "${JAVASMT_FULL_NAME}" "compile+optional" "${JAVASMT_BASE_FILES[@]}"; then
    FAILED_TESTS=$((FAILED_TESTS + 1))
fi

echo -e "${BLUE}------------------------------------------------------------${NC}"
if [[ $FAILED_TESTS -eq 0 ]]; then
    echo -e "${GREEN}All tests passed successfully!${NC}"
    exit 0
else
    echo -e "${RED}$FAILED_TESTS test(s) failed!${NC}"
    exit 1
fi
