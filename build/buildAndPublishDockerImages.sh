#
# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0
#

set -e

JDK_VERSIONS="jdk-11 jdk-17 jdk-21 jdk-23"
DOCKER_PLATFORMS="linux/amd64,linux/arm64"
REGISTRY="registry.gitlab.com/sosy-lab/software/java-smt"

# podman login registry.gitlab.com

for JDK_VERSION in $JDK_VERSIONS; do
  IMAGE="test:$JDK_VERSION"
  DOCKER_FILE="gitlab-ci.Dockerfile.$JDK_VERSION"
  # cleanup old images
  podman image rm "$IMAGE" || true
  podman image rm "$REGISTRY/$IMAGE" || true
  # build new images
  podman build --platform "$DOCKER_PLATFORMS" --manifest "$IMAGE" -f "$DOCKER_FILE"
  podman tag "$IMAGE" "$REGISTRY/$IMAGE"
  podman manifest push --all "$REGISTRY/$IMAGE"
done
