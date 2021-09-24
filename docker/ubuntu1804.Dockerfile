FROM ubuntu:bionic

RUN apt-get update \
 && apt-get install -y \
        wget curl git \
        build-essential cmake patchelf \
        openjdk-11-jdk ant maven \
        mingw-w64 zlib1g-dev

# Add the user "developer" with UID:1000, GID:1000, home at /developer.
# This allows to map the docker-internal user to the local user 1000:1000 outside of the container.
# This avoids to have new files created with root-rights.
RUN groupadd -r developer -g 1000 \
 && useradd -u 1000 -r -g developer -m -d /developer -s /sbin/nologin -c "JavaSMT Development User" developer \
 && chmod 755 /developer

USER developer
