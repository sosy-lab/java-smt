# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:24.04

# Avoid interactive prompts during apt installations
ENV DEBIAN_FRONTEND=noninteractive

# 1. Update and install Java 17 + Tomcat 10
RUN apt-get update && apt-get install -y \
    openjdk-17-jdk \
    tomcat10 \
    libgomp1 \
    && rm -rf /var/lib/apt/lists/*

# 2. Set the environment so Tomcat knows where everything is
ENV CATALINA_HOME=/usr/share/tomcat10
ENV CATALINA_BASE=/var/lib/tomcat10

# 3. Expose the default Tomcat port
EXPOSE 8080

# 4. Clean out default apps and copy your WAR file to the container
RUN rm -rf $CATALINA_BASE/webapps/*
COPY ./target/java-smt-web-example-2.0.war $CATALINA_BASE/webapps/ROOT.war

# 5. Run Tomcat in the foreground
CMD ["/usr/share/tomcat10/bin/catalina.sh", "run"]
