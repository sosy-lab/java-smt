// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

// This is an example for Gradle usage in Kotlin with Kotlin in Gradle

import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    // Apply the kotlin.jvm plugin to add support for Kotlin.
    kotlin("jvm") version "2.3.21"

    // Apply the application plugin to add support for building a CLI application in Java.
    application
}

// Globally define versions used for our dependencies
val javasmtVersion = "6.0.0-148-gba08f432a"
val javasmtYices2Version = "6.0.0-141-g04134287c"

val bitwuzlaVersion = "0.9.0-gd13ef925"
val boolectorVersion = "3.2.2-g1a89c229"
val cvc4Version = "1.8-prerelease-2020-06-24-g7825d8f28"
val cvc5Version = "2026-02-26-d22638a"
val mathsat5Version = "5.6.15"
val opensmtVersion = "2.9.2-ge4c80308"
val smtInterpolVersion = "2.5-1242-g5c50fb6d"
val princessVersion = "2025-11-17"
val ostrichVersion = "2.0"
val yices2Version = "2.7.0-gdc5687ca"
val z3Version = "4.16.0"
val z3LegacyVersion = "4.5.0-gd57a2a6dc"

val junit6Version = "6.1.0"

repositories {
    // Use MavenCentral as a source, but try using POMs first and if that fails just use the artifact
    mavenCentral {
        metadataSources {
            mavenPom()
        }
    }
    mavenCentral {
        metadataSources {
            artifact()
        }
    }

    // Ivy can be used as an alternative to MavenCentral
    ivy {
        url = uri("https://www.sosy-lab.org/ivy")
        patternLayout {
            artifact("/[organisation]/[module]/[classifier]-[revision].[ext]")
        }
        metadataSources {
            artifact()
        }
    }
}

val architecture = "x64"

dependencies {
    // Align versions of all Kotlin components
    implementation(platform("org.jetbrains.kotlin:kotlin-bom"))

    // JUnit
    testImplementation("org.junit.jupiter:junit-jupiter-api:$junit6Version")
    testImplementation("org.junit.jupiter:junit-jupiter-params:$junit6Version")
    testImplementation("org.junit.jupiter:junit-jupiter-engine:$junit6Version")

    // JavaSMT dependencies
    implementation("org.sosy-lab:java-smt:$javasmtVersion")

    // JavaSMT solver dependencies
    // Princess
    implementation("io.github.uuverifiers:princess_2.13:$princessVersion")
    implementation("io.github.uuverifiers:ostrich_2.13:$ostrichVersion")

    // SMTInterpol
    implementation("de.uni-freiburg.informatik.ultimate:smtinterpol:$smtInterpolVersion")

    // Mathsat5
    runtimeOnly("org.sosy-lab:javasmt-solver-mathsat:$mathsat5Version:libmathsat5j-${architecture}@so")

    // Z3
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-${architecture}@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-${architecture}@so")

    // Z3 4.5
    runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:com.microsoft.z3legacy@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:libz3legacy-${architecture}@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:libz3javalegacy-${architecture}@so")

    // Bitwuzla
    runtimeOnly("org.sosy-lab:javasmt-solver-bitwuzla:$bitwuzlaVersion@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-bitwuzla:$bitwuzlaVersion:libbitwuzlaj-${architecture}@so")

    // CVC4
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:CVC4@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4jni@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4parser@so")

    // CVC5
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version:libcvc5jni-${architecture}@so")

    // Boolector
    runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libboolector@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libminisat@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libpicosat@so")

    // Yices2
    runtimeOnly("org.sosy-lab:javasmt-yices2:$javasmtYices2Version@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-yices2:$yices2Version@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-yices2:$yices2Version:libyices2java-${architecture}@so")

    // OpenSMT
    runtimeOnly("org.sosy-lab:javasmt-solver-opensmt:$opensmtVersion@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-opensmt:$opensmtVersion:libopensmtj-${architecture}@so")

    // Tell implementation config to use the JavaSMT + dependencies from our dependencies folder
    implementation(fileTree("dir" to "build/dependencies", "include" to "*.jar"))
}

// Not really used in the current example, just here for completeness sake
testing {
    suites {
        // Configure the built-in test suite
        val test by getting(JvmTestSuite::class) {
            // Use Kotlin Test test framework
            useKotlinTest()
        }
    }
}

// Define the main class for the application.
application {
    mainClass.set("org.sosy_lab.java_smt_example.JavaSMTKotlinExampleKt")
}

// Use a config to identify JavaSMT components
configurations {
    register("javaSMTConfig").configure {
        dependencies.addAll(runtimeOnly.get().dependencies.filter { it.group == "org.sosy-lab" })
        dependencies.addAll(implementation.get().dependencies.filter { it.group == "org.sosy-lab" })
    }
}

// JavaSMT needs the solver dependencies in a particular folder structure; in the same folder as JavaSMT is the easiest.
// Also we need to rename some solver dependencies.
// Clean, then copy all JavaSMT components into the build/dependencies folder, rename and use it from there
tasks.register<Copy>("copyDependencies") {
    dependsOn("cleanDownloadedDependencies")
    from(configurations["javaSMTConfig"])
    into("build/dependencies")
    rename(".*(lib[^-]*)-?.*.so", "\$1.so")
}

// Cleanup task for the JavaSMT components/dependencies
tasks.register<Delete>("cleanDownloadedDependencies") {
    delete(file("build/dependencies"))
}

// Always copy the dependencies for JavaSMT when compiling
tasks.compileKotlin {
    dependsOn("copyDependencies")
}

// Use the cleanup task for JavaSMT declared above when cleaning
tasks.clean {
    dependsOn("cleanDownloadedDependencies")
}

// Set duplicate strategies to remove a warning
tasks.withType<Tar> {
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE
}

tasks.withType<Zip>{
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE
}
