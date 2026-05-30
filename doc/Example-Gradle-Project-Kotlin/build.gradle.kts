// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

// This is an example for Gradle usage in Kotlin with Kotlin in Gradle

import org.gradle.nativeplatform.platform.internal.DefaultNativePlatform
import org.jetbrains.kotlin.gradle.dsl.JvmTarget

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
val z3Version = "4.15.0"
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

val os = DefaultNativePlatform.getCurrentOperatingSystem()
val arch = DefaultNativePlatform.getCurrentArchitecture()

dependencies {
    // Align versions of all Kotlin components
    implementation(platform("org.jetbrains.kotlin:kotlin-bom"))

    // JUnit
    testImplementation("org.junit.jupiter:junit-jupiter-api:$junit6Version")
    testImplementation("org.junit.jupiter:junit-jupiter-params:$junit6Version")
    testImplementation("org.junit.jupiter:junit-jupiter-engine:$junit6Version")

    // JavaSMT dependencies
    implementation("org.sosy-lab:java-smt:$javasmtVersion")

    // Princess/Ostrich
    runtimeOnly("io.github.uuverifiers:princess_2.13:$princessVersion")
    runtimeOnly("io.github.uuverifiers:ostrich_2.13:$ostrichVersion")

    // SMTInterpol
    runtimeOnly("de.uni-freiburg.informatik.ultimate:smtinterpol:$smtInterpolVersion")

    // Z3
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version@jar")

    // Z3 4.5
    runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:com.microsoft.z3legacy@jar")

    // Bitwuzla
    runtimeOnly("org.sosy-lab:javasmt-solver-bitwuzla:$bitwuzlaVersion@jar")

    // CVC4
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:CVC4@jar")

    // CVC5
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version@jar")

    // Yices2
    runtimeOnly("org.sosy-lab:javasmt-yices2:$javasmtYices2Version@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-yices2:$yices2Version@jar")

    // OpenSMT
    runtimeOnly("org.sosy-lab:javasmt-solver-opensmt:$opensmtVersion@jar")

    when {
        os.isLinux() && arch.isAmd64() -> {
            // Mathsat5
            runtimeOnly("org.sosy-lab:javasmt-solver-mathsat:$mathsat5Version:libmathsat5j-x64@so")

            // Z3
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-x64@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-x64@so")

            // Z3 4.5
            runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:libz3legacy-x64@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:libz3javalegacy-x64@so")

            // Bitwuzla
            runtimeOnly("org.sosy-lab:javasmt-solver-bitwuzla:$bitwuzlaVersion:libbitwuzlaj-x64@so")

            // CVC4
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4jni@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4parser@so")

            // CVC5
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version:libcvc5jni-x64@so")

            // Boolector
            runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libboolector@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libminisat@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libpicosat@so")

            // Yices2
            runtimeOnly("org.sosy-lab:javasmt-solver-yices2:$yices2Version:libyices2java-x64@so")

            // OpenSMT
            runtimeOnly("org.sosy-lab:javasmt-solver-opensmt:$opensmtVersion:libopensmtj-x64@so")
        }

        os.isLinux() && arch.isArm64() -> {
            // Mathsat5
            runtimeOnly("org.sosy-lab:javasmt-solver-mathsat:$mathsat5Version:libmathsat5j-arm64@so")

            // Z3
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-arm64@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-arm64@so")

            // Z3 4.5
            runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:libz3legacy-arm64@so")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3-legacy:$z3LegacyVersion:libz3javalegacy-arm64@so")

            // Bitwuzla
            runtimeOnly("org.sosy-lab:javasmt-solver-bitwuzla:$bitwuzlaVersion:libbitwuzlaj-arm64@so")

            // CVC5
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version:libcvc5jni-arm64@so")

            // OpenSMT
            runtimeOnly("org.sosy-lab:javasmt-solver-opensmt:$opensmtVersion:libopensmtj-arm64@so")
        }

        os.isWindows() && arch.isAmd64() -> {
            // Mathsat5
            runtimeOnly("org.sosy-lab:javasmt-solver-mathsat:$mathsat5Version:mathsat5j-x64@dll")
            runtimeOnly("org.sosy-lab:javasmt-solver-mathsat:$mathsat5Version:mathsat-x64@dll")
            runtimeOnly("org.sosy-lab:javasmt-solver-mathsat:$mathsat5Version:gmp-x64@dll")

            // Z3
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-x64@dll")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-x64@dll")

            // Bitwuzla
            runtimeOnly("org.sosy-lab:javasmt-solver-bitwuzla:$bitwuzlaVersion:libbitwuzlaj-x64@dll")

            // CVC5
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version:libcvc5jni-x64@dll")

            // Yices2
            runtimeOnly("org.sosy-lab:javasmt-solver-yices2:$yices2Version:yices2java-x64@dll")
        }

        os.isWindows() && arch.isArm64() -> {
            // Z3
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-arm64@dll")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-arm64@dll")

            // CVC5
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version:libcvc5jni-arm64@dll")
        }

        os.isMacOsX() && arch.isAmd64() -> {
            // Z3
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-x64@dylib")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-x64@dylib")

            // CVC5
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version:libcvc5jni-x64@dylib")
        }

        os.isMacOsX() && arch.isArm64() -> {
            // Z3
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3-arm64@dylib")
            runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java-arm64@dylib")

            // CVC5
            runtimeOnly("org.sosy-lab:javasmt-solver-cvc5:$cvc5Version:libcvc5jni-arm64@dylib")
        }

        else -> error("Unsupported OS or architecture")
    }

    // Tell implementation config to use the JavaSMT + dependencies from our dependencies folder
    implementation(fileTree("dir" to "build/dependencies", "include" to "*.jar"))
}

// Configure tests
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

// Compile to Java 17
// JavaSMT requires at least Java 17, but a newer version could be used here
kotlin {
    compilerOptions {
        jvmTarget.set(JvmTarget.JVM_17)
    }
}
java.sourceCompatibility = JavaVersion.VERSION_17

// Use a config to identify JavaSMT components
configurations {
    register("javaSMTConfig").configure {
        dependencies.addAll(runtimeOnly.get().dependencies.filter { it.group == "org.sosy-lab" })
        dependencies.addAll(implementation.get().dependencies.filter { it.group == "org.sosy-lab" })
    }
}

fun shorten(full: String) : String {
    val regex = """(.*)(?:-x64|-arm64)\.(so|dll|dylib)$""".toRegex()
    val matchResult = regex.find(full)
    var clipped = ""
    if (matchResult != null) {
        val (prefix, suffix) = matchResult.destructured
        clipped = "$prefix.$suffix"
    } else {
        clipped = full
    }
    val regex2 = """.*-(.*).(so|dll|dylib)$""".toRegex()
    val matchResult2 = regex2.find(clipped)
    if (matchResult2 != null) {
        val (libname, suffix) = matchResult2.destructured
        return "$libname.$suffix"
    } else {
        return clipped
    }
}

// JavaSMT needs the solver dependencies in a particular folder structure; in the same folder as JavaSMT is the easiest.
// Also we need to rename some solver dependencies.
// Clean, then copy all JavaSMT components into the build/dependencies folder, rename and use it from there
tasks.register<Copy>("copyDependencies") {
    dependsOn("cleanDownloadedDependencies")
    from(configurations["javaSMTConfig"])
    into("build/dependencies")
    rename(::shorten)
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

tasks.withType<Zip> {
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE
}
