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
    kotlin("jvm") version "1.6.21"

    // Apply the application plugin to add support for building a CLI application in Java.
    application
}

// Set the used Java version
java.sourceCompatibility = JavaVersion.VERSION_11

// Globally define versions used for our dependencies
val javasmtVersion = "3.12.0"
val javasmtYices2Version = "3.12.0"
val junit4Version = "4.13"
val z3Version = "4.8.17"
val smtInterpolVersion = "2.5-916-ga5843d8b"
val boolectorVersion = "3.2.2-g1a89c229"
val cvc4Version = "1.8-prerelease-2020-06-24-g7825d8f28"
val mathsat5Version = "5.6.6-sosy1"
val optiMathsat5Version = "1.7.1-sosy0"
val yices2Version = "2.6.2-396-g194350c1"
val princessVersion = "2021-11-15"

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

dependencies {
    // Align versions of all Kotlin components
    //implementation(platform("org.jetbrains.kotlin:kotlin-bom"))

    // Use the Kotlin JDK 11 standard library.
    //implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk11")

    // JUnit 4
	testImplementation("junit:junit:$junit4Version")

    // JavaSMT dependencies
    implementation("org.sosy-lab:java-smt:$javasmtVersion")

    // JavaSMT solver dependencies
    // Z3
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:com.microsoft.z3@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-z3:$z3Version:libz3java@so")
    
    runtimeOnly("org.sosy-lab:javasmt-solver-mathsat5:$mathsat5Version:libmathsat5j@so")

    // Retrieve OptiMathSAT via Ivy (as it is currently not available in Maven)
	runtimeOnly("org.sosy_lab:javasmt-solver-optimathsat:$optiMathsat5Version:liboptimathsat5j@so")

    // Retrieve CVC4 via Maven
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:CVC4@jar")
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4jni@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-cvc4:$cvc4Version:libcvc4parser@so")

    // Retrieve Boolector via Maven
    runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libboolector@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libminisat@so")
    runtimeOnly("org.sosy-lab:javasmt-solver-boolector:$boolectorVersion:libpicosat@so")

    // Retrieve Princess
    runtimeOnly("io.github.uuverifiers:princess_2.13:$princessVersion@jar")
  
    // Retrieve SMTInterpol
    runtimeOnly("de.uni-freiburg.informatik.ultimate:smtinterpol:$smtInterpolVersion@jar")
  
    // Example as to how to use Yices2
    // First get JavaSMT for Yices2 from Maven (if you want to use only Yices2 use this dependency in the "implementation" part above instead of regual JavaSMT)
    runtimeOnly("org.sosy-lab:javasmt-yices2:$javasmtYices2Version@jar")
    // And the Yices2 solver from Maven
    runtimeOnly("org.sosy-lab:javasmt-solver-yices2:$yices2Version:libyices2j@so")
  

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

// compile bytecode to java 11
tasks.withType<KotlinCompile> {
    kotlinOptions.jvmTarget = "11"
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