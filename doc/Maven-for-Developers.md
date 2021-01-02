<!--
This file is part of JavaSMT,
an API wrapper for a collection of SMT solvers:
https://github.com/sosy-lab/java-smt

SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

Local Test for Maven (Still needs internet to pull dependencys for Maven)
0. If you are only interested in the JavaSMT part and know basic Maven, skip to 13.
1. Install Maven
2. Install Sonatype Nexus Repository Manager 3 (Free Version!)
  2.1 Download Nexus
  2.2 Unpack .tar
  2.3 Move Nexus-version and sonatype-work folders to where you want them (/usr/local/ for example)
  2.4 Change Folder permissions (chmod something)
3. Start Nexus with ./nexus start (file located in nexus-version/bin/ folder with version being the nexus version you use)
     (You can stop it with ./nexus stop )
4. Open a browser and enter: http://localhost:8081
5. Press Log in in the top right corner and enter the name: "admin" and search for the password in the file located at sonatype-work/nexus3/admin.password )
6. Optional: Change Password
7. Make a new User called "deployment" with a password of your choosing. (You can name it however you want. Just substitute deployment with your version from now on)
8. Go to the Maven Repo (~/.m2  most likely in the home dir. If you don't know where it is use this on the commandline:  mvn help:evaluate -Dexpression=settings.localRepository )
9. If a settings.xml is present save it, else make a new one. (Or edit your current one if you know what you are doing)
10. Enter the following into the settings.xml:
  (The urls are taken from the Nexus Repo. You can find them at http://localhost:8081 after logging in in the left menu on browse and copy the url of maven-snapshot/releases)
  (The username and password have to match the ones you entered in step 7, it does not matter how they are named)
  (If you do not want to use the release or the snapshot repo you can simply omit it here and in all further steps.)
  (Difference release vs snapshot: snapshots can be overridden with the same version number by deploying again. Release can NEVER be overridden by deploying)

```xml
<settings>
  <servers>
    <server>
      <id>nexusrepo</id>
      <username>deployment</username>
      <password>the_password_for_the_deployment_user</password>
    </server>
  </servers>

  <!-- You only need this if you want to make snapshots -->
  <profiles>
    <profile>
      <id>snapshot</id>
      <repositories>
        <repository>
          <id>nexus-snapshot-repo</id>
          <name>my snapshot repo</name>
          <url>http://localhost:8081/repository/maven-snapshots/</url>
        </repository>
      </repositories>
    </profile>
  
    <profile>
      <id>release</id>
      <repositories>
        <repository>
          <id>nexus-release-repo</id>
          <name>my release repo</name>
          <url>http://localhost:8081/repository/maven-releases/</url>
        </repository>
      </repositories>
    </profile>
  </profiles>

  <activeProfiles>
    <!--make the profile active all the time. You may change this as you want to use it. -->
    <activeProfile>release</activeProfile>
  </activeProfiles>
  </settings>
```

11. If you want to test a Project, download the test Project from Maven with the following command:
        mvn archetype:generate -DgroupId=com.mycompany.app -DartifactId=my-app -DarchetypeArtifactId=maven-archetype-quickstart -DarchetypeVersion=1.4 -DinteractiveMode=false
12. Now switch to the new folder called "my-app" and go through the existing pom.xml and copy the parts missing
    (copy it into a .xml so that you can read it easier):
   
```xml
  <?xml version="1.0" encoding="UTF-8"?>

  <project xmlns="http://maven.apache.org/POM/4.0.0" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xsi:schemaLocation="http://maven.apache.org/POM/4.0.0 http://maven.apache.org/xsd/maven-4.0.0.xsd">
  <!-- modelVersion is always 4.0.0 -->
  <modelVersion>4.0.0</modelVersion>
  <!-- self-explanatory -->
  <groupId>com.mycompany.app</groupId>
  <!-- Name of final artifact (it will consist of artifactId-version.type) -->
  <!-- If you want a static final name use finalName when building the jar) -->
  <artifactId>my-app</artifactId>
  <!--  Include -SNAPSHOT in the version for a snapshot  -->
  <version>1.0-SNAPSHOT</version>
  
  
  <!-- All dependencies are entered here. 
  The dependency-artifacts are named like this: artifactId-version.type with type=jar as standard.
  You should not use local dependencys that are not in your local repo as it may break Maven 
  (according to the documentation)
  If you have a different type than jar you need to specify it <type>so</type>
  If you want the dependency available just for a specific scope (i.e. testing)
  you may simply enter <scope>test</scope>
  More information: https://maven.apache.org/guides/introduction/introduction-to-dependency-mechanism.html -->
  <dependencies>
    <dependency>
      <groupId>junit</groupId>
      <artifactId>junit</artifactId>
      <version>4.10</version>
    </dependency>
  </dependencies>
  
  
  <!-- distributionManagement manages how you deploy your project. 
  You can use the following for the local Nexus server configured above -->
  <distributionManagement>
    <snapshotRepository>
      <id>nexusrepo</id>
      <name>My internal repository</name>
      <url>http://localhost:8081/repository/maven-snapshots/</url>
    </snapshotRepository>

    <repository>
      <id>nexusrepo</id>
      <name>My internal repository</name>
      <url>http://localhost:8081/repository/maven-releases/</url>
    </repository>
  </distributionManagement>
  
  <build>
  <!-- Here you can specify your plugins.
  The ones not in this example are not needed at the moment, but you don't need to delete them.
  Note: pluginManagement does manage them, not necassaryly execute. 
  For that you need either an execute block in the plugin
  (then it will get executed in the phase specified or in the default one for the plugin), execute it yourself via cmd 
  or simply use <plugins> instead of <pluginManagement>. I will show <plugins> in the JavaSMT example. -->
    <pluginManagement><!-- lock down plugins versions to avoid using Maven defaults (may be moved to parent pom) -->
      <plugins>
        <!-- clean lifecycle, see https://maven.apache.org/ref/current/maven-core/lifecycles.html#clean_Lifecycle -->
        <plugin>
          <!-- This compiles jars -->
          <artifactId>maven-compiler-plugin</artifactId>
          <version>3.8.0</version>
          <configuration>
            <!-- Enter the Java Version below that you have installed. i.e. 11 -->
            <release>11</release>
          </configuration>
        </plugin>
        <plugin>
        <!-- This tests the project. Careful because it does not use the system PATH(s) CLASSPATH etc.
             You need to specify all of those if you need them here! (See JavaSMT example) -->
          <artifactId>maven-surefire-plugin</artifactId>
          <version>2.22.1</version>
        </plugin>
        <plugin>
        <!-- Builds the jar. The jar will NOT be useable by: java -jar ...
            by default! You need to set the MANIFEST for this. 
            Also you need to set the classpath for the jar here if you need one that does not rely
            on the exact dependencies set in the dependency part of this pom.xml (See JavaSMT example)-->
          <artifactId>maven-jar-plugin</artifactId>
          <version>3.0.2</version>
          <!-- example MANIFEST for a usable jar that specifies the package and mainClass. -->
          <archive>
            <manifest>
              <mainClass>com.mycompany.app.App</mainClass>
            </manifest>
          </archive>
        </plugin>
        <plugin>
        <!-- Default deploy to the repository set above. This won't work for Maven-Central. -->
	         <artifactId>maven-deploy-plugin</artifactId>
	         <version>2.8.1</version>
	         <executions>
	          <execution>
	            <id>default-deploy</id>
	            <phase>deploy</phase>
	            <goals>
	            <goal>deploy</goal>
	            </goals>
	          </execution>
	        </executions>
	      </plugin>
      </plugins>
    </pluginManagement>
  </build>
</project>
```
	  
	  
In this testproject you can see and test some basic Maven ideas 
i.e. the folder structure, plugins, deployment etc.
Besides the pom.xml you can see the /src folder that will bring you to the test project and the tests for said project.
This folder layout is standard for maven and should be followed (src/main/java and src/test/java, after that you may change the names to your needs of course ;D )
See: https://maven.apache.org/guides/introduction/introduction-to-the-standard-directory-layout.html
We will cover changes in the JavaSMT example!
Open a terminal in the directory with the pom.xml and you may enter the following example commands:
mvn package        // (tests and packages the project. You will get the testresults in the cmd and a new folder target appears with the jar and classfiles etc.)
mvn clean          // (cleans the target folder etc.)
mvn clean package  // (first cleans, then uses package)
mvn deploy         // deploys the current project to the local Maven Repo with the set group/articactId and version and this pom.xml. 
                      This will use the active server from settings.xml.
                      You should be able to see the project on said server in the browser-interface.

## JavaSMT example from here:
-----------------------------------------------------------------
13. Use the following on the command line to deploy an artifact of your choise that was not compiled by Maven (For example shared libs or our projects)
  Using a pom.xml for this works BUT you would create 2 deployments. One for the pom.xml and then one extra for the deploy-file goal, so just stick with this for now.
  url = url of the server
  repository = same name you gave in the <server> entry of the settings.xml
  artifactId = name of the file (dependency) after deployment (do not use a file ending here)
  file = the file you want to deploy. You must be in the folder of the file or enter the path to it! You need the full filename including ending (.so for example).
  version = self-explenatory. Set it to your current version! Will get Appended to your artifactId for the final filename after deployment. No you can't just not enter one, i tried, i truly did....
  groupId = org.sosy-lab   (most likely, for testing not relevant)
  packaging = file ending i.e. so, jar etc. for the final deployed file
  pomDescription = String that describes the artifact (Optional)
  
  The below is an example for mathsat5 deployment. 
  You can look at it in the local nexus repo under "Browse" on the left side, maven-releases, org, sosy-lab, javasmt-mathsat5, 1.1


mvn deploy:deploy-file -Durl=http://localhost:8081/repository/maven-releases/ -DrepositoryId=nexusrepo -Dfile=libmathsat5j.so -DgroupId=org.sosy-lab -DartifactId=javasmt-solver-mathsat5 -Dversion=1.1 -Dpackaging=so -DgeneratePom=false


  The below is an example for Z3 deployment:
    files= additional files (seperated by a comma and NO spaces. If you use this you need to specify types and classifiers)
    classifiers=classifiers for the files (in the order they appear in files seperated by a comma with no spaces)
    types= types of files (in the order they appear in files seperated by a comma with no spaces)


mvn deploy:deploy-file -Durl=http://localhost:8081/repository/maven-releases/ -DrepositoryId=nexusrepo  -Dfile=lib/java/runtime-z3/com.microsoft.z3.jar -Dfiles=lib/java/runtime-z3/libz3java.so,lib/java/runtime-z3/libz3.so -Dtypes=so,so -DgroupId=org.sosy-lab -Dclassifiers=libz3java,libz3 -DartifactId=javasmt-solver-z3 -Dversion=4.8.9-sosy0 -Dpackaging=jar -DpomFile=solvers_maven_conf/maven_z3_pom.xml -DgeneratePom=false

For deployment to Maven Central change the first part of the command to:
      mvn org.apache.maven.plugins:maven-gpg-plugin:1.3:sign-and-deploy-file
  Change url and repository to:
       -Durl=${ossrh-staging-repository-url} -DrepositoryId=${ossrh-server-id}
  Add to the end: 
    -Pgpg
    
    Or simply take a look at the file /build/build-maven-publish.xml
  
    If you want to use those dependencys you need to rename them and copy them to a location that is checked
    by the sosy commons library!
    To perform this we need a little bit of user interaction.

  
14. Use Mathsat5/Z3 with Maven:
    Open the pom.xml you want to use with JavaSMT and Mathsat5/Z3.
    (This assumes that you use the project provided. Meaning that there is the main-file 
    my-app/src/main/java/com/mycompany/app/SolverOverviewTable.java and the test-file
    my-app/src/test/java/com/mycompany/app/SudokuTest.java  
    You can change the folder structure as described above. Lets say you want
    javasmt-maven-example/src/main/java/org/sosy-lab/SolverOverviewTable.java then
    you just need to edit the following things: the folder structure itself, the groupId
    in the beginning of the pom.xml and the mainClass attribute of the maven-jar-plugin.
    Note: the name of the root dir in which the pom.xml resides is irrelevant for Maven.)
    Add this to the dependencys:
    (I assume you want to use both. Mathsat5 is 1 dependency with 1 solver binary.
    Z3 is 3 dependencies with 1 JAR and 2 binaries. If you don't want Z3 you need to remove
    all 3 here and 2 items from the copy 

```xml
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>java-smt</artifactId>
      <version>3.7.0</version>
    </dependency>
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-mathsat5</artifactId>
      <version>5.6.5</version>
      <type>so</type>
    </dependency>
    <!-- Z3 has 3 dependencies (from the same repo) -->
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-z3</artifactId>
      <version>1.2</version>
    </dependency>
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-z3</artifactId>
      <version>1.2</version>
      <type>so</type>
      <classifier>libz3</classifier>
    </dependency>
    <dependency>
      <groupId>org.sosy-lab</groupId>
      <artifactId>javasmt-solver-z3</artifactId>
      <version>1.2</version>
      <type>so</type>
      <classifier>libz3java</classifier>
    </dependency>
    
    <!-- Junit is not needed by JavaSMT! Its just here to complete the explanation. -->
    <!-- For testing we take Junit 4. As we only need it for the tests we restrict the scope. -->
    <dependency>
      <groupId>junit</groupId>
      <artifactId>junit</artifactId>
      <version>4.11</version>
      <scope>test</scope>
    </dependency>
```
    
    Modify the plugins maven-surefire-plugin and maven-jar-plugin in pluginManagement:

```xml
       <plugin>
          <!-- This shit starts its own JVM that ignores system properties set by the user, because why would those ever be important?! -->
          <artifactId>maven-surefire-plugin</artifactId>
          <version>2.22.1</version>
          <!-- For solvers with native binaries (i.e. Z3, Mathsat5) you need to add a classpath or
               java.library.path to test properly. This has to have
               the location of the sosy-lab.commons.jar + the solver binaries. 
               See maven-dependency-plugin below for more information.   -->
          <configuration>
            <argLine>-Djava.library.path=${project.build.directory}/dependency</argLine>
          </configuration>  
        </plugin>
        <plugin>
          <artifactId>maven-jar-plugin</artifactId>
          <version>3.0.2</version>
          <configuration>
          <archive>
            <manifest>
              <!-- For solvers with native binaries (i.e. Z3, Mathsat5) you need to add a classpath to
                   the location of the sosy-lab.commons.jar + the solver binaries. 
                   See maven-dependency-plugin below for more information.   -->
              <addClasspath>true</addClasspath>
              <classpathPrefix>${project.build.directory}/dependency</classpathPrefix>
              <mainClass>com.mycompany.app.SolverOverviewTable</mainClass>
            </manifest>
          </archive>
        </configuration>
        </plugin>
```

    Additionally add the following to <plugins> (NOT <pluginManagement>). 
    (If you really wanted it in there you need to execute it in <plugins> later on!)
    <plugins> is just like <pluginManagement> in <build>.

```xml
      <plugins>
        <plugin>
          <!-- This plugin allows us to copy/delete stuff around. -->
          <groupId>org.apache.maven.plugins</groupId>
          <artifactId>maven-dependency-plugin</artifactId>
          <version>3.1.1</version>
          <executions>
            <execution>
              <!-- We want to init the goal properties very early (phase initialize) executed.
                   This allows us to find the folder to every dependency on every system like this: 
                   ${groupId:artifactId:type:[classifier]} 
                   More infos on this: https://maven.apache.org/plugins/maven-dependency-plugin/properties-mojo.html
 
                   The goal copy is used to change the name of the solver binaries (i.e. Z3)   -->
              <id>copy</id>
              <phase>initialize</phase>
              <goals>
                <goal>properties</goal>
                <goal>copy</goal>
              </goals>
            </execution>
            <execution>
              <!-- This copys all dependencies to ${project.build.directory}/dependency -->
              <!-- We do this because the sosy-lab.commons dependency (in JavaSMT) needs the 
                   nativ solver binaries(i.e. Z3) at specifc locations (see below) and with specifc names.
                   So we just copy all dependencies and set the classpath to this location.
                   You may of course change this if you know how to.
                   Locations for commons: in its own folder (by far the easiest)
                   or in the "native library path" as returned by getNativeLibraryPath() in java, which is the
                   directory ../native/<arch>-<os>/ relative to the JAR file of sosy-lab.commons, with
                   <arch>-<os> being one of the following values depending on your system:
                   x86_64-linux
                   x86-linux
                   x86-windows
                   x86_64-windows
                   x86-macosx
                   x86_64-macosx       -->
              <id>copy-dependencies</id>
              <phase>validate</phase>
              <goals>
                <goal>copy-dependencies</goal>
              </goals>
            </execution>
          </executions>
          <configuration>
            <artifactItems>
              <!-- Here we specify what we want to copy.
                   In our case we copy the solver dependencies (binaries) to change their names.
                   groupId/artifactId/version/type/classifier have to match the dependency!
                   We copy them to ${project.build.directory}/dependency as this is the location
                   that copy-dependencies uses by default. destFileName specifies the final name.
                   You may only need some of the artifacts below, depending on what solver(s) you want.
                   Important: you NEED to set the classpath to ${project.build.directory}/dependency or
                   wherever you have your sosy-lab.commons + solver binaries!   -->
              <artifactItem>
                <groupId>org.sosy-lab</groupId>
                <artifactId>javasmt-solver-mathsat5</artifactId>
                <version>5.6.5</version>
                <type>so</type>
                <!-- We put all dependencies in ${project.build.directory}/dependency so we put mathsat there as well -->
                <outputDirectory>${project.build.directory}/dependency</outputDirectory>
                <destFileName>libmathsat5j.so</destFileName>
              </artifactItem>
              <!-- If you want Z3, you need to copy 2 artifacts: libz3java.so, libz3.so -->
              <artifactItem>
                <groupId>org.sosy-lab</groupId>
                <artifactId>javasmt-solver-z3</artifactId>
                <version>1.2</version>
                <type>so</type>
                <classifier>libz3java</classifier>
                <!-- We put all dependencies in ${project.build.directory}/dependency so we put z3 there as well -->
                <outputDirectory>${project.build.directory}/dependency</outputDirectory>
                <destFileName>libz3java.so</destFileName>
              </artifactItem>
              <artifactItem>
                <groupId>org.sosy-lab</groupId>
                <artifactId>javasmt-solver-z3</artifactId>
                <version>1.2</version>
                <type>so</type>
                <classifier>libz3</classifier>
                <!-- We put all dependencies in ${project.build.directory}/dependency so we put z3 there as well -->
                <outputDirectory>${project.build.directory}/dependency</outputDirectory>
                <destFileName>libz3.so</destFileName>
              </artifactItem>
            </artifactItems>
          </configuration>
      </plugin>
```
  
    Due to the way org.sosy-lab.commons loads the native solver binaries it is currently not possible to build a single JAR 
    that runs with Mathsat5/Z3 without any external dependencies.
    It is however possible to build a WAR file, see web tutorial below.

15. Optional/Debug: You may need something to print our stuff like properties in Maven to debug your pom.xml.
                 The following might help with that:

```xml
  <plugin>
    <groupId>org.apache.maven.plugins</groupId>
    <artifactId>maven-antrun-plugin</artifactId>
    <version>1.7</version>
    <executions>
      <execution>
        <phase>compile</phase>
         <goals>
           <goal>run</goal>
         </goals>
         <configuration>
           <tasks>
             <!-- Some examples: -->
             <echo>******** Displaying value of a property ********</echo>
             <echo>${java.library.path}</echo>
             <echo>${org.sosy-lab:common:jar}</echo>
           </tasks>
         </configuration>
       </execution>
     </executions>
   </plugin>
```

16. Web-Tutorial explaining how to create a Tomcat-Server:

    -Download Tomcat (i used the Tomcat 9 tarball): https://tomcat.apache.org/download-90.cgi
    
    -Extract at a location that you want to use for your server and set permissions.
    
    -We need to configure the admin login and the java location for the server first.
     In the extracted server folder go to the conf folder and open tomcat-users.xml
     Insert the following inside the <tomcat-users> thingy:

```xml
<role rolename="manager-gui"/>
<role rolename="manager-status"/>
<user username="manager" roles="manager-gui,manager-status" password="manager"/>
```
       
     With this you can later deploy/delete war files to and from the server.
     You can of course set the username/password however you like.
     It is possible that the server later refuses those login details, i too had that problem, 
     but then it went away and i don't know why. If you have this problem and find a solution please
     contact me (Daniel Baier)!
     
     To configure java you need to know where your default java is located. (It should be Java 8 +)
     Search for setenv.sh (on linux) in the bin folder of Tomcat. If its not there, create one.
     In there write:
     
     JRE_HOME=/path/to/your/java
     CATALINA_PID="$CATALINA_BASE/tomcat.pid"
     
     Technically you need to set CATALINA_HOME in the setenv too. However it should be set by default.
     (CATALINA_HOME default is your Tomcat folder)
     
     More information in the RUNNING.txt in the main folder of Tomcat.
     
    -You can now start your Tomcat 9 server with the startup.sh in the bin folder.
     You can stop it with the shutdown.sh in the same folder.
     You can access the server GUI via a Web-Browser and the IP: http://localhost:8080
     You can change/access/upload directly to the server via the "Manager App" in the top right corner.
     You need your login credentials specified above for that.
     In there you can upload via "Deploy" (War file to deploy).
     After deploying simply click the WAR in the Applications tab.


17. Web-Tutorial explaining how to create a Dynamic Web Project (w Eclipse):
    (Simple example with 1 button that does something trivial)

    -Create a new Dynamic Web Project in Eclipse via new -> other -> Web
     (If you can't you are missing an extension for web projects. 
      Most likely you won't be able to install a Server in Eclipse either. 
      So download it from the marketplace.)
    
    -Choose a name
     Choose the runtime you downloaded (Tomcat 9 most likely)
     Module Version 4.0
     Default Configuration for your runtime
     EAR Membership simply EAR
     Click next twice and set the box to create a web.xml descriptor
     
    -Open your project in the project explorer, open Java Ressources and create a package and a crate a new Servlet in there
     When creating a Servlet you need the "doPost" and "doGet" methods so just let them create automatically
     In this class (Servlet) you can now add your code to the code of the doGet method i.e.:
       Printwriter out = response.getWriter(); // We need this to print something. You need to import the io package!
       out.println("Hallo Welt!");
       
     With this every time the servlet is used it will print "Hallo Welt!" on the screen.
     
    -Next we need a JSP Page to provide a frontend for the user:
     Rightclick WebContent in the project explorer -> new -> JSP File
     name it "index.jsp", choose the default options and finish.
     (We name it index because that one will be used as it is a standard, you may name if however you like)
     In this JSP add the following in the <body>:
     
```xml
       <hl>Welcome</hl>
       <hr/>
       <form action="MyServlet">
         <input type="submit" value="Send" />
       </form>
```
       
     This creates a button (type=submit) that has the text "Send" on it.
     Now go to  WEB-INF/web.xml in your project.
     (insert the name of your JSP here if you don't want to name it index)
     Here you should be able to see a mapping to your Servlet.
     If not, add it yourself (this will assume your servlet is named MyServlet in a package named org.sosy-lab):
     
```xml
       <servlet>
         <description></description>
         <display-name>MyServlet</display-name>
         <servlet-name>MyServlet</servlet-name>
         <servlet-class>org.sosy-lab.MyServlet</servlet-class>
       </servlet>
       <servlet-mapping>
         <servlet-name>MyServlet</servlet-name>
         <url-pattern>/MyServlet</url-pattern>
       </servlet-mapping>
```

    This mapping is not needed in an basic example (or at all).
    In servlet the description and display-name is optional and does what it says. (You can simply delete those 2 if you want)
    In servlet the servlet-class specifies the file you want to map to the servlet-name.
    In servlet-mapping you can map this servlet-name to one or more urls.
    You may access those urls later with the IP:port/MyServlet etc. 
    (With IP:port being the IP/port you use for your server. 
    By default you get the IP:port/MyServlet mapping anyway)
    
    If you want to test this you can rightclick the project and execute it with "run with".
    You will have to have installed the web dev tools/server tools however
    and you have to choose/create a Tomcat server. Simply use the Tomcat server files you already downloaded.

18. Web-Tutorial explaining how to create a WAR file with Maven:

    Now create a new folder (this will be the main folder of your Maven project).
    Name it however you like (i.e. MyProject) and enter it. In there create a new folder named "src" and your pom.xml.
    Enter the src folder, create a folder main here an copy your web project into this folder so that it looks like this:
    You may have to rename some folders to match the pattern below (src/main/java and src/main/webapp is a must!)
    
    MyProject
      |--pom.xml
      |--src
          |--main
              |--java
              |   |--org
              |   |   |--sosy_lab
              |   |   |     |--MyServlet.java
              |--webapp
                   |--META-INF
                   |--WEB-INF
                   |--index.jsp
    
    
    More information here:
    https://maven.apache.org/guides/introduction/introduction-to-the-standard-directory-layout.html
    
19. pom.xml for a web-project / how to create a WAR file with Maven:

    We will package the dependencys, including the native solver files, into the WAR.
    The pom looks nearly the same as the normal JAR pom, the differences are:
    
    ```xml
    <!-- We want to package it as a WAR file -->
    <packaging>war</packaging>
    
    <!-- in plugins add this: -->
    <!-- This plugin packages our WAR. 
         We include the native files that are not java based in the include and specify where to find them.
         targetPath specifies the location in the WAR. This needs to be set up so that the commons lib finds it. -->
    <plugin>
        <groupId>org.apache.maven.plugins</groupId>
        <artifactId>maven-war-plugin</artifactId>
        <version>3.3.1</version>
        <configuration>
          <archive>
            <manifest>
              <addClasspath>true</addClasspath>
            </manifest>
          </archive>
                <webResources>
                    <resource>
                        <directory>target/dependency</directory>
                        <includes>
                            <include>libmathsat5j.so</include>
                            <include>libz3.so</include>
                            <include>libz3java.so</include>
                        </includes>
                        <targetPath>WEB-INF/lib</targetPath>
                    </resource>
                </webResources>
        </configuration>
      </plugin>
    ```
    
    The rest needs to be set up exactly like before (except the jar plugin and the tests if you don't have any)
    Now mvn package should create a WAR file in the target directory for you that you may test on your own Tomcat server.
