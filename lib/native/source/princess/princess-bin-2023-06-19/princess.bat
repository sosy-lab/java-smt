@echo off

rem Base directory of the Princess installation
rem (might have to be replaced with absolute path)

set BASE=.


rem ----------------------------------- don't change anything below this line

rem Set Java classpath

set CLASSPATH=%CLASSPATH%;%BASE%\dist\princess-all.jar

java -Xss20000k -Xmx1500m -noverify ap.CmdlMain %1 %2 %3 %4 %5 %6 %7 %8 %9