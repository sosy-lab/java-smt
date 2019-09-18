#!/bin/sh

satcompetition=no

log=no
debug=no
stats=undefined
trace=undefined
static=yes
shared=no
thirtytwobit=no
static=no
rcode=no

while [ $# -gt 0 ]
do
  case $1 in
    -g|--debug) debug=yes;;
    -O|--optimize) debug=no;;
    -l|--log) log=yes;;
    -s|--stats) stats=yes;;
    -t|--trace) trace=yes;;
    --no-stats) stats=no;;
    --no-trace) trace=no;;
    --no-rcode) rcode=no;;
    --rcode) rcode=yes;;
    -32|--32|-m32) thirtytwobit=yes;;
    -static|--static) static=yes;;
    -shared|--shared) shared=yes;;
    *) cat <<EOF
usage: ./configure.sh [<option> ...]

where <option> is one of the following:

  -g|--debug           include debugging code and symbols
  -O|--optimize        optimized compilation (default)
  -l|--log             add low level logging code (default with '-g')
  -s|--stats           more expensive statististcs (default with '-g')
  -t|--trace           trace generation (more memory, default with '-g')
  --no-stats           disable expensive stats
  --no-trace           enable trace generation
  -32|--32|-m32        compile for 32 bit machine even on 64 bit host
  -rcode|--no-rcode    enable/disable compatibility for used in R exension
  -static|--static     produce static binary
  -shared|--shared     produce shared library
EOF
exit 1
;;
  esac
shift
done

echo "version ... `cat VERSION`"

if [ $satcompetition = yes ]
then
  debug=no
  stats=no
  trace=no
  thirtytwobit=yes
  static=yes
  shared=no
fi

echo "debug ... $debug"
echo "log ... $log"

[ $stats = undefined ] && stats=$debug
echo "stats ... $stats"

[ $trace = undefined ] && trace=$debug
echo "trace ... $trace"

echo "static ... $static"

echo "shared ... $shared"

[ "X$CC" = X ] && CC=gcc

if [ X"$CFLAGS" = X ]
then
  case X"$CC" in
    *wine*|*mingw*) CFLAGS="-DNGETRUSAGE -DNALLSIGNALS";;
    *);;
  esac
  [ $log = yes ] && CFLAGS="$CFLAGS -DLOGGING"
  [ $stats = yes ] && CFLAGS="$CFLAGS -DSTATS"
  [ $trace = yes ] && CFLAGS="$CFLAGS -DTRACE"
  [ $static = yes ] && CFLAGS="$CFLAGS -static"
  [ $rcode = yes ] && CFLAGS="$CFLAGS -DRCODE"
  case X"$CC" in
    X*gcc*)
      CFLAGS="$CFLAGS -Wall -Wextra"
      [ $thirtytwobit = yes ] && CFLAGS="$CFLAGS -m32"
      if [ $debug = yes ]
      then
        CFLAGS="$CFLAGS -g3 -ggdb"
      else
	CFLAGS="$CFLAGS -DNDEBUG -O3"
      fi
      ;;
    *)
      if [ $debug = yes ]
      then
        CFLAGS="$CFLAGS -g"
      else
        CFLAGS="$CFLAGS -O"
      fi
      ;;
  esac
fi

if [ $rcode = yes ]
then
  for rdoth in /usr/share/R/include/R.h $RINC undefined
  do
    [ -f $rdoth ] && break
  done
  if [ $rdoth = undefined ]
  then
    echo "R.h ... not found (add '-I' manually or 'RHEADER=...  ./configure')"
  else
    RINC="-I`dirname $rdoth`"
    CFLAGS="$CFLAGS $RINC"
    echo "R.h ... added '$RINC' include directive"
  fi
  TARGETS="libpicosat.a"
else
  TARGETS="picosat picomcs picomus picogcnf libpicosat.a"
fi

if [ $shared = yes ]
then
  TARGETS="$TARGETS libpicosat.so"
  CFLAGS="$CFLAGS -fPIC"
fi
echo "targets ... $TARGETS"

echo "cc ... $CC"

echo "cflags ... $CFLAGS"

printf "makefile ..."
rm -f makefile
sed \
  -e "s,@CC@,$CC," \
  -e "s,@CFLAGS@,$CFLAGS," \
  -e "s,@TARGETS@,$TARGETS," \
makefile.in > makefile
echo " done"
