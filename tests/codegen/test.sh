#!/bin/bash

domidirc=0
opts="cse copyprop constprop nzp deadcode blockelim flat tailcall"

base=`dirname $0`

if uname -a | grep "Darwin" > /dev/null; then
    echo "(compiling for Mac OS X)"
    d=`pwd`
    cd $base/maclib
    make
    cd $d
    archstring="-arch x86_64"
    dccopt="--mac"
    lib="$base/maclib/lib6035.o"
    LD_LIBRARY_PATH=$base/maclib:$LD_LIBRARY_PATH
else
    d=`pwd`
    cd $base/lib
    make
    cd $d
    archstring=""
    dccopt=""
    lib="-L$base/lib -l6035 -l6035_2"
    if ! gcc -v 2>&1 |grep -q '^Target: x86_64-linux-gnu'; then
  echo "Refusing to run cross-compilation on non-64-bit architechure."
  exit 0;
    fi
fi

runcompiler() {
    $base/../../dcc $dccopt --target codegen $3 -o $2 $1
}

runcompilertoc() {
    $base/../../dcc $dccopt --target midirc $3 $1 > $2
}

isolate() {
  exec 3>/dev/stderr 2>/dev/null
  if $*; then
    exec 3>&2
    return 0
  else
    exec 3>&2
    return 1
  fi
}

fail=0

testfile() {
  file=$1
  echo $file
  optstring=$2
  diffout=""
  output=""
  asm="`tempfile`.s"
  msg=""
  cmsg=""
  retest="" # retry with all optimizations
  desired="blargle this shouldn't match anything"
  if runcompiler $file $asm $optstring; then
    binary=`tempfile`
    gcccmd="gcc $archstring -o $binary $asm $lib"
	  # echo "$file: $gcccmd"
    if $gcccmd; then
      input=`tempfile`
      grep '//<' $file | sed -E 's@^//< ?@@' > $input
      output=`tempfile`
     
      if isolate $binary < $input > $output 2>&1; then
        ret=""
      else
        ret="fail"
      fi
      if grep '//!' $file > /dev/null; then
        if [ -z "$ret" ]; then
           msg="Program did not fail to run.";
           retest="yes"
        fi
      else
        if [ -z "$ret" ]; then
           desired=`tempfile`
           grep '//>' $file | sed -E 's@^//> ?@@' > $desired
           diffout=`tempfile`
           if ! diff -u $output $desired > $diffout; then
             msg="File $file output mismatch.";
             retest="yes"
           fi
        else
           msg="Program failed to run.";
           retest="yes"
        fi
      fi
    else
      msg="Program failed to assemble.";
    fi
  else
    msg="Program failed to generate assembly.";
  fi
  if [ ! -z "$msg" ]; then
    fail=1
    echo $file
    if [ ! -z "$diffout" ]; then
      cat $diffout
    elif [ ! -z "$output" ]; then
      cat $output
    fi
    echo $msg "(with optimization level $optstring)"
  fi

  if [ "$domidirc" -ne 0 ]; then
    ccode=`tempfile`
    if runcompilertoc $file $ccode $optstring; then
      cbinary=`tempfile`
      gccerrs=`tempfile`
      gcccmd="gcc -x c -o $cbinary $ccode $lib"
      if $gcccmd 2>$gccerrs; then
        coutput=`tempfile`
        input=`tempfile`
        grep '//<' $file | sed -E 's@^//< ?@@' > $input
        
        if isolate $cbinary < $input > $coutput 2>&1; then
          ret=""
        else
          ret="fail"
        fi
        if grep '//!' $file > /dev/null; then
          if [ -z "$ret" ]; then
            cmsg="Program should have failed.";
          else
            cmsg=""
          fi
        else
          if [ -z "$ret" ]; then
            desired=`tempfile`
            grep '//>' $file | sed -E 's@^//> ?@@' > $desired
            diffout=`tempfile`
            if ! diff -u $coutput $desired > $diffout; then
              cmsg="File output mismatch.";
            else
              cmsg=""
            fi
          else
            cmsg="Program failed to run.";
          fi
        fi
      else
        cmsg="Couldn't run gcc. ($gcccmd)"
      fi
    else
      cmsg="Couldn't compile to C."
    fi
      
    if [ ! -z "$cmsg" ]; then
      echo "Compilation via C failed on $file:"
      if [ ! -z "$diffout" ]; then
        cat $diffout
      elif [ ! -z "$coutput" ]; then
        cat $coutput
      fi
      if [ ! -z "$gccerrs" ]; then
        cat $gccerrs | grep -v "warning:" | grep -v "note:" | (while read x; do echo "    $x"; done)
      fi
      echo "  $cmsg (with optimization level $optstring)"
    fi
  fi

  rm -f $output $input $binary $asm $coutput $cbinary $ccode
  if [ ! -z "$diffout" ]; then
    rm -f $diffout $desired;
  fi
}

for file in `find $base -iname '*.dcf'`; do
  testfile $file "--opt=all,-condelim,-parallelize -r"
  if [ ! -z "$retest" ]; then
    echo "test $file failed, trying with all optimization levels"
    for opt in $opts; do
      testfile $file "--opt=$opt"
    done
  fi
done

if [ "$fail" -ne "0" ]; then
  echo "*** A test failed ***"
else
  echo "(success)"
fi
exit $fail;
