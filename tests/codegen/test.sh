#!/bin/sh

optstring="--opt=all"

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
    $base/../../dcc $dccopt --target codegen $optstring -o $2 $1
}

runcompilertoc() {
    $base/../../dcc $dccopt --target midirc $optstring $1 > $2
}

fail=0

for file in `find $base -iname '*.dcf'`; do
  diffout=""
  output=""
  asm=`tempfile --suffix=.s`
  msg=""
  desired="blargle this shouldn't match anything"
  if runcompiler $file $asm; then
    binary=`tempfile`
    if gcc $archstring -o $binary $asm $lib; then
      input=`tempfile`
      grep '//<' $file | sed -E 's@^//< ?@@' > $input
      output=`tempfile`
     
      if $binary < $input > $output 2>&1; then
        ret=""
      else
        ret="fail"
      fi
      if grep '//!' $file > /dev/null; then
        if [ -z "$ret" ]; then
           msg="Program did not fail to run.";
        fi
      else
        if [ -z "$ret" ]; then
           desired=`tempfile`
           grep '//>' $file | sed -E 's@^//> ?@@' > $desired
           diffout=`tempfile`
           if ! diff -u $output $desired > $diffout; then
             msg="File $file output mismatch.";
           fi
        else
           msg="Program failed to run.";
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
    echo $msg
  fi

  ccode=`tempfile`
  if runcompilertoc $file $ccode; then
    cbinary=`tempfile`
    if gcc -x c -o $cbinary $ccode 2>/dev/null; then
      coutput=`tempfile`
      input=`tempfile`
      grep '//<' $file | sed -E 's@^//< ?@@' > $input
      
      if $cbinary < $input > $coutput 2>&1; then
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
      cmsg="Couldn't run gcc."
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
    echo "  $cmsg"
  fi

  rm -f $output $input $binary $asm $coutput $cbinary $ccode
  if [ ! -z "$diffout" ]; then
    rm -f $diffout $desired;
  fi
done

if [ "$fail" -ne "0" ]; then
    echo "*** A test failed ***"
else
    echo "(success)"
fi
exit $fail;
