#!/bin/sh

base=`dirname $0`

if uname -a | grep "Darwin" > /dev/null; then
    echo "(compiling for Mac OS X)"
    archstring="-arch x86_64"
    dccopt="--mac"
    lib="$base/maclib/lib6035.o"
    LD_LIBRARY_PATH=$base/maclib:$LD_LIBRARY_PATH
else
    archstring=""
    dccopt=""
    lib="-L$base/lib -l6035"
    if ! gcc -v 2>&1 |grep -q '^Target: x86_64-linux-gnu'; then
	echo "Refusing to run cross-compilation on non-64-bit architechure."
	exit 0;
    fi
fi

runcompiler() {
    ../../dcc $dccopt --target codegen --opt=all -o $2 $1
}

fail=0

for file in `find $base -iname '*.dcf'`; do
  diffout=""
  output=""
  asm=`tempfile --suffix=.s`
  msg=""
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
      if grep '//>' $file > /dev/null; then
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
      elif grep '//!' $file > /dev/null; then
        if [ -z "$ret" ]; then
           msg="Program did not fail to run.";
        fi
      else
        msg="Test case has no output directive."
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
  rm -f $output $input $binary $asm
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
