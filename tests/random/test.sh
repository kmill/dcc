#!/bin/sh

runcompiler() {
    ../../dcc --target codegen --opt=all -o $2 $1
}

fail=0

if ! gcc -v 2>&1 |grep -q '^Target: x86_64-linux-gnu'; then
  echo "Refusing to run cross-compilation on non-64-bit architechure."
  exit 0;
fi

base=`dirname $0`

for file in `find $base -iname '*.dcf'`; do
  diffout=0
  asm=`tempfile --suffix=.s`
  msg=""
  if runcompiler $file $asm; then
    binary=`tempfile`
    if gcc -o $binary -L `dirname $0`/lib -l6035 $asm; then
      output=`tempfile`
      ret=`$binary &> $output`
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
        if [ ! -z "$ret" ]; then
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
  rm -f $output $binary $asm
  if [ ! -z "$hasdiff" ]; then
    rm -f $diffout $desired;
  fi
done

exit $fail;
