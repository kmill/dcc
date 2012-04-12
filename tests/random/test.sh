#!/bin/sh

runcompiler() {
    ../../dcc --target codegen --opt=all -o $2 $1
}

fail=0

if ! gcc -v 2>&1 |grep -q '^Target: x86_64-linux-gnu'; then
  echo "Refusing to run cross-compilation on non-64-bit architechure."
  exit 0;
fi

for file in `find ./$0 -iname='*.dcf'`; do
  asm=`tempfile --suffix=.s`
  msg=""
  if runcompiler $file $asm; then
    binary=`tempfile`
    if gcc -o $binary -L `dirname $0`/lib -l6035 $asm; then
      output=`tempfile`
      ret=`$binary > $output`
      if grep '//>' $file; then
        if [ "$ret" -eq 0 ]
        then
           desired=`tempfile`
           grep '//>' $file | sed -E 's@^//> ?@@' > $desired
           diffout=`tempfile`
           if ! diff -u $output $desired > $diffout; then
             msg="File $file output mismatch.";
           fi
        else
           msg="Program failed to run.";
        fi
      elif grep '//!' $file; then
        if [ "$ret" -eq 0 ]
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
  rm -f $diffout $output $binary $asm $desired;
done

exit $fail;
