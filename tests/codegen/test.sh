#!/bin/sh

runcompiler() {
    ../../dcc --target codegen -o $2 $1
}

fail=0

if ! gcc -v 2>&1 |grep -q '^Target: x86_64-linux-gnu'; then
  echo "Refusing to run cross-compilation on non-64-bit architechure."
  exit 0;
fi

mv `dirname $0`/input/10-bounds.dcf 10.dfc

for file in `dirname $0`/input/*.dcf; do
  asm=`tempfile --suffix=.s`
  msg=""
  if runcompiler $file $asm; then
    binary=`tempfile`
    if gcc -o $binary -L `dirname $0`/lib -l6035 $asm; then
      output=`tempfile`
      if $binary > $output; then
        diffout=`tempfile`
        if ! diff -u $output `dirname $0`/output/`basename $file`.out > $diffout; then
          msg="File $file output mismatch.";
        fi
      else
        msg="Program failed to run.";
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
  rm -f $diffout $output $binary $asm;
done

mv 10.dfc `dirname $0`/input/10-bounds.dcf

exit $fail;
