#!/bin/sh

runscanner() {
  olddir=`pwd`;
  cd `dirname $1`
  ../../../dcc --target scan --compat `basename $1`
  cd $olddir;
}

fail=0

for file in `dirname $0`/input/*; do
  output=`mktemp /tmp/XXXXX`
  runscanner $file > $output;
  if ! diff -u $output `dirname $0`/output/`basename $file`.out; then
    echo "File $file scanner output mismatch.";
    fail=1
    #exit $fail
  fi
  rm $output;
done

if [ "$fail" -eq 0 ]
then
    echo "\nPassed"
else
    echo "\nFailed"
fi

exit $fail;
