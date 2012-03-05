#!/bin/sh

runparser() {
  ../../dcc --target inter $1
}

cd `dirname $0`

fail=0
temp="`mktemp /tmp/XXXXX`"

for file in ./illegal/*; do
  if runparser $file >$temp; then
    echo "[ ] Illegal file $file incorrectly parsed successfully.";
	cat $temp
    fail=1
  else
    echo "[+]" $file;
  fi
done

for file in ./legal/*; do
  if ! runparser $file >$temp; then
    echo "[ ] Legal file $file failed to parse.";
	cat $temp
    fail=1
  else
      echo "[+]" $file;
  fi
done

if [ "$fail" -eq 0 ]
then
    echo "\nPassed"
else
    echo "\nFailed"
fi

exit $fail;
