#!/bin/sh

runparser() {
  ../../dcc --target parse $1
}

cd `dirname $0`

fail=0

for file in ./illegal/*; do
  if runparser $file; then
    echo "[ ] Illegal file $file incorrectly parsed successfully.";
    fail=1
  else
    echo "[+]" $file;
    echo
  fi
done

for file in ./legal/*; do
  if ! runparser $file; then
    echo "[ ] Legal file $file failed to parse.";
    fail=1
  else
      echo "[+]" $file;
  fi
done

if test fail; then
    echo "\nPassed"
else
    echo "\nFailed"
fi

exit $fail;
