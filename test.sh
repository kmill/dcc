#!/bin/sh

fail=0

cabal build

for i in `ls tests`; do 
	cd tests/$i
	if ! ./test.sh > /dev/null; then
		echo "Failed $i Tests";
		fail=1
	fi
	cd ../..
done

if [ "$fail" -eq 0 ]
then
    echo "\nPassed"
else
    echo "\nFailed"
fi

exit $fail;

