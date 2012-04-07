if [ -z $1 ]; then
	echo "Invalid argument (./submit.sh [archivename])"
	exit 1
fi

if ./test.sh; then
	./package.sh $1
	cp $1.tar.gz /mit/6.035/group/le07/submit/
	echo "Submission Complete"
else
	echo "Error with tests. No submission sent."
fi

exit 0
