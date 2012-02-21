#!/bin/bash

cabal configure &> /dev/null
cabal build &> /dev/null

array=("-h")
i=0
for arg in $*
do
    if [[ $arg == \-* ]]
    then
        if [[ $arg == \-\-* ]]
	then
	    array[$i]=$arg
	else
	    array[$i]="-$arg"
	fi
    else
	array[$i]=$arg
    fi
    let i=$i+1
done

./dcc --compat ${array[0]} ${array[1]} ${array[2]} ${array[3]} ${array[4]} ${array[5]} ${array[6]} ${array[7]}
