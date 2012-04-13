outFolder="inputOutput"
rm -rf $outFolder
mkdir $outFolder
for i in `ls input/`; do
    sed "s/^/\/\/> /g" output/$i.out >> $outFolder/$i
    cat input/$i >> $outFolder/$i
done