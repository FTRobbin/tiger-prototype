filename=$(basename $1)
filenameegg="$filename.egg"
filenamejson="$filename.json"
filenameegraph="$filename.in"
~/Egg/eggcc/target/debug/eggcc --run-mode egglog $1 > $filenameegg
~/Egg/egglog/target/release/egglog --to-json $filenameegg --max-functions=1000000000 --max-calls-per-function=1000000000
./json2egraph < $filenamejson > $filenameegraph
