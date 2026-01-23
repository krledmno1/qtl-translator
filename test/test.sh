#!/bin/bash

# find all the mfotl formulas
fmas=$(find -f "" .. 2>/dev/null | grep mfotl$)
for fma in $fmas; do

    echo "Processing $fma"

    #get file name without path
    filename=$(basename -- "$fma")
    SPEC="${filename%.mfotl}.qtl"
    
    # translate each formula and save the output
    echo "  Translating $fma..."
    java -jar ../target/spec-parser-1.0-SNAPSHOT.jar -n -e e "$fma" > $SPEC
    res=$?
    if [ $res -ne 0 ]; then
        echo "  ❌ Translation failed for $fma"
        echo "      $(cat $SPEC)"
        rm "$SPEC"
        continue
    fi

    echo "  Parsing $fma..."
    java -cp dejavu.jar dejavu.Verify $SPEC 2>&1 > parse_out.txt
    res=$?
    if [ $res -ne 0 ]; then
        echo "  ❌ Parsing failed for $fma"
        echo "      $(cat parse_out.txt)"
        rm parse_out.txt
        continue
    fi

    # echo "  Generating monitor for $fma..."
    # scalac -cp .:dejavu.jar TraceMonitor.scala > /dev/null 2>&1
    # res=$?
    # if [ $res -ne 0 ]; then
    #     echo "  Monitor compilation failed for $fma"
    #     continue
    # fi

    echo "  ✅ Test passed: $fma" 

    rm $SPEC
    rm parse_out.txt   

done

rm -f *.class
rm -f TraceMonitor.scala
rm -f ast.dot
