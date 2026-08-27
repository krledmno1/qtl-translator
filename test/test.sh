#!/bin/bash

test_formula() {
    local fma=$1
    local exit_on_error=${2:-false}

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
        if [ "$exit_on_error" = true ]; then
            exit 1
        fi
        return 1
    fi

    echo "  Parsing $fma..."
    java -cp dejavu.jar dejavu.Verify $SPEC 2>&1 > parse_out.txt
    res=$?
    if [ $res -ne 0 ]; then
        echo "  ❌ Parsing failed for $fma"
        echo "      $(cat parse_out.txt)"
        rm parse_out.txt
        if [ "$exit_on_error" = true ]; then
            exit 1
        fi
        return 1
    fi

    echo "  ✅ Test passed: $fma" 

    rm $SPEC
    rm parse_out.txt   
    return 0
}

fma=$1

if [ -z "$fma" ]; then
    
    # find all the mfotl formulas
    fmas=$(find -f "" .. 2>/dev/null | grep mfotl$)
    for fma in $fmas; do
        test_formula "$fma" false
    done

else
    test_formula "$fma" true

fi

rm -f *.class
rm -f TraceMonitor.scala
rm -f ast.dot
