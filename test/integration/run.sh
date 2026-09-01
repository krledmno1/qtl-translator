#!/bin/bash

# Integration tests for the MFOTL -> QTL translation.
#
# Each case under cases/<name>/ holds a fixed MFOTL policy with a fixed pair of traces
# describing the same scenario for both monitors:
#   policy.mfotl               the original MFOTL policy
#   trace.sig, trace.log       signature and log for MonPoly/VeriMon
#   trace.csv                  the boundary-encoded DejaVu trace (one event per line,
#                              each database terminated by the nullary event 'e')
#   trace.timed.csv            (alternative) DejaVu trace whose last field is the
#                              timestamp, used for policies with metric intervals
#   expected                   space-separated time points at which the policy is
#                              satisfied (0-based database index)
#
# VeriMon monitors the original policy and reports the time points with satisfying
# valuations. The policy is translated to QTL (negated, existentially closed), DejaVu
# monitors it on the encoded trace, and its violations are mapped back to database
# indices by counting 'e' events. The test passes if both monitors report exactly the
# time points listed in 'expected'.
#
# Configuration (environment variables):
#   VERIMON_IMAGE   docker image providing the 'monpoly' binary
#                   (default: monpoly_master_mf_image:latest)
#   DEJAVU_IMAGE    docker image wrapping DejaVu; invoked as <image> <spec.qtl> <trace.csv>
#                   with the work directory mounted at /home/dejavu/work
#                   (default: monitoring-face-dejavu:latest)
#   VERIMON_FLAGS   extra monpoly flags (default: -verified)
#   TRANSLATOR_JAR  path to the translator jar
#   EPRED           name of the database-boundary event (default: e)
#   KEEP=1          keep per-case work directories
#
# Usage: ./run.sh [case ...]     (no arguments: run all cases)

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
VERIMON_IMAGE="${VERIMON_IMAGE:-monpoly_master_mf_image:latest}"
DEJAVU_IMAGE="${DEJAVU_IMAGE:-monitoring-face-dejavu:latest}"
VERIMON_FLAGS="${VERIMON_FLAGS:--verified}"
TRANSLATOR_JAR="${TRANSLATOR_JAR:-$HERE/../../target/spec-parser-1.0-SNAPSHOT.jar}"
EPRED="${EPRED:-e}"
KEEP="${KEEP:-0}"

WORKROOT="$HERE/work"
rm -rf "$WORKROOT"
mkdir -p "$WORKROOT"

if [ ! -f "$TRANSLATOR_JAR" ]; then
    echo "Translator jar not found: $TRANSLATOR_JAR (build with 'mvn package -Dmaven.test.skip=true')"
    exit 2
fi

if [ "$#" -gt 0 ]; then
    CASES="$@"
else
    CASES=$(ls "$HERE/cases")
fi

pass=0
fail=0
failed_cases=""

normalize() {
    # sorts numbers and joins them with single spaces; empty input -> empty string
    tr ' ' '\n' | grep -E '^[0-9]+$' | sort -n | uniq | tr '\n' ' ' | sed 's/ $//'
}

for name in $CASES; do
    case_dir="$HERE/cases/$name"
    if [ ! -d "$case_dir" ]; then
        echo "❌ $name: no such case"
        fail=$((fail+1)); failed_cases="$failed_cases $name"
        continue
    fi

    work="$WORKROOT/$name"
    mkdir -p "$work"
    cp "$case_dir"/* "$work/"

    if [ -f "$work/trace.timed.csv" ]; then
        csv_name="trace.timed.csv"
    else
        csv_name="trace.csv"
    fi

    # 1. Translate the policy.
    if ! java -jar "$TRANSLATOR_JAR" -n -e "$EPRED" "$work/policy.mfotl" > "$work/policy.qtl" 2> "$work/translate.err"; then
        echo "❌ $name: translation failed"
        sed 's/^/     /' "$work/policy.qtl" "$work/translate.err"
        fail=$((fail+1)); failed_cases="$failed_cases $name"
        continue
    fi

    # 2. VeriMon on the original policy and log.
    docker run --rm -v "$work":/work "$VERIMON_IMAGE" \
        monpoly -sig /work/trace.sig -formula /work/policy.mfotl -log /work/trace.log $VERIMON_FLAGS \
        > "$work/verimon.out" 2>&1
    verimon_status=$?
    verimon_tps=$(grep -Eo 'time point [0-9]+' "$work/verimon.out" | awk '{print $3}' | normalize)
    # MonPoly reports an unmonitorable formula on stdout and still exits with 0.
    if [ $verimon_status -ne 0 ] || grep -qi "not monitorable" "$work/verimon.out"; then
        echo "❌ $name: verimon failed (exit $verimon_status)"
        sed 's/^/     /' "$work/verimon.out" | head -5
        fail=$((fail+1)); failed_cases="$failed_cases $name"
        continue
    fi

    # 3. DejaVu on the translated policy and the encoded trace.
    docker run --rm -v "$work":/home/dejavu/work "$DEJAVU_IMAGE" policy.qtl "$csv_name" \
        > "$work/dejavu.out" 2>&1
    if grep -qE "Error during specification|Exception|error:" "$work/dejavu.out"; then
        echo "❌ $name: dejavu failed"
        sed 's/^/     /' "$work/dejavu.out" | head -5
        fail=$((fail+1)); failed_cases="$failed_cases $name"
        continue
    fi

    dejavu_events=$(grep -Eo 'violated on event number [0-9]+' "$work/dejavu.out" | grep -Eo '[0-9]+$' | tr '\n' ' ')

    # Map each violation event to its database index (number of preceding 'e' events);
    # a violation on a non-'e' line means the translation leaked a raw-position verdict.
    dejavu_tps=$(awk -F, -v events="$dejavu_events" -v epred="$EPRED" '
        BEGIN { n = split(events, E, " "); for (i = 1; i <= n; i++) want[E[i]] = 1; ecount = 0 }
        {
            if ($1 == epred) {
                if (want[NR]) print ecount
                ecount++
            } else if (want[NR]) {
                print "RAW" NR
            }
        }' "$work/$csv_name" | normalize)
    if grep -Eo 'violated on event number [0-9]+' "$work/dejavu.out" | grep -Eo '[0-9]+$' | \
       awk -v max="$(wc -l < "$work/$csv_name")" '$1 > max { bad = 1 } END { exit bad }'; then :; else
        echo "❌ $name: dejavu reported an event beyond the trace"
        fail=$((fail+1)); failed_cases="$failed_cases $name"
        continue
    fi
    raw_hits=$(awk -F, -v events="$dejavu_events" -v epred="$EPRED" '
        BEGIN { n = split(events, E, " "); for (i = 1; i <= n; i++) want[E[i]] = 1 }
        $1 != epred && want[NR] { print NR }' "$work/$csv_name")
    if [ -n "$raw_hits" ]; then
        echo "❌ $name: dejavu verdicts at non-$EPRED events (lines: $raw_hits)"
        fail=$((fail+1)); failed_cases="$failed_cases $name"
        continue
    fi

    expected_tps=$(cat "$work/expected" | normalize)

    if [ "$verimon_tps" = "$dejavu_tps" ] && [ "$verimon_tps" = "$expected_tps" ]; then
        echo "✅ $name: verimon and dejavu agree on time points [${expected_tps}]"
        pass=$((pass+1))
        [ "$KEEP" = "1" ] || rm -rf "$work"
    else
        echo "❌ $name: verdicts differ"
        echo "     expected: [${expected_tps}]"
        echo "     verimon:  [${verimon_tps}]"
        echo "     dejavu:   [${dejavu_tps}] (events: ${dejavu_events})"
        fail=$((fail+1)); failed_cases="$failed_cases $name"
    fi
done

echo
echo "$pass passed, $fail failed"
if [ $fail -ne 0 ]; then
    echo "Failed cases:$failed_cases (outputs kept in $WORKROOT)"
    exit 1
fi
[ "$KEEP" = "1" ] || rm -rf "$WORKROOT"
exit 0
