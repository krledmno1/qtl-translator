# Integration tests: VeriMon vs. DejaVu

Each case in `cases/<name>/` fixes one scenario twice — once for each monitor — and
checks that the two monitors report exactly the same time points:

| file              | role                                                                  |
|-------------------|-----------------------------------------------------------------------|
| `policy.mfotl`    | the original MFOTL policy (input to VeriMon, input to the translator) |
| `trace.sig`       | MonPoly signature                                                     |
| `trace.log`       | MonPoly log: one database per `@ts` entry                             |
| `trace.csv`       | the same trace in the DejaVu boundary encoding (see below)            |
| `trace.timed.csv` | alternative to `trace.csv` for policies with metric intervals         |
| `expected`        | space-separated 0-based time points at which the policy is satisfied  |

The runner translates `policy.mfotl` to QTL (`-n -e e`, i.e. negated and existentially
closed), runs VeriMon on the original policy/log and DejaVu on the translated
policy/CSV, and maps DejaVu's violation events back to time points by counting `e`
events. A case passes when VeriMon's satisfaction time points, DejaVu's reported time
points, and `expected` coincide. Any DejaVu verdict on a non-`e` event fails the case:
translated formulas must never hold at raw positions.

## Trace encoding

A MonPoly database `@ts P(1) Q(2)` becomes one CSV line per event, followed by the
fresh nullary boundary event `e`:

```
P,1
Q,2
e
```

An empty database contributes only the `e` line. For metric policies the trace must be
named `*.timed.csv` and every line carries the database's timestamp as its **last**
field (`P,1,ts`, and `e,ts` for the boundary) — that is the format in which this DejaVu
version reads time; on a plain `.csv` its clock never advances and interval bounds are
meaningless.

## Running

```bash
mvn package -Dmaven.test.skip=true          # build the translator (repo root)
./run.sh                                    # all cases
./run.sh prev letsince                      # selected cases
```

Docker images and other knobs are environment variables:

```bash
VERIMON_IMAGE=monpoly_master_mf_image:latest \
DEJAVU_IMAGE=monitoring-face-dejavu:latest \
VERIMON_FLAGS=-verified \
./run.sh
```

`VERIMON_IMAGE` must provide the `monpoly` binary (invoked as
`monpoly -sig ... -formula ... -log ... $VERIMON_FLAGS`, work directory mounted at
`/work`). `DEJAVU_IMAGE` must accept `<spec.qtl> <trace.csv>` relative to a work
directory mounted at `/home/dejavu/work`, and print DejaVu's
`violated on event number N` lines. Set `KEEP=1` to keep the per-case `work/`
directories with all monitor outputs.

## Cases

| case         | exercises                                                        |
|--------------|------------------------------------------------------------------|
| prev         | PREVIOUS refers to the previous database                         |
| prevempty    | PREVIOUS across an empty database                                |
| prevtrue     | PREVIOUS TRUE is false exactly at the first database             |
| prevint      | metric PREVIOUS on a timestamped trace                           |
| oncenot      | negation under ONCE stays relativized to boundaries              |
| negunder     | guarded negation inside a conjunction                            |
| eqguard      | equality leaves hold only at boundaries                          |
| eqflip       | `c = x` is flipped to `x = c` (DejaVu needs the variable first)  |
| eqconst      | `c = c'` is evaluated statically                                 |
| sinceuntimed | the reference SINCE example                                      |
| sincele      | SINCE with an upper-bounded interval on a timestamped trace      |
| sincegt      | SINCE with a lower-bounded interval on a timestamped trace       |
| letsince     | LET with a conjunctive body used under SINCE                     |
| capturelet   | LET expansion renames bound variables to avoid capture           |
| dupprev      | one predicate with two argument lists (two DejaVu macros)        |
| constonce    | constant predicate argument (inlined, no macro)                  |
| strconst     | string constant argument                                         |
| repvar       | repeated variable argument (inlined, no macro)                   |
| shadow       | free and bound occurrence of the same variable name              |
| example1     | `examples/test1.mfotl`: one predicate, permuted variables, under negation |
| example3     | `examples/test3.mfotl`: negation inside a SINCE left-hand side   |
| example5     | `examples/test5.mfotl`: metric PREVIOUS plus a negated SINCE     |
| example6     | `examples/test6.mfotl`: EXISTS under PREVIOUS, negated nullary conjunction |
| example7     | `examples/test7.mfotl`: PREVIOUS of SINCE and negated ONCE of PREVIOUS |
| example8     | `examples/test8.mfotl`: EXISTS of SINCE as a SINCE rhs, repeated variable in the lhs |
| example10    | `examples/test10.mfotl`: repeated variables in a SINCE lhs, negated conjunction |
