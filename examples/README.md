# Examples

Three example policies, each provided with everything needed to run both monitors:

| example  | policy                                            | features                              |
|----------|---------------------------------------------------|---------------------------------------|
| example1 | `(P0(x3, x1)) SINCE P2(x3, x2, x1)`               | plain SINCE                           |
| example2 | `(P0(x2,x1,x3) AND (x3 = 30)) AND (NOT P1(x3,x1,x2))` | equality and negation             |
| example3 | `(A(x) AND B(x)) SINCE C(x)`                      | SINCE with a conjunctive left-hand side |

Per example there are four files:

- `exampleN.mfotl` — the MFOTL policy (input to MonPoly/VeriMon and to the translator),
- `exampleN.sig` / `exampleN.log` — signature and log for MonPoly/VeriMon,
- `exampleN.csv` — the same trace, encoded for DejaVu (see *Trace encoding* below).

The walkthrough below uses `example1`; the same commands work for the others by
changing the name. It assumes the translator jar has been built at the repository
root (`mvn package -Dmaven.test.skip=true`) and that Docker images for the two
monitors are available; the image names below are the ones used by the integration
tests (`test/integration/`) — any image providing the `monpoly` binary, and any
DejaVu wrapper invoked as `<image> <spec.qtl> <trace.csv>`, work the same way.

## Step 1: run VeriMon on the original policy

```bash
docker run --rm -v "$PWD":/work <verimon-docker-image> \
    monpoly -sig /work/example1.sig -formula /work/example1.mfotl -log /work/example1.log -verified
```

MonPoly reports, for every time point, the valuations of the free variables that
satisfy the policy (omit `-verified` to use MonPoly's unverified kernel instead of
VeriMon). For `example1` it prints:

```
@1 (time point 0): (1,2,3)
@2 (time point 1): (1,2,3)
```

i.e. the policy is satisfied at time points 0 and 1: `P2(1,2,3)` holds at time
point 0 and `P0(1,3)` extends the SINCE at time point 1, while at time point 2 the
chain is broken.

## Step 2: translate the policy to QTL

```bash
java -jar ../target/spec-parser-1.0-SNAPSHOT.jar -n -e e example1.mfotl > example1.qtl
```

`-e e` names the fresh boundary event (it must not occur in the policy or the
trace), and `-n` negates and existentially closes the formula, so that DejaVu's
*violations* are exactly the time points where the original policy is *satisfied*.
The result for `example1`:

```
prop fma: ! Exists x3. Exists x2. Exists x1. (((_P0(x3, x1) | ! e()) S  _P2(x3, x2, x1)) & e()) where _P0(x3, x1) := e() & @  (! e() S  P0(x3, x1)), _P2(x3, x2, x1) := e() & @  (! e() S  P2(x3, x2, x1))
```

## Step 3: run DejaVu on the translated policy

```bash
docker run --rm -v "$PWD":/home/dejavu/work <dejavu-docker-image> example1.qtl example1.csv
```

DejaVu evaluates the property at every event of the encoded trace and reports the
events where it is violated:

```
*** Property fma violated on event number 2:
*** Property fma violated on event number 4:
```

## Step 4: relate the two outputs

DejaVu's event numbers are 1-based line numbers of `example1.csv`. Every reported
event is an `e` line, and the number of *preceding* `e` lines is the 0-based time
point it corresponds to: event 2 is the first `e` (time point 0) and event 4 the
second (time point 1) — exactly VeriMon's time points 0 and 1 from Step 1. Because
of `-n`, DejaVu reports the time points where the policy is satisfied; unlike
MonPoly it does not print the satisfying valuations.

The expected outputs for the other two examples:

- `example2`: VeriMon `@1 (time point 0): (1,2,30)`; DejaVu `violated on event number 3`.
- `example3`: VeriMon time points 1, 2, 3 (valuations `(1) (2) (3)`, `(1) (2) (3)`,
  `(1) (2)`); DejaVu events 7, 15, 21.

## Trace encoding

`exampleN.csv` is the DejaVu encoding of `exampleN.log`: every database
`@ts P(1) Q(2)` becomes one CSV line per event followed by the fresh nullary
boundary event `e`,

```
P,1
Q,2
e
```

and an empty database (`@ts` alone) contributes only the `e` line. Policies with
metric intervals additionally need timestamps: the trace must then be named
`*.timed.csv` and every line carries the database's timestamp as its last field
(`P,1,ts` and `e,ts`) — none of the three examples here is metric; see
`test/integration/cases/sincele/` for a timed one.

## Automated comparison

`test/integration/run.sh` performs these steps for a whole suite of cases and
checks that VeriMon and DejaVu report exactly the same time points; see
`test/integration/README.md`.
