# QTL-traslator

This is a standalone Maven project for parsing MFOTL (Metric First-Order Temporal Logic) policy
specifications and translating them into QTL (Quantified Temporal Logic) formulas. It has been
partially extracted and extended from the [scalable-online-monitoring project](https://bitbucket.org/krle/scalable-online-monitor/). 


## Structure

### Source Files

**Scala Files:**
- `src/main/scala/ch/ethz/infsec/policy/Policy.scala` - Main policy parser using FastParse
- `src/main/scala/ch/ethz/infsec/policy/GenFormula.scala` - Generic formula definitions and types (inlined from monitoring-common)
- `src/main/scala/ch/ethz/infsec/policy/package.scala` - Package object with type aliases

**Java Files:**
- `src/main/java/ch/ethz/infsec/monitor/DataType.java` - Data type enumeration (inlined from monitoring-common)
- `src/main/java/ch/ethz/infsec/monitor/Signature.java` - Signature interface (inlined from monitoring-common)

### Dependencies

- **FastParse** (1.0.0) - Parser combinator library
- **Scala** (2.12.6) - Programming language
- **Test dependencies**: JUnit, ScalaTest, ScalaCheck

## Building

```bash
mvn clean compile
```

To create a JAR:
```bash
mvn package
```

## Usage

For example, after building the project, you can run the parser with:

```bash
java -jar target/spec-parser-1.0-SNAPSHOT.jar -e e examples/example1.mfotl
```

Where the last argument is the input MFOTL policy file. See `examples/README.md`
for a step-by-step walkthrough from a policy to the outputs of both monitors.

```bash
Usage: java -jar spec-parser.jar [options] --epred <name> <policy-file>

Required:
  -e, --epred <name>     Event predicate name for QTL transformation

Options:
  -n, --neg              Translate the negation of the policy

Arguments:
  policy-file            Path to the MFOTL policy file to translate
```




## Testing

Unit tests (parser and QTL translation, including the expected QTL output for the
supported operators and the rejection of unsupported ones):

```bash
mvn test
```

Integration tests compare VeriMon and DejaVu on fixed traces: VeriMon monitors the
original MFOTL policy, DejaVu monitors the translated QTL policy on the
boundary-encoded trace, and the reported time points must coincide. They require
Docker images for both monitors (see `test/integration/README.md`):

```bash
mvn package -Dmaven.test.skip=true
cd test/integration && ./run.sh
```

## License

GNU Lesser General Public License, Version 3
