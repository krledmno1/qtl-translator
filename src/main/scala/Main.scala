package ch.ethz.infsec.policy

import scala.io.Source

object Main {
  def main(args: Array[String]): Unit = {
    if (args.length == 0 || args.contains("--help") || args.contains("-h")) {
      printUsage()
      sys.exit(if (args.length == 0) 1 else 0)
    }

    var negated = false
    var eventPredOpt: Option[String] = None
    var domPred = GenFormula.defaultDomPred
    var filePath: Option[String] = None

    var i = 0
    while (i < args.length) {
      def argument(name: String): String = {
        if (i + 1 >= args.length) {
          println(s"Error: $name requires an argument")
          printUsage()
          sys.exit(1)
        }
        i += 1
        args(i)
      }
      args(i) match {
        case "--neg" | "-n" => negated = true
        case "--epred" | "-e" => eventPredOpt = Some(argument(args(i)))
        case "--dom" | "-d" => domPred = argument(args(i))
        case other if other.startsWith("-") =>
          println(s"Error: unknown option $other")
          printUsage()
          sys.exit(1)
        case other if filePath.isEmpty => filePath = Some(other)
        case other =>
          println(s"Error: more than one policy file given ($other)")
          sys.exit(1)
      }
      i += 1
    }

    if (eventPredOpt.isEmpty) {
      println("Error: --epred <predicate-name> is required")
      printUsage()
      sys.exit(1)
    }

    filePath match {
      case Some(path) =>
        try {
          val policyText = Source.fromFile(path).mkString
          translatePolicy(policyText, negated, eventPredOpt.get, domPred)
        } catch {
          case e: java.io.FileNotFoundException =>
            println(s"Error: File not found: $path")
            sys.exit(1)
          case e: Exception =>
            println(s"Error reading file: ${e.getMessage}")
            sys.exit(1)
        }
      case None =>
        println("Error: No input file specified")
        printUsage()
        sys.exit(1)
    }
  }

  private def translatePolicy(policyText: String, negated: Boolean, eventPredName: String,
                              domPredName: String): Unit = {
    Policy.parse(policyText) match {
      case Right(formula) =>
        try {
          val eventPred = Pred[String](eventPredName)
          val domPred = Pred[String](domPredName)
          val (qtl, constants) = formula.toQTLString(negated, eventPred, domPred)
          println(qtl)
          writeDomFile(domPredName, constants)
        } catch {
          case e: UnsupportedOperationException =>
            println(s"Error: ${e.getMessage()}")
            println("Note: Some MFOTL features are also not supported in the QTL translation")
            sys.exit(1)
          case e: Exception =>
            println(s"Error during translation: ${e.getMessage()}")
            sys.exit(1)
        }
      case Left(error) =>
        println(s"Parse error: $error")
        sys.exit(1)
    }
  }

  /** Writes the constants that must be registered in the trace as a single MonPoly time point
    * without a timestamp, e.g. `_dom(1)(2)(5)`. The file is written only when the formula
    * compares a variable against a constant. */
  private def writeDomFile(domPredName: String, constants: Seq[Any]): Unit = {
    if (constants.isEmpty) return
    val path = domPredName + ".dom"
    val tuples = constants.map(c => "(" + Const[String](c).toQTL + ")").mkString
    val writer = new java.io.PrintWriter(path)
    try writer.println(domPredName + tuples) finally writer.close()
    Console.err.println(
      s"Wrote ${constants.length} constant registration event(s) to $path; " +
        s"replay the trace with the replayer's -init $path to add them to its first time point")
  }

  private def printUsage(): Unit = {
    println(
      """Usage: java -jar spec-parser.jar [options] --epred <name> <policy-file>
        |
        |Required:
        |  -e, --epred <name>     Event predicate name for QTL transformation
        |
        |Options:
        |  -n, --neg              Translate the negation of the policy
        |  -d, --dom <name>       Predicate that registers the policy's constants in the
        |                         trace (default: _dom). If the policy compares a variable
        |                         against a constant, the constants are written to
        |                         <name>.dom, to be added to the trace's first time point.
        |  -h, --help             Show this help message
        |
        |Arguments:
        |  policy-file            Path to the MFOTL policy file to translate
        |
        |Examples:
        |  java -jar spec-parser.jar --epred E policy.mfotl
        |  java -jar spec-parser.jar -e E --neg policy.mfotl
        |  java -jar spec-parser.jar -e E -n -d dom policy.mfotl
        |""".stripMargin)
  }
}
