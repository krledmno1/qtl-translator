package ch.ethz.infsec.policy

import scala.io.Source

object Main {
  def main(args: Array[String]): Unit = {
    if (args.length == 0) {
      printUsage()
      sys.exit(1)
    }

    val negated = args.contains("--neg") || args.contains("-n")
    val eventPredOpt = args.zipWithIndex.collectFirst {
      case ("--epred", i) if i + 1 < args.length => args(i + 1)
      case ("-e", i) if i + 1 < args.length => args(i + 1)
    }
    
    if (eventPredOpt.isEmpty) {
      println("Error: --epred <predicate-name> is required")
      printUsage()
      sys.exit(1)
    }
    
    val filePath = args.filter(arg => !arg.startsWith("-") && 
      !(eventPredOpt.isDefined && arg == eventPredOpt.get)).headOption

    filePath match {
      case Some(path) =>
        try {
          val policyText = Source.fromFile(path).mkString
          translatePolicy(policyText, negated, eventPredOpt.get)
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

  private def translatePolicy(policyText: String, negated: Boolean, eventPredName: String): Unit = {
    Policy.parse(policyText) match {
      case Right(formula) =>
        try {
          val eventPred = Pred[String](eventPredName)
          val qtl = formula.toQTLString(negated, eventPred)
          println(qtl)
        } catch {
          case e: UnsupportedOperationException =>
            println(s"Error: ${e.getMessage}")
            println("Note: Some MFOTL features are not supported in QTL translation")
            sys.exit(1)
          case e: Exception =>
            println(s"Error during translation: ${e.getMessage}")
            sys.exit(1)
        }
      case Left(error) =>
        println(s"Parse error: $error")
        sys.exit(1)
    }
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
        |
        |Arguments:
        |  policy-file            Path to the MFOTL policy file to translate
        |
        |Examples:
        |  java -jar spec-parser.jar --epred E policy.mfotl
        |  java -jar spec-parser.jar -e E --neg policy.mfotl
        |  java -jar spec-parser.jar -e E -n policy.mfotl
        |""".stripMargin)
  }
}
