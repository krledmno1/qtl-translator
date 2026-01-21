package ch.ethz.infsec

package object policy {
  type Variable = VariableID[String]
  type Predicate = Pred[Variable]
  type Formula = GenFormula[Variable]
}
