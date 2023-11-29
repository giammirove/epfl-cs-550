package lisa.mathematics
package settheory

import lisa.mathematics.settheory.SetTheory.setIntersection

object AxiomOfChoice extends lisa.Main {
  // export everything in this package

  // pairwise_disjoint :: "i ⇒ o"  where
  //   "pairwise_disjoint(A) ≡ ∀A1 ∈ A. ∀A2 ∈ A. A1 ∩ A2 ≠ 0 ⟶ A1=A2"

  private val x = variable
  private val y = variable

  private val A = variable

  val pairwiseDisjoint = DEF(A) --> {
    forall(
      x,
      forall(
        y,
        in(x, A) /\ in(y, A) ==>
          ((!(setIntersection(x, y) === emptySet)) ==> (x === y))
      )
    )
  }

}
