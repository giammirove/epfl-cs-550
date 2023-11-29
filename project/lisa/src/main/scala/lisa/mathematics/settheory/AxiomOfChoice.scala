package lisa.mathematics
package settheory

object AxiomOfChoice extends lisa.Main {
  // export everything in this package

  // pairwise_disjoint :: "i ⇒ o"  where
  //   "pairwise_disjoint(A) ≡ ∀A1 ∈ A. ∀A2 ∈ A. A1 ∩ A2 ≠ 0 ⟶ A1=A2"

  private val x = variable
  private val y = variable

  val pairwiseDisjoint = DEF(A) --> {
    forall(x, forall(y, in(x, A) /\ in(y, A)))
  }
}
