package lisa.mathematics
package settheory

import lisa.mathematics.settheory.SetTheory.pair
import lisa.mathematics.settheory.SetTheory.setIntersection
import lisa.mathematics.settheory.SetTheory.functional
import lisa.mathematics.settheory.SetTheory.relationDomain
import lisa.mathematics.settheory.SetTheory.relationRange
import lisa.mathematics.settheory.SetTheory.singleton
import lisa.mathematics.settheory.SetTheory.setIntersection
import lisa.mathematics.settheory.SetTheory.restrictedFunction
import lisa.mathematics.settheory.SetTheory.Pi
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension

object AxiomOfChoice extends lisa.Main {
  // export everything in this package

  // pairwise_disjoint :: "i ⇒ o"  where
  //   "pairwise_disjoint(A) ≡ ∀A1 ∈ A. ∀A2 ∈ A. A1 ∩ A2 ≠ 0 ⟶ A1=A2"

  private val a = variable
  private val b = variable
  private val f = variable
  private val g = variable
  private val r = variable
  private val t = variable
  private val x = variable
  private val y = variable
  private val z = variable

  private val A = variable
  private val B = variable
  private val C = variable

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

  val imageUniqueness = Theorem(
    ∃!(g, ∀(t, in(t, g) <=> in(t, relationRange(r)) /\ exists(x, in(x, A) /\ in(pair(x, t), r))))
  ) {
    have(∃!(g, ∀(t, in(t, g) <=> in(t, relationRange(r)) /\ exists(x, in(x, A) /\ in(pair(x, t), r))))) by UniqueComprehension(
      relationRange(r),
      lambda((t, b), exists(x, in(x, A) /\ in(pair(x, t), r)))
    )
  }

  // // [[https://isabelle.in.tum.de/dist/library/FOL/ZF/ZF_Base.html#ZF_Base.Image|const]]
  val image = DEF(r, A) --> The(g, forall(t, in(t, g) <=> in(t, relationRange(r)) /\ exists(x, in(x, A) /\ in(pair(x, t), r))))(imageUniqueness)

  // // [[https://isabelle.in.tum.de/dist/library/FOL/ZF/ZF_Base.html#apply]]
  // // TODO: not sure about singleton
  val apply = DEF(f, a) --> union(image(f, a))

  // /*
  // (* ********************************************************************** *)
  // (* AC1 ⟹ AC2                                                            *)
  // (* ********************************************************************** *)
  //  */
  // // lemma AC1_AC2_aux1: "⟦f:(∏X ∈ A. X);  B ∈ A;  0∉A⟧ ⟹ {f`B} ⊆ B ∩ {f`C. C ∈ A}"
  // // by(fast elim !: apply_type)
  //
  val AC1_AC2_aux1 = Lemma({
    val f = Pi(A, A)
    in(B, A) /\ !in(emptySet, A) |- subset(apply(f, B), setIntersection(B, restrictedFunction(f, A)))
  }) {
    sorry
  }
}
