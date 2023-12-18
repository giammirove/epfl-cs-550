package lisa.settheory

import lisa.fol.FOL.{_, given}
import lisa.utils.K
import lisa.utils.K.makeAxiom
import lisa.mathematics.settheory.AxiomOfChoice.pairwiseDisjoint
import lisa.mathematics.settheory.AxiomOfChoice.identityFunction
import lisa.mathematics.settheory.SetTheory.setIntersection
import lisa.mathematics.settheory.SetTheory.singleton
import lisa.mathematics.settheory.SetTheory.Pi
import lisa.mathematics.settheory.orderings.Ordinals.ordinal
import lisa.mathematics.settheory.orderings.WellOrders.wellOrder
import lisa.mathematics.settheory.orderings.PartialOrders.totalOrder
import lisa.mathematics.settheory.AxiomOfChoice.equiPollent

/**
 * Axioms for the Zermelo-Fraenkel theory (ZFC)
 */
private[settheory] trait SetTheoryZFCAxioms extends SetTheoryZFAxioms {
  private val a = variable
  private val b = variable
  private val x = variable
  private val y = variable
  private val f = variable
  private val A = variable
  private val B = variable
  private val C = variable
  private val R = variable

  /*
   *
   * Title:      ZF/AC/AC_Equiv.thy
   *  Author:     Krzysztof Grabczewski
   *
   * Axioms AC1 -- AC19 come from "Equivalents of the Axiom of Choice, II"
   * by H. Rubin and J.E. Rubin, 1985.
   *
   * Axiom AC0 comes from "Axiomatic Set Theory" by P. Suppes, 1972.
   *
   * Some Isabelle proofs of equivalences of these axioms are formalizations of
   * proofs presented by the Rubins.  The others are based on the Rubins' proofs,
   * but slightly changed.
   *
   */

  // "AC1 ≡ ∀A. 0∉A ⟶ (∃f. f ∈ (∏X ∈ A. X))"
  final val ac1: this.AXIOM = Axiom(
    "ac1",
    forall(A, !in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A))))))
  )

  // "AC2 ≡ ∀A. 0∉A ∧ pairwise_disjoint(A)
  //                  ⟶ (∃C. ∀B ∈ A. ∃y. B ∩ C = {y})"
  // [[https://isabelle.in.tum.de/dist/library/FOL/ZF-AC/AC_Equiv.html#AC2]]
  final val ac2: this.AXIOM = Axiom(
    "ac2",
    forall(
      A,
      !in(emptySet, A) /\ pairwiseDisjoint(A) ==>
        exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
    )
  )

  final val wo1: this.AXIOM = Axiom(
    "wo1",
    // forall(A, exists(R, wellOrder2(A, R)))
    forall(A, exists(R, in(R, A) /\ wellOrder(R)))
  )
  final val wo2: this.AXIOM = Axiom(
    "wo2",
    forall(A, exists(a, ordinal(a) /\ equiPollent(A, a)))
  )
  final val wo3: this.AXIOM = Axiom(
    "wo3",
    forall(A, exists(a, ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b))))
  )

  private val acAxioms: Set[(String, AXIOM)] = Set(
    ("ac1", ac2),
    ("ac2", ac2),
    ("wo1", wo1),
    ("wo2", wo2),
    ("wo3", wo3)
  )

  override def axioms: Set[(String, AXIOM)] = super.axioms ++ acAxioms

}
