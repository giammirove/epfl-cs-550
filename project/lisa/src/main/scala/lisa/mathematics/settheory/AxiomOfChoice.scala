package lisa.mathematics
package settheory

import lisa.prooflib.Substitution
import lisa.automation.Tableau

import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.settheory.SetTheoryTactics.*

import lisa.mathematics.fol.*
import lisa.mathematics.fol.Quantifiers.closedFormulaExistential
import lisa.mathematics.fol.Quantifiers.existentialConjunctionWithClosedFormula
import lisa.mathematics.fol.Quantifiers.equalityTransitivity

import lisa.mathematics.settheory.SetTheory.injective
import lisa.mathematics.settheory.SetTheory.surjective
import lisa.mathematics.settheory.SetTheory.bijective
import lisa.mathematics.settheory.SetTheory.pair
import lisa.mathematics.settheory.SetTheory.pairExtensionality
import lisa.mathematics.settheory.SetTheory.pairInCartesianProduct
import lisa.mathematics.settheory.SetTheory.setIntersection
import lisa.mathematics.settheory.SetTheory.functional
import lisa.mathematics.settheory.SetTheory.functionFrom
import lisa.mathematics.settheory.SetTheory.functionalOver
import lisa.mathematics.settheory.SetTheory.functionalOverApplication
import lisa.mathematics.settheory.SetTheory.relationDomain
import lisa.mathematics.settheory.SetTheory.relationRange
import lisa.mathematics.settheory.SetTheory.singleton
import lisa.mathematics.settheory.SetTheory.singletonHasNoExtraElements
import lisa.mathematics.settheory.SetTheory.singletonExtensionality
import lisa.mathematics.settheory.SetTheory.singletonNonEmpty
import lisa.mathematics.settheory.SetTheory.setIntersection
import lisa.mathematics.settheory.SetTheory.setIntersectionMembership
import lisa.mathematics.settheory.SetTheory.intersectionOfSubsets
import lisa.mathematics.settheory.SetTheory.restrictedFunction
import lisa.mathematics.settheory.SetTheory.restrictedFunctionPairMembership
import lisa.mathematics.settheory.SetTheory.setWithElementNonEmpty
import lisa.mathematics.settheory.SetTheory.Sigma
import lisa.mathematics.settheory.SetTheory.Pi
import lisa.mathematics.settheory.SetTheory.piUniqueness
import lisa.mathematics.settheory.SetTheory.app
import lisa.mathematics.settheory.SetTheory.pairInFunctionIsApp
import lisa.mathematics.settheory.SetTheory.pairInCartesianProduct
import lisa.mathematics.settheory.SetTheory.relation
import lisa.mathematics.settheory.SetTheory.relationBetween
import lisa.mathematics.settheory.SetTheory.cartesianProduct
import lisa.mathematics.settheory.SetTheory.setWithElementNonEmpty
import lisa.mathematics.settheory.SetTheory.subsetEqualitySymmetry
import lisa.mathematics.settheory.SetTheory.subsetReflexivity
import lisa.mathematics.settheory.SetTheory.firstInPair
import lisa.mathematics.settheory.SetTheory.firstInPairReduction
import lisa.mathematics.settheory.SetTheory.secondInPair
import lisa.mathematics.settheory.SetTheory.productWithEmptySetEmpty
import lisa.mathematics.settheory.SetTheory.setUnion
import lisa.mathematics.settheory.orderings.Ordinals.ordinal
import lisa.mathematics.settheory.orderings.WellOrders.wellOrder
import lisa.mathematics.settheory.orderings.PartialOrders.totalOrder

object AxiomOfChoice extends lisa.Main {
  // export everything in this package

  // pairwise_disjoint :: "i ⇒ o"  where
  //   "pairwise_disjoint(A) ≡ ∀A1 ∈ A. ∀A2 ∈ A. A1 ∩ A2 ≠ 0 ⟶ A1=A2"

  private val a = variable
  private val b = variable
  private val c = variable
  private val d = variable
  private val f = variable
  private val g = variable
  private val p = formulaVariable
  private val q = formulaVariable
  private val r = variable
  private val t = variable
  private val x = variable
  private val y = variable
  private val z = variable

  private val A = variable
  private val B = variable
  private val C = variable
  private val D = variable
  private val R = variable
  private val X = variable
  private val Z = variable

  private val phi = predicate[1]
  private val P = predicate[1]
  private val Q = predicate[1]

  val pairwiseDisjoint = DEF(A) --> { forall(x, forall(y, in(x, A) /\ in(y, A) ==> ((!(setIntersection(x, y) === emptySet)) ==> (x === y)))) }

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
  // TODO: not sure about singleton
  val apply = DEF(f, a) --> union(image(f, singleton(a)))

  val identityFunctionUniqueness = Theorem(
    ∃!(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(x, x)) /\ exists(y, in(y, x) /\ (t === pair(y, y)))))
  ) {
    have(∃!(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(x, x)) /\ exists(y, in(y, x) /\ (t === pair(y, y)))))) by UniqueComprehension(
      cartesianProduct(x, x),
      lambda((t, b), exists(y, in(y, x) /\ (t === pair(y, y))))
    )
  }
  // builds the identity function as set of pairs like pair(x,x)
  // TODO: not sure about existsOne
  val identityFunction = DEF(x) --> The(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(x, x)) /\ ∃(y, in(y, x) /\ (t === pair(y, y)))))(identityFunctionUniqueness)

  // Rovelli Gianmaria
  val pairInIdentityFunction = Lemma(in(pair(a, b), identityFunction(A)) |- (a === b)) {
    assume(in(pair(a, b), identityFunction(A)))

    have(forall(t, in(t, identityFunction(A)) <=> in(t, cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (t === pair(y, y))))) by InstantiateForall(identityFunction(A))(
      identityFunction.definition of (x -> A)
    )
    thenHave(in(pair(a, b), identityFunction(A)) <=> in(pair(a, b), cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (pair(a, b) === pair(y, y)))) by InstantiateForall(pair(a, b))
    val s1 = thenHave(exists(y, in(y, A) /\ (pair(a, b) === pair(y, y)))) by Tautology

    val s2 = have(in(y, A) /\ (pair(a, b) === pair(y, y)) |- (a === y) /\ (b === y)) by Tautology.from(pairExtensionality of (c -> y, d -> y))
    val s3 = thenHave(in(y, A) /\ (pair(a, b) === pair(y, y)) |- (a === y)) by Tautology
    val s4 = have(in(y, A) /\ (pair(a, b) === pair(y, y)) |- (b === y)) by Tautology.from(s2)
    val s5 = thenHave(in(y, A) /\ (pair(a, b) === pair(y, y)) |- (b === a)) by Substitution.ApplyRules(s3)
    thenHave(exists(y, in(y, A) /\ (pair(a, b) === pair(y, y))) |- (b === a)) by LeftExists
    have(b === a) by Tautology.from(lastStep, s1)
  }

  // Rovelli Gianmaria
  val firstInPairType = Lemma(
    in(x, cartesianProduct(A, B)) |- in(firstInPair(x), A)
  ) {
    assume(in(x, cartesianProduct(A, B)))
    have(
      forall(
        t,
        in(t, cartesianProduct(A, B))
          <=> ((in(t, powerSet(powerSet(setUnion(A, B))))) /\ (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, B)))))
      )
    ) by InstantiateForall(cartesianProduct(A, B))(cartesianProduct.definition of (x -> A, y -> B))
    thenHave(
      in(x, cartesianProduct(A, B))
        <=> ((in(x, powerSet(powerSet(setUnion(A, B))))) /\ (∃(a, ∃(b, (x === pair(a, b)) /\ in(a, A) /\ in(b, B)))))
    ) by InstantiateForall(x)
    have((in(x, powerSet(powerSet(setUnion(A, B))))) /\ (∃(a, ∃(b, (x === pair(a, b)) /\ in(a, A) /\ in(b, B))))) by Tautology.from(lastStep)
    val s1 = thenHave(∃(a, ∃(b, (x === pair(a, b)) /\ in(a, A) /\ in(b, B)))) by Tautology

    have((x === pair(a, b)) /\ in(a, A) /\ in(b, B) |- in(firstInPair(x), A)) subproof {
      val subs = assume(x === pair(a, b))
      assume(in(a, A))
      assume(in(b, B))
      have(firstInPair(pair(a, b)) === a) by Tautology.from(firstInPairReduction of (x -> a, y -> b))
      val ss1 = thenHave(firstInPair(x) === a) by Substitution.ApplyRules(subs)
      have(in(a, A)) by Hypothesis
      thenHave(in(firstInPair(x), A)) by Substitution.ApplyRules(ss1)
    }
    thenHave(exists(b, (x === pair(a, b)) /\ in(a, A) /\ in(b, B)) |- in(firstInPair(x), A)) by LeftExists
    thenHave(exists(a, exists(b, (x === pair(a, b)) /\ in(a, A) /\ in(b, B))) |- in(firstInPair(x), A)) by LeftExists

    have(in(firstInPair(x), A)) by Tautology.from(lastStep, s1)
  }

  // Rovelli Gianmaria
  val inclusionImpliesInclusionInIdentity = Lemma(in(x, A) <=> in(pair(x, x), identityFunction(A))) {
    have(forall(t, in(t, identityFunction(A)) <=> in(t, cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (t === pair(y, y))))) by InstantiateForall(identityFunction(A))(
      identityFunction.definition of (x -> A)
    )
    val idDef =
      thenHave(in(pair(x, x), identityFunction(A)) <=> in(pair(x, x), cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (pair(x, x) === pair(y, y)))) by InstantiateForall(pair(x, x))

    val fwd = have(in(x, A) ==> in(pair(x, x), identityFunction(A))) subproof {
      assume(in(x, A))
      val ss1 = have(in(pair(x, x), cartesianProduct(A, A))) by Tautology.from(pairInCartesianProduct of (x -> A, y -> A, a -> x, b -> x))
      have(in(x, A) /\ (pair(x, x) === pair(x, x))) by Tautology
      val ss2 = thenHave(exists(y, in(y, A) /\ (pair(x, x) === pair(y, y)))) by RightExists
      have(thesis) by Tautology.from(ss1, ss2, idDef)
    }

    val bwd = have(in(pair(x, x), identityFunction(A)) ==> in(x, A)) subproof {
      assume(in(pair(x, x), identityFunction(A)))

      val ss1 = have(firstInPair(pair(x, x)) === x) by Tautology.from(firstInPairReduction of (x -> x, y -> x))

      have(forall(t, in(t, identityFunction(A)) <=> in(t, cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (t === pair(y, y))))) by InstantiateForall(identityFunction(A))(
        identityFunction.definition of (x -> A)
      )
      thenHave(in(pair(x, x), identityFunction(A)) <=> in(pair(x, x), cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (pair(x, x) === pair(y, y)))) by InstantiateForall(pair(x, x))
      thenHave(in(pair(x, x), cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (pair(x, x) === pair(y, y)))) by Tautology
      thenHave(in(pair(x, x), cartesianProduct(A, A))) by Tautology

      have(in(firstInPair(pair(x, x)), A)) by Tautology.from(lastStep, firstInPairType of (x -> pair(x, x), A -> A, B -> A))
      thenHave(in(x, A)) by Substitution.ApplyRules(ss1)
    }

    have(in(x, A) <=> in(pair(x, x), identityFunction(A))) by Tautology.from(fwd, bwd)
  }

  // Rovelli Gianmaria
  val domainOfIdentityFunction = Lemma(relationDomain(identityFunction(A)) === A) {
    have(forall(t, in(t, relationDomain(identityFunction(A))) <=> exists(a, in(pair(t, a), identityFunction(A))))) by InstantiateForall(relationDomain(identityFunction(A)))(
      relationDomain.definition of (r -> identityFunction(A))
    )
    val relDomDef = thenHave(in(z, relationDomain(identityFunction(A))) <=> exists(a, in(pair(z, a), identityFunction(A)))) by InstantiateForall(z)
    val fwd = have(in(z, relationDomain(identityFunction(A))) ==> in(z, A)) subproof {
      assume(in(z, relationDomain(identityFunction(A))))
      val s1 = have(exists(a, in(pair(z, a), identityFunction(A)))) by Tautology.from(relDomDef)
      val subs = have(in(pair(z, a), identityFunction(A)) |- z === a) by Tautology.from(pairInIdentityFunction of (a -> z, b -> a))
      have(in(pair(z, a), identityFunction(A)) |- in(pair(z, a), identityFunction(A))) by Restate
      thenHave(in(pair(z, a), identityFunction(A)) |- in(pair(z, z), identityFunction(A))) by Substitution.ApplyRules(subs)
      thenHave(exists(a, in(pair(z, a), identityFunction(A))) |- in(pair(z, z), identityFunction(A))) by LeftExists
      have(in(pair(z, z), identityFunction(A))) by Tautology.from(lastStep, s1)
      have(in(z, A)) by Tautology.from(lastStep, inclusionImpliesInclusionInIdentity of (x -> z))
    }
    val bwd = have(in(z, A) ==> in(z, relationDomain(identityFunction(A)))) subproof {
      assume(in(z, A))
      have(in(pair(z, z), identityFunction(A))) by Tautology.from(inclusionImpliesInclusionInIdentity of (x -> z))
      thenHave(exists(a, in(pair(z, a), identityFunction(A)))) by RightExists
      have(in(z, relationDomain(identityFunction(A)))) by Tautology.from(lastStep, relDomDef)
    }
    have(in(z, relationDomain(identityFunction(A))) <=> in(z, A)) by Tautology.from(fwd, bwd)
    thenHave(forall(z, in(z, relationDomain(identityFunction(A))) <=> in(z, A))) by RightForall
    have(relationDomain(identityFunction(A)) === A) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationDomain(identityFunction(A)), y -> A))
  }

  // Rovelli Gianmaria
  val rangeOfIdentityFunction = Lemma(relationRange(identityFunction(A)) === A) {
    have(forall(t, in(t, relationRange(identityFunction(A))) <=> exists(a, in(pair(a, t), identityFunction(A))))) by InstantiateForall(relationRange(identityFunction(A)))(
      relationRange.definition of (r -> identityFunction(A))
    )
    val rangeDef = thenHave(in(z, relationRange(identityFunction(A))) <=> exists(a, in(pair(a, z), identityFunction(A)))) by InstantiateForall(z)

    val fwd = have(in(z, relationRange(identityFunction(A))) ==> in(z, A)) subproof {
      assume(in(z, relationRange(identityFunction(A))))
      val s1 = have(exists(a, in(pair(a, z), identityFunction(A)))) by Tautology.from(rangeDef)
      val subs = have(in(pair(a, z), identityFunction(A)) |- a === z) by Tautology.from(pairInIdentityFunction of (a -> a, b -> z))
      have(in(pair(a, z), identityFunction(A)) |- in(pair(a, z), identityFunction(A))) by Restate
      thenHave(in(pair(a, z), identityFunction(A)) |- in(pair(z, z), identityFunction(A))) by Substitution.ApplyRules(subs)
      thenHave(exists(a, in(pair(a, z), identityFunction(A))) |- in(pair(z, z), identityFunction(A))) by LeftExists
      have(in(pair(z, z), identityFunction(A))) by Tautology.from(lastStep, s1)
      have(in(z, A)) by Tautology.from(lastStep, inclusionImpliesInclusionInIdentity of (x -> z))
    }
    val bwd = have(in(z, A) ==> in(z, relationRange(identityFunction(A)))) subproof {
      assume(in(z, A))
      have(in(pair(z, z), identityFunction(A))) by Tautology.from(inclusionImpliesInclusionInIdentity of (x -> z))
      thenHave(exists(a, in(pair(a, z), identityFunction(A)))) by RightExists
      have(in(z, relationRange(identityFunction(A)))) by Tautology.from(lastStep, rangeDef)
    }
    have(in(z, relationRange(identityFunction(A))) <=> in(z, A)) by Tautology.from(fwd, bwd)
    thenHave(forall(z, in(z, relationRange(identityFunction(A))) <=> in(z, A))) by RightForall
    have(relationRange(identityFunction(A)) === A) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationRange(identityFunction(A)), y -> A))
  }

  // Rovelli Gianmaria
  val identityFunctionHasSameDomainRange = Lemma(relationDomain(identityFunction(A)) === relationRange(identityFunction(A))) {
    val subs = have(relationDomain(identityFunction(A)) === A) by Tautology.from(domainOfIdentityFunction)
    have(relationRange(identityFunction(A)) === A) by Tautology.from(rangeOfIdentityFunction)
    thenHave(relationRange(identityFunction(A)) === relationDomain(identityFunction(A))) by Substitution.ApplyRules(subs)
  }

  // Rovelli Gianmaria
  val Pi_iff = Lemma(
    in(f, Pi(A, B)) <=> (functional(f) /\ subset(f, Sigma(A, B)) /\ subset(A, relationDomain(f)))
  ) {
    have(forall(t, in(t, Pi(A, B)) <=> (in(t, powerSet(Sigma(A, B))) /\ (subset(A, relationDomain(t)) /\ functional(t))))) by InstantiateForall(Pi(A, B))(Pi.definition of (x -> A, f -> B))
    val s1 = thenHave(
      in(f, Pi(A, B))
        <=> (in(f, powerSet(Sigma(A, B))) /\ (subset(A, relationDomain(f)) /\ functional(f)))
    ) by InstantiateForall(f)
    have(in(f, powerSet(Sigma(A, B))) <=> subset(f, Sigma(A, B))) by Tautology.from(powerAxiom of (x -> f, y -> Sigma(A, B)))

    have(
      in(f, Pi(A, B))
        <=> (subset(f, Sigma(A, B)) /\ (subset(A, relationDomain(f)) /\ functional(f)))
    ) by Tautology.from(lastStep, s1)
  }

  // Rovelli Gianmaria
  val funIsRel = Lemma(in(f, Pi(A, B)) |- subset(f, Sigma(A, B))) {
    assume(in(f, Pi(A, B)))
    have(functional(f) /\ subset(f, Sigma(A, B)) /\ subset(A, relationDomain(f))) by Tautology.from(Pi_iff)
    thenHave(subset(f, Sigma(A, B))) by Tautology
  }

  // val setUnionMembership = Theorem(
  //   in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))
  // val restrictedFunction = DEF(f, x) --> The(g, ∀(t, in(t, g)
  // <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))(restrictedFunctionUniqueness)

  // Rovelli Gianmaria
  val domainType = Lemma(in(pair(a, b), f) /\ in(f, Pi(A, B)) |- in(a, A)) {
    assume(in(pair(a, b), f))
    assume(in(f, Pi(A, B)))

    val subs = have(Sigma(A, B) === restrictedFunction(B, A)) by InstantiateForall(Sigma(A, B))(Sigma.definition of (x -> A, f -> B))

    have(subset(f, Sigma(A, B))) by Tautology.from(funIsRel)
    have(forall(z, in(z, f) ==> in(z, Sigma(A, B)))) by Tautology.from(lastStep, subsetAxiom of (x -> f, y -> Sigma(A, B)))
    thenHave(in(pair(a, b), f) ==> in(pair(a, b), Sigma(A, B))) by InstantiateForall(pair(a, b))
    thenHave(in(pair(a, b), Sigma(A, B))) by Tautology
    val s1 = thenHave(in(pair(a, b), restrictedFunction(B, A))) by Substitution.ApplyRules(subs)

    have(in(pair(a, b), restrictedFunction(B, A)) <=> (in(pair(a, b), B) /\ in(a, A))) by Tautology.from(restrictedFunctionPairMembership of (t -> a, a -> b, f -> B, x -> A))
    have(in(pair(a, b), B) /\ in(a, A)) by Tautology.from(lastStep, s1)
    thenHave(in(a, A)) by Tautology
  }

  // Rovelli Gianmaria
  val domainOfDependentProductFunction = Lemma(in(f, Pi(A, B)) |- relationDomain(f) === A) {
    assume(in(f, Pi(A, B)))
    have(forall(t, in(t, relationDomain(f)) <=> exists(a, in(pair(t, a), f)))) by InstantiateForall(relationDomain(f))(
      relationDomain.definition of (r -> f)
    )
    val relDomDef = thenHave(in(z, relationDomain(f)) <=> exists(a, in(pair(z, a), f))) by InstantiateForall(z)
    have(forall(t, in(t, Pi(A, B)) <=> (in(t, powerSet(Sigma(A, B))) /\ (subset(A, relationDomain(t)) /\ functional(t))))) by InstantiateForall(
      Pi(A, B)
    )(Pi.definition of (x -> A, f -> B))
    thenHave(
      in(f, Pi(A, B))
        <=> (in(f, powerSet(Sigma(A, B))) /\ (subset(A, relationDomain(f)) /\ functional(f)))
    ) by InstantiateForall(f)
    val fwd = thenHave(in(f, powerSet(Sigma(A, B))) /\ (subset(A, relationDomain(f)) /\ functional(f))) by Tautology

    val bwd = have(subset(relationDomain(f), A)) subproof {

      have(in(z, relationDomain(f)) ==> in(z, A)) subproof {
        assume(in(z, relationDomain(f)))
        assume(!in(z, A))
        val s1 = have(exists(a, in(pair(z, a), f))) by Tautology.from(relDomDef)

        have(in(pair(z, a), f) |- in(z, A)) by Tautology.from(domainType of (a -> z, b -> a, B -> B))
        thenHave(exists(a, in(pair(z, a), f)) |- in(z, A)) by LeftExists
        have(in(z, A)) by Tautology.from(lastStep, s1)
      }
      thenHave(forall(z, in(z, relationDomain(f)) ==> in(z, A))) by RightForall
      have(subset(relationDomain(f), A)) by Tautology.from(lastStep, subsetAxiom of (x -> relationDomain(f), y -> A))
    }

    have(relationDomain(f) === A) by Tautology.from(fwd, bwd, subsetEqualitySymmetry of (x -> relationDomain(f), y -> A))
  }

  // this could be hard
  // see `pairSingletonIsFunctional`
  val identityFunctionIsFunctional = Lemma(functional(identityFunction(A))) {

    val id = identityFunction(A)

    val rel = have(relation(id)) subproof {
      have(forall(t, in(t, id) <=> in(t, cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (t === pair(y, y))))) by InstantiateForall(id)(
        identityFunction.definition of (x -> A)
      )
      thenHave(forall(t, in(t, id) ==> in(t, cartesianProduct(A, A)))) by Tautology
      have(relationBetween(id, A, A)) by Tautology.from(
        lastStep,
        subsetAxiom of (x -> id, y -> cartesianProduct(A, A)),
        relationBetween.definition of (r -> id, a -> A, b -> A)
      )
      thenHave(exists(b, relationBetween(id, A, b))) by RightExists
      thenHave(exists(a, exists(b, relationBetween(id, a, b)))) by RightExists
      have(thesis) by Tautology.from(lastStep, relation.definition of r -> id)
    }

    val uniq = have(forall(a, exists(b, in(pair(a, b), id)) ==> existsOne(b, in(pair(a, b), id)))) subproof {
      val a_eq_b_premis2 = have(((a === y) /\ (y === b)) |- (a === b)) by Restate.from(equalityTransitivity of (x -> a, z -> b))
      have((pair(a, b) === pair(y, y)) |- (pair(a, b) === pair(y, y))) by Tautology
      thenHave((pair(a, b) === pair(y, y)) |- ((a === y) /\ (b === y))) by Substitution.ApplyRules(pairExtensionality of (c -> y, d -> y))
      val a_eq_b_premis1 = thenHave((pair(a, b) === pair(y, y)) |- ((a === y) /\ (y === b))) by Tautology
      // val a_eq_b = have((pair(a, b) === pair(y, y)) ==> (a === b)) by Substitution.ApplyRules(eq_trans)(premis1)
      have((pair(a, b) === pair(y, y)) |- (a === b)) by Tautology.from(a_eq_b_premis1, a_eq_b_premis2)
      val a_eq_b = thenHave(exists(y, pair(a, b) === pair(y, y)) |- (a === b)) by LeftExists

      have(forall(t, in(t, id) <=> in(t, cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (t === pair(y, y))))) by InstantiateForall(id)(identityFunction.definition of (x -> A))
      thenHave(in(pair(a, b), id) <=> in(pair(a, b), cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (pair(a, b) === pair(y, y)))) by InstantiateForall(pair(a, b))
      thenHave(in(pair(a, b), id) |- in(pair(a, b), cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (pair(a, b) === pair(y, y)))) by Weakening
      thenHave(in(pair(a, b), id) |- in(pair(a, b), cartesianProduct(A, A)) /\ exists(y, pair(a, b) === pair(y, y))) by Weakening
      val eq_premis = thenHave(in(pair(a, b), id) |- exists(y, pair(a, b) === pair(y, y))) by Weakening
      val eq = have(in(pair(a, b), id) |- (a === b)) by Tautology.from(a_eq_b, eq_premis)

      have(in(pair(a, b), id) |- in(pair(a, b), id)) by Tautology
      thenHave((in(pair(a, b), id), (z === b)) |- in(pair(a, z), id)) by RightSubstEq.withParameters(List((z, b)), lambda(z, in(pair(a, z), id)))
      val dir1 = thenHave(in(pair(a, b), id) |- (z === b) ==> in(pair(a, z), id)) by Tautology

      have((z === a) /\ (a === b) |- (z === b)) by Restate.from(equalityTransitivity of (x -> z, y -> a, z -> b))
      have(in(pair(a, b), id) |- (z === a) ==> (z === b)) by Tautology.from(eq, lastStep)
      val dir2 = have(in(pair(a, b), id) |- in(pair(a, z), id) ==> (z === b)) by Tautology.from(eq of (b -> z), lastStep)

      val equiv_z = have(in(pair(a, b), id) |- (z === b) <=> in(pair(a, z), id)) by Tautology.from(dir1, dir2)
      thenHave(in(pair(a, b), id) |- forall(z, (z === b) <=> in(pair(a, z), id))) by RightForall
      thenHave(in(pair(a, b), id) |- exists(b, forall(z, (z === b) <=> in(pair(a, z), id)))) by RightExists
      thenHave(in(pair(a, b), id) |- existsOne(b, in(pair(a, b), id))) by RightExistsOne
      thenHave(exists(b, in(pair(a, b), id)) |- existsOne(b, in(pair(a, b), id))) by LeftExists
      thenHave(exists(b, in(pair(a, b), id)) ==> existsOne(b, in(pair(a, b), id))) by Restate
      thenHave(thesis) by RightForall
    }
    have(thesis) by Tautology.from(rel, uniq, functional.definition of f -> id)
  }

  // Rovelli Gianmaria
  val functionalApplicationOfIdentity = Lemma(in(B, A) |- (app(identityFunction(A), B) === B)) {
    assume(in(B, A))

    val appDef = have(
      (app(identityFunction(A), B) === B) <=> (((functional(identityFunction(A)) /\ in(B, relationDomain(identityFunction(A)))) ==> in(pair(B, B), identityFunction(A))) /\
        ((!functional(identityFunction(A)) \/ !in(B, relationDomain(identityFunction(A)))) ==> (B === ∅)))
    ) by InstantiateForall(B)(app.definition of (f -> identityFunction(A), x -> B, b -> B))

    val sub1 = have(((functional(identityFunction(A)) /\ in(B, relationDomain(identityFunction(A)))) ==> in(pair(B, B), identityFunction(A)))) subproof {
      assume(functional(identityFunction(A)))
      assume(in(B, relationDomain(identityFunction(A))))

      have(in(pair(B, B), identityFunction(A))) by Tautology.from(inclusionImpliesInclusionInIdentity of (x -> B))
    }

    val sub2 = have((!functional(identityFunction(A)) \/ !in(B, relationDomain(identityFunction(A)))) ==> (B === ∅)) subproof {
      assume(!functional(identityFunction(A)) \/ !in(B, relationDomain(identityFunction(A))))

      val ssub1 = have(!functional(identityFunction(A)) ==> (B === emptySet)) subproof {
        assume(!functional(identityFunction(A)))
        have(functional(identityFunction(A))) by Tautology.from(identityFunctionIsFunctional)
        // contradiction
        thenHave(!functional(identityFunction(A)) |- ()) by Tautology
        thenHave(!functional(identityFunction(A)) |- (B === emptySet)) by Weakening
      }
      val ssub2 = have(!in(B, relationDomain(identityFunction(A))) ==> (B === emptySet)) subproof {
        val hp = assume(!in(B, relationDomain(identityFunction(A))))
        val ss = have(relationDomain(identityFunction(A)) === A) by Tautology.from(domainOfIdentityFunction)
        have(!in(B, A)) by Substitution.ApplyRules(ss)(hp)
        // contradiction
        thenHave(!in(B, relationDomain(identityFunction(A))) |- ()) by Tautology
        thenHave(!in(B, relationDomain(identityFunction(A))) |- (B === emptySet)) by Weakening
      }

      have(thesis) by Tautology.from(ssub1, ssub2)
    }

    have(app(identityFunction(A), B) === B) by Tautology.from(sub1, sub2, appDef)
  }

  // Rovelli Gianmaria
  val inclusionExtensionality = Lemma(in(x, A) /\ (x === z) |- in(z, A)) {
    val step1 = assume(x === z)
    assume(in(x, A))
    thenHave(thesis) by Substitution.ApplyRules(step1)
  }

  // Rovelli Gianmaria
  val singletonIsSubsetOfIdentity = Lemma(subset(singleton(x), A) <=> in(x, A)) {
    // ==>
    val fwd = have(subset(singleton(x), A) ==> in(x, A)) subproof {
      assume(subset(singleton(x), A))
      val s1 = have(in(x, singleton(x))) by Tautology.from(singletonHasNoExtraElements of (y -> x))
      have(forall(z, in(z, singleton(x)) ==> in(z, A))) by Tautology.from(subsetAxiom of (x -> singleton(x), y -> A))
      val s2 = thenHave(in(x, singleton(x)) ==> in(x, A)) by InstantiateForall(x)
      have(in(x, A)) by Tautology.from(s1, s2)
    }
    val bwd = have(in(x, A) ==> subset(singleton(x), A)) subproof {
      assume(in(x, A))
      val s1 = have(in(z, singleton(x)) ==> (x === z)) by Tautology.from(singletonHasNoExtraElements of (y -> z))
      val s2 = have((x === z) ==> in(z, A)) by Tautology.from(inclusionExtensionality)
      have(in(z, singleton(x)) ==> in(z, A)) by Tautology.from(s1, s2)
      val s3 = thenHave(forall(z, in(z, singleton(x)) ==> in(z, A))) by RightForall
      have(subset(singleton(x), A)) by Tautology.from(s3, subsetAxiom of (x -> singleton(x), y -> A))
    }
    have(thesis) by Tautology.from(fwd, bwd)
  }

  // Rovelli Gianmaria
  val inclusionImpliesSubsetOfIdenity = Lemma(in(x, A) |- subset(singleton(pair(x, x)), identityFunction(A))) {
    assume(in(x, A))

    val subsetDef = have(
      subset(singleton(pair(x, x)), identityFunction(A))
        <=> (forall(z, in(z, singleton(pair(x, x))) ==> in(z, identityFunction(A))))
    ) by Tautology.from(subsetAxiom of (x -> singleton(pair(x, x)), y -> identityFunction(A)))

    have(in(z, singleton(pair(x, x))) ==> in(z, identityFunction(A))) subproof {
      assume(in(z, singleton(pair(x, x))))
      val ss1 = have(z === pair(x, x)) by Tautology.from(singletonHasNoExtraElements of (y -> z, x -> pair(x, x)))
      have(forall(t, in(t, identityFunction(A)) <=> in(t, cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (t === pair(y, y))))) by InstantiateForall(identityFunction(A))(
        identityFunction.definition of (x -> A)
      )
      val iddef = thenHave(in(pair(x, x), identityFunction(A)) <=> in(pair(x, x), cartesianProduct(A, A)) /\ exists(y, in(y, A) /\ (pair(x, x) === pair(y, y)))) by InstantiateForall(pair(x, x))
      val p1 = have(in(pair(x, x), cartesianProduct(A, A))) by Tautology.from(pairInCartesianProduct of (a -> x, b -> x, x -> A, y -> A))
      have(in(x, A) /\ (pair(x, x) === pair(x, x))) by Tautology
      val p2 = thenHave(exists(y, in(y, A) /\ (pair(x, x) === pair(y, y)))) by RightExists
      have(in(pair(x, x), identityFunction(A))) by Tautology.from(iddef, p1, p2)
      thenHave(in(z, identityFunction(A))) by Substitution.ApplyRules(ss1)
    }
    thenHave(forall(z, in(z, singleton(pair(x, x))) ==> in(z, identityFunction(A)))) by RightForall
    have(subset(singleton(pair(x, x)), identityFunction(A))) by Tautology.from(lastStep, subsetDef)
  }

  // Rovelli Gianmaria
  val relationDomainEquality = Lemma((x === y) /\ in(x, relationDomain(f)) |- in(y, relationDomain(f))) {
    have(thesis) by Tautology.from(inclusionExtensionality of (x -> x, A -> relationDomain(f), z -> y))
  }
  // Rovelli Gianmaria
  val relationDomainNotEquality = Lemma((x === y) /\ !in(x, relationDomain(f)) |- !in(y, relationDomain(f))) {
    val step1 = assume(x === y)
    assume(!in(x, relationDomain(f)))
    thenHave(thesis) by Substitution.ApplyRules(step1)
  }

  // Rovelli Gianmaria
  val functionalExtensionality = Lemma(functional(f) |- ((x === y) ==> (app(f, x) === app(f, y)))) {
    assume(x === y)
    have(forall(z, in(z, x) <=> in(z, y)) <=> (x === y)) by Tautology.from(extensionalityAxiom)
    thenHave(forall(z, in(z, x) <=> in(z, y))) by Tautology
    thenHave(in(z, x) <=> in(z, y)) by InstantiateForall(z)

    val sub1 = have(((functional(f) /\ in(x, relationDomain(f))) |- in(pair(x, app(f, y)), f))) subproof {
      assume(functional(f))
      assume(in(x, relationDomain(f)))
      val fx = app(f, x)
      val fy = app(f, y)
      val eq = have(in(y, relationDomain(f))) by Tautology.from(relationDomainEquality)
      val appDef = have(
        (fy === fy) <=> (((functional(f) /\ in(y, relationDomain(f))) ==> in(pair(y, fy), f)) /\ ((!functional(f) \/ !in(y, relationDomain(f))) ==> (fy === ∅)))
      ) by InstantiateForall(fy)(app.definition of (x -> y, b -> fy))
      val fwd = have(in(pair(y, fy), f)) by Tautology.from(eq, appDef)
      thenHave(in(pair(x, fy), f)) by Substitution.ApplyRules(x === y)
    }
    val sub2 = have((!functional(f) \/ !in(x, relationDomain(f))) |- (app(f, y) === ∅)) subproof {
      assume(!functional(f) \/ !in(x, relationDomain(f)))
      // i need to prove !functional(f) |- app(f,y) === emptySet
      val subsub1 = have(!functional(f) |- app(f, y) === emptySet) subproof {
        assume(!functional(f))
        val fx = app(f, x)
        val fy = app(f, y)
        val appDef = have(
          (fy === fy) <=> (((functional(f) /\ in(y, relationDomain(f))) ==> in(pair(y, fy), f)) /\ ((!functional(f) \/ !in(y, relationDomain(f))) ==> (fy === ∅)))
        ) by InstantiateForall(fy)(app.definition of (x -> y, b -> fy))
        have(fy === emptySet) by Tautology.from(appDef)
        have(thesis) by Tautology.from(lastStep)
      }

      // i need to prove !in(x, relationDomain(f)) |- app(f,y) === emptySet
      val subsub2 = have(!in(x, relationDomain(f)) |- app(f, y) === emptySet) subproof {
        assume(!in(x, relationDomain(f)))
        val fx = app(f, x)
        val fy = app(f, y)
        val eq = have(!in(y, relationDomain(f))) by Tautology.from(relationDomainNotEquality)
        val appDef = have(
          (fy === fy) <=> (((functional(f) /\ in(y, relationDomain(f))) ==> in(pair(y, fy), f)) /\ ((!functional(f) \/ !in(y, relationDomain(f))) ==> (fy === ∅)))
        ) by InstantiateForall(fy)(app.definition of (x -> y, b -> fy))
        have(fy === emptySet) by Tautology.from(eq, appDef)
        have(thesis) by Tautology.from(lastStep)
      }

      have(thesis) by Tautology.from(subsub1, subsub2)
    }

    val appDef = have(
      (app(f, x) === app(f, y)) <=> (((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, app(f, y)), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (app(f, y) === ∅)))
    ) by InstantiateForall(app(f, y))(app.definition of (b -> app(f, y)))
    have(app(f, x) === app(f, y)) by Tautology.from(sub1, sub2, appDef)
    have(thesis) by Tautology.from(lastStep)
  }

  // /*
  // (* ********************************************************************** *)
  // (* AC1 ⟹ AC2                                                            *)
  // (* ********************************************************************** *)
  //  */
  // // lemma AC1_AC2_aux1: "⟦f:(∏X ∈ A. X);  B ∈ A;  0∉A⟧ ⟹ {f`B} ⊆ B ∩ {f`C. C ∈ A}"
  // // by(fast elim !: applyType)
  //

  // lemma function_apply_Pair: "⟦function(f);  a ∈ domain(f)⟧ ⟹ <a,f`a>: f"
  // Rovelli Gianmaria
  val function_apply_pair = Lemma(functional(f) /\ in(a, relationDomain(f)) |- in(pair(a, app(f, a)), f)) {
    assume(functional(f) /\ in(a, relationDomain(f)))
    val appDef = have(
      (app(f, a) === app(f, a)) <=> (((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, app(f, a)), f)) /\ ((!functional(f) \/ !in(a, relationDomain(f))) ==> (app(f, a) === ∅)))
    ) by InstantiateForall(app(f, a))(app.definition of x -> a)
    thenHave(((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, app(f, a)), f)) /\ ((!functional(f) \/ !in(a, relationDomain(f))) ==> (app(f, a) === ∅))) by Tautology
    thenHave(((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, app(f, a)), f))) by Tautology
    thenHave(in(pair(a, app(f, a)), f)) by Tautology
  }

  // lemma apply_Pair: "⟦f ∈ Pi(A,B);  a ∈ A⟧ ⟹ <a,f`a>: f"
  // Rovelli Gianmaria
  val apply_pair = Lemma(
    in(f, Pi(A, B)) /\ in(a, A) |- in(pair(a, app(f, a)), f)
  ) {
    assume(in(a, A))
    assume(in(f, Pi(A, B)))

    have(in(f, Pi(A, B)) |- (functional(f) /\ subset(f, Sigma(A, B)) /\ subset(A, relationDomain(f)))) by Tautology.from(Pi_iff)
    thenHave(in(f, Pi(A, B)) |- (functional(f) /\ subset(A, relationDomain(f)))) by Weakening
    val step1 = thenHave(in(f, Pi(A, B)) |- functional(f)) by Weakening

    val sub1 = have(
      in(a, A) /\ in(f, Pi(A, B)) |-
        in(a, relationDomain(f))
    ) subproof {

      val step1 = have(in(f, Pi(A, B)) |- (functional(f) /\ subset(f, Sigma(A, B)) /\ subset(A, relationDomain(f)))) by Tautology.from(Pi_iff)

      have(
        in(a, A) /\ in(f, Pi(A, B))
          |-
          forall(a, in(a, A) ==> in(a, relationDomain(f)))
      ) by Tautology.from(step1, subsetAxiom of (x -> A, y -> relationDomain(f)))
      thenHave(
        in(a, A) /\ in(f, Pi(A, B)) |-
          in(a, A) ==> in(a, relationDomain(f))
      ) by InstantiateForall(a)
      thenHave(
        thesis
      ) by Tautology
    }

    have(thesis) by Tautology.from(step1, sub1, function_apply_pair)
  }

  // // lemma applyType [TC]: "⟦f ∈ Pi(A,B);  a ∈ A⟧ ⟹ f`a ∈ B(a)"
  // // by (blast intro: apply_Pair dest: fun_is_rel)
  // Rovelli Gianmaria
  val applyType = Lemma(
    in(f, Pi(A, B)) /\ in(a, A) |- in(app(f, a), app(B, a))
  ) {
    // in(f, Pi(A, B)) /\ in(a, A) |- in(pair(a, app(f, a)), f)
    // since in(f, Pi(A,B)) => subset(A, relationDomain(f)) /\ functional(f)
    // functional(f) /\ in(a, relationDomain(f)) |- in(pair(a, b), f) <=> (app(f, a) === b)
    // so app(f,a) === b
    // val funIsRel = Lemma(in(f, Pi(A, B)) |- subset(f, Sigma(A, B))) {
    // val apply_pair = Lemma(
    //   in(f, Pi(A, B)) /\ in(a, A) |- in(pair(a, app(f, a)), f)

    // val app = DEF(f, x) --> The(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))(functionApplicationUniqueness)
    // val restrictedFunction = DEF(f, x) --> The(g, ∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))(restrictedFunctionUniqueness)

    // in(b, c) /\ (b === app(f, a)) /\ (c === app(B, a))
    // in(b, c) /\ in(pair(a, b), f) /\ in(pair(a, c), B)
    // in(b, c) /\ in(pair(a, b), Sigma(A, B)) /\ in(pair(a, c), B)
    // in(b, c) /\ in(pair(a, b), restrictedFunction(B, A)) /\ in(pair(a, c), B)
    // in(b, c) /\ (in(pair(a, b), B) /\ ()) /\ in(pair(a, c), B)

    sorry
  }

  // Rovelli Gianmaria
  val AC1AC2aux1 = Lemma({
    in(f, Pi(A, identityFunction(A))) /\ in(B, A) /\ !in(emptySet, A) |- subset(singleton(app(f, B)), setIntersection(B, relationRange(f)))
  }) {

    assume(in(f, Pi(A, identityFunction(A))))
    assume(in(B, A))
    assume(!in(emptySet, A))

    val sub1 = have(in(a, singleton(app(f, B))) |- in(a, B)) subproof {
      assume(in(B, A))
      assume(in(a, singleton(app(f, B))))

      val step1 = have(in(a, singleton(app(f, B))) |- a === app(f, B)) by Tautology.from(singletonHasNoExtraElements of (y -> a, x -> app(f, B)))

      have(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(app(f, B), app(identityFunction(A), B))) by Tautology.from(applyType of (f -> f, A -> A, B -> identityFunction(A), a -> B))
      thenHave(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(app(f, B), B)) by Substitution.ApplyRules(functionalApplicationOfIdentity)
      thenHave(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(a, B)) by Substitution.ApplyRules(step1)
      thenHave(thesis) by Restate
    }

    val sub2 = have(in(a, singleton(app(f, B))) |- in(a, relationRange(f))) subproof {
      assume(in(B, A))
      assume(in(a, singleton(app(f, B))))

      val step1 = have(in(a, singleton(app(f, B))) |- a === app(f, B)) by Tautology.from(singletonHasNoExtraElements of (y -> a, x -> app(f, B)))

      have(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(pair(B, app(f, B)), f)) by Tautology.from(apply_pair of (A -> A, B -> identityFunction(A), a -> B, f -> f))
      thenHave(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(pair(B, a), f)) by Substitution.ApplyRules(step1)
      val step2 = thenHave(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- exists(y, in(pair(y, a), f))) by RightExists

      have(forall(t, in(t, relationRange(f)) <=> exists(y, in(pair(y, t), f)))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
      val rangeDef = thenHave(in(a, relationRange(f)) <=> (∃(y, in(pair(y, a), f)))) by InstantiateForall(a)

      have(in(B, A) /\ in(a, singleton(app(f, B))) |- in(a, relationRange(f))) by Tautology.from(step2, rangeDef)
      thenHave(thesis) by Restate
    }

    val step1 = have(in(a, singleton(app(f, B))) |- in(a, B)) by Tautology.from(sub1)
    val step2 = have(in(a, singleton(app(f, B))) |- in(a, relationRange(f))) by Tautology.from(sub2)
    val step3 =
      have(in(a, singleton(app(f, B))) |- in(a, setIntersection(B, relationRange(f)))) by Tautology.from(step1, step2, setIntersectionMembership of (t -> a, x -> B, y -> relationRange(f)))
    thenHave(() |- (in(a, singleton(app(f, B))) ==> in(a, setIntersection(B, relationRange(f))))) by Tautology
    val step4 = thenHave(() |- forall(a, in(a, singleton(app(f, B))) ==> in(a, setIntersection(B, relationRange(f))))) by RightForall

    val myx = singleton(app(f, B))
    val myy = setIntersection(B, relationRange(f))
    have(() |- subset(myx, myy)) by Tautology.from(step4, subsetAxiom of (x -> myx, y -> myy))
    thenHave(thesis) by Restate
  }

  // lemma AC1_AC2_aux2:
  //     "⟦pairwise_disjoint(A); B ∈ A; C ∈ A; D ∈ B; D ∈ C⟧ ⟹ f`B = f`C"
  // Rovelli Gianmaria
  val AC1AC2aux2 = Lemma((pairwiseDisjoint(A) /\ in(B, A) /\ in(C, A) /\ in(D, B) /\ in(D, C) /\ functional(f)) |- app(f, B) === app(f, C)) {

    assume(pairwiseDisjoint(A))
    assume(in(B, A))
    assume(in(C, A))
    assume(in(D, B))
    assume(in(D, C))
    assume(functional(f))

    val sub1 = have((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- B === C) subproof {
      have((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- forall(B, forall(C, in(B, A) /\ in(C, A) ==> ((!(setIntersection(B, C) === emptySet)) ==> (B === C))))) by Tautology.from(
        pairwiseDisjoint.definition of (x -> B, y -> C)
      )
      thenHave((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- forall(C, in(B, A) /\ in(C, A) ==> ((!(setIntersection(B, C) === emptySet)) ==> (B === C)))) by InstantiateForall(B)
      val step1 = thenHave((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- in(B, A) /\ in(C, A) ==> ((!(setIntersection(B, C) === emptySet)) ==> (B === C))) by InstantiateForall(C)

      val step2 = thenHave((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- ((!(setIntersection(B, C) === emptySet)) ==> (B === C))) by Tautology

      val step3 = have((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- in(D, setIntersection(B, C))) by Tautology.from(setIntersectionMembership of (t -> D, x -> B, y -> C))
      val step4 = have(in(D, setIntersection(B, C)) |- !(setIntersection(B, C) === emptySet)) by Tautology.from(step3, setWithElementNonEmpty of (x -> setIntersection(B, C), y -> D))
      val step5 = have((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- B === C) by Tautology.from(step4, step3, step2)
      have(thesis) by Tautology.from(step5)
    }

    // BROKEN version with apply instead of app , but stucked with (x === y) ==> image(f, x) === image(f,y) which it is not true in general
    // val eqSingUnfold = have((singleton(B) === singleton(C)) <=> (B === C)) by Tautology.from(singletonExtensionality of (x -> B, y -> C))
    // val eqSing = have((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C)) |- singleton(B) === singleton(C)) by Tautology.from(sub1, eqSingUnfold)
    // val step1 = have(image(f, singleton(B)) === image(f, singleton(C))) by Tautology.from(eqSing, imageExtensionality of (x -> singleton(B), y -> singleton(C)))
    // val step2 = have(apply(f, C) === union(image(f, singleton(C)))) by InstantiateForall(apply(f, C))(apply.definition of (a -> C))
    // have(apply(f, B) === union(image(f, singleton(B)))) by InstantiateForall(apply(f, B))(apply.definition of (a -> B))
    // thenHave(apply(f, B) === union(image(f, singleton(C)))) by Substitution.ApplyRules(step1)
    // thenHave(apply(f, B) === apply(f, C)) by Substitution.ApplyRules(step2)

    val step1 = have(app(f, B) === app(f, C)) by Tautology.from(sub1, functionalExtensionality of (x -> B, y -> C))

    have(thesis) by Tautology.from(lastStep)
  }

  val firstOfPairInDomain = Lemma(in(pair(a, b), f) |- in(a, relationDomain(f))) {

    assume(in(pair(a, b), f))
    val existsB = thenHave(exists(b, in(pair(a, b), f))) by RightExists

    have(forall(t, in(t, relationDomain(f)) <=> exists(b, in(pair(t, b), f)))) by InstantiateForall(relationDomain(f))(
      relationDomain.definition of (r -> f)
    )
    val relDomDef = thenHave(in(a, relationDomain(f)) <=> exists(b, in(pair(a, b), f))) by InstantiateForall(a)
    have(in(a, relationDomain(f))) by Tautology.from(lastStep, existsB)
  }

  // Rovelli Gianmaria
  val intersectionInSingleton = Lemma(
    pairwiseDisjoint(A) /\ in(f, Pi(A, identityFunction(A))) /\ in(B, A) /\ !in(emptySet, A)
      |- in(x, setIntersection(B, relationRange(f))) ==> in(x, singleton(app(f, B)))
  ) {
    assume(in(x, setIntersection(B, relationRange(f))))
    assume(in(f, Pi(A, identityFunction(A))))
    assume(!in(emptySet, A))
    val BinA = assume(in(B, A))
    val disj = assume(pairwiseDisjoint(A))

    // -------------------------------------------------------------------------------------------------------
    // Preliminaries
    val prel = have(in(x, B) /\ in(x, relationRange(f))) by Tautology.from(setIntersectionMembership of (t -> x, x -> B, y -> relationRange(f)))
    val xInRange = have(in(x, relationRange(f))) by Weakening(lastStep)
    val xInB = have(in(x, B)) by Weakening(prel)

    have(forall(t, in(t, Pi(A, identityFunction(A))) <=> (in(t, powerSet(Sigma(A, identityFunction(A)))) /\ (subset(A, relationDomain(t)) /\ functional(t))))) by InstantiateForall(
      Pi(A, identityFunction(A))
    )(Pi.definition of (x -> A, f -> identityFunction(A)))
    thenHave(
      in(f, Pi(A, identityFunction(A)))
        <=> (in(f, powerSet(Sigma(A, identityFunction(A)))) /\ (subset(A, relationDomain(f)) /\ functional(f)))
    ) by InstantiateForall(f)
    val fIsFun = thenHave(functional(f)) by Tautology

    val s1bInDomain = have(relationDomain(f) === A) by Tautology.from(domainOfDependentProductFunction of (B -> identityFunction(A)))
    assume(in(B, A))
    val bInDomain = thenHave(in(B, relationDomain(f))) by Substitution.ApplyRules(s1bInDomain)

    have(forall(t, in(t, relationRange(f)) <=> exists(a, in(pair(a, t), f)))) by InstantiateForall(relationRange(f))(
      relationRange.definition of (r -> f)
    )
    val rangeDef = thenHave(in(x, relationRange(f)) <=> exists(t, in(pair(t, x), f))) by InstantiateForall(x)
    val existsT = have(exists(t, in(pair(t, x), f))) by Tautology.from(lastStep, xInRange)

    val tInDomain = have(in(pair(t, x), f) |- in(t, relationDomain(f))) by Tautology.from(firstOfPairInDomain of (a -> t, b -> x))
    val xIsApp = have(
      in(pair(t, x), f)
        |- (app(f, t) === x)
    ) by Tautology.from(lastStep, fIsFun, pairInFunctionIsApp of (a -> t, b -> x))
    have(in(pair(t, x), f) |- in(x, singleton(app(f, t)))) by Tautology.from(lastStep, singletonHasNoExtraElements of (x -> app(f, t), y -> x))

    val tInA = have(in(pair(t, x), f) |- in(t, A)) by Tautology.from(domainType of (a -> t, b -> x, A -> A, B -> identityFunction(A)))
    val tsubs = have(in(pair(t, x), f) |- app(identityFunction(A), t) === t) by Tautology.from(lastStep, functionalApplicationOfIdentity of (a -> t, b -> x, A -> A, B -> t))

    have(in(pair(t, x), f) |- in(app(f, t), app(identityFunction(A), t))) by Tautology.from(tInA, applyType of (a -> t, B -> identityFunction(A)))
    thenHave(in(pair(t, x), f) |- in(app(f, t), t)) by Substitution.ApplyRules(tsubs)
    val xInT = thenHave(in(pair(t, x), f) |- in(x, t)) by Substitution.ApplyRules(xIsApp)
    // --------------------------------------------------------------------------------------------------------

    have(
      in(pair(t, x), f)
        |- app(f, B) === app(f, t)
    ) by Tautology.from(disj, BinA, tInA, xInB, xInT, fIsFun, AC1AC2aux2 of (C -> t, D -> x))
    thenHave(
      in(pair(t, x), f)
        |- app(f, B) === x
    ) by Substitution.ApplyRules(xIsApp)
    thenHave(
      exists(t, in(pair(t, x), f))
        |- app(f, B) === x
    ) by LeftExists
    have(app(f, B) === x) by Tautology.from(lastStep, existsT)
    have(in(x, singleton(app(f, B)))) by Tautology.from(lastStep, singletonHasNoExtraElements of (y -> x, x -> app(f, B)))
  }

  // Rovelli Gianmaria
  val intersectionSubsetSingleton = Lemma(
    pairwiseDisjoint(A) /\ in(f, Pi(A, identityFunction(A))) /\ in(B, A) /\ !in(emptySet, A)
      |- subset(setIntersection(B, relationRange(f)), singleton(app(f, B)))
  ) {
    assume(in(f, Pi(A, identityFunction(A))))
    assume(!in(emptySet, A))
    assume(in(B, A))
    assume(pairwiseDisjoint(A))

    // lemma2
    // (pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C), functional(f)) |- app(f, B) === app(f, C)

    val inter = setIntersection(B, relationRange(f))
    val singl = singleton(app(f, B))

    have(in(z, inter) ==> in(z, singl)) by Tautology.from(intersectionInSingleton of (x -> z))
    thenHave(forall(z, in(z, inter) ==> in(z, singl))) by RightForall

    have(subset(inter, singl)) by Tautology.from(lastStep, subsetAxiom of (x -> inter, y -> singl))
  }

  // lemma AC1_AC2: "AC1 ⟹ AC2"
  // Rovelli Gianmaria
  val AC1AC2 = Lemma(
    forall(A, !in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A))))))
      ==>
        forall(
          A,
          !in(emptySet, A) /\ pairwiseDisjoint(A)
            ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
        )
  ) {
    assume(forall(A, !in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A)))))))

    val sub1 = have(
      !in(emptySet, A) /\ pairwiseDisjoint(A)
        ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
    ) subproof {
      assume(!in(emptySet, A))
      assume(pairwiseDisjoint(A))

      have(!in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A)))))) by InstantiateForall
      val fExists = have(exists(f, in(f, Pi(A, identityFunction(A))))) by Tautology.from(lastStep)

      val inter = setIntersection(B, relationRange(f))
      val singl = singleton(app(f, B))

      val ssub1 = have(in(f, Pi(A, identityFunction(A))) |- in(B, A) ==> exists(y, setIntersection(B, relationRange(f)) === singleton(y))) subproof {
        assume(in(f, Pi(A, identityFunction(A))))
        assume(in(B, A))

        val fwd = have(
          subset(singl, inter)
        ) by Tautology.from(AC1AC2aux1)
        val bwd = have(
          subset(inter, singl)
        ) by Tautology.from(intersectionSubsetSingleton)
        have(inter === singl) by Tautology.from(fwd, bwd, subsetEqualitySymmetry of (x -> inter, y -> singl))
        thenHave(exists(y, setIntersection(B, relationRange(f)) === singleton(y))) by RightExists
      }
      thenHave(in(f, Pi(A, identityFunction(A))) |- forall(B, in(B, A) ==> exists(y, setIntersection(B, relationRange(f)) === singleton(y)))) by RightForall
      thenHave(in(f, Pi(A, identityFunction(A))) |- exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))) by RightExists
      thenHave(exists(f, in(f, Pi(A, identityFunction(A)))) |- exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))) by LeftExists
      have(exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))) by Tautology.from(lastStep, fExists)
    }

    have(
      forall(
        A,
        !in(emptySet, A) /\ pairwiseDisjoint(A)
          ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
      )
    ) by RightForall(sub1)
  }

  // Rovelli Gianmaria
  val iffElimination = Lemma(
    (p /\ P(x)) <=> (p /\ P(y)) |- P(x) <=> P(y)
  ) {
    assume((p /\ P(x)) <=> (p /\ P(y)))
    have((p /\ P(x)) ==> (p /\ P(y))) by Tautology
    val s1 = thenHave(!p \/ !P(x) \/ (p /\ P(y))) by Tautology
    have((p /\ P(y)) ==> (p /\ P(x))) by Tautology
    val s2 = thenHave(!p \/ !P(y) \/ (p /\ P(x))) by Tautology

    sorry
  }

  val cartesianProductWithIdentityUniqueness = Theorem(
    existsOne(g, forall(t, in(t, g) <=> (exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b)))))))
  ) {
    sorry
  }

  // union of all elements like {B*{B}. B ∈ A}
  val cartesianProductWithIdentity = DEF(A) -->
    The(g, forall(t, in(t, g) <=> (exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b)))))))(cartesianProductWithIdentityUniqueness)
  // The(g, forall(t, in(t, g) <=> (in(firstInPair(t), A) /\ (secondInPair(t) === singleton(firstInPair(t))))))(cartesianProductWithIdentityUniqueness)

  // Rovelli Gianmaria
  val cartesianProductEquality = Lemma(
    (cartesianProduct(x, A) === cartesianProduct(x, B)) ==> (A === B)
  ) {
    assume((cartesianProduct(x, A) === cartesianProduct(x, B)))
    have(
      forall(z, in(z, cartesianProduct(x, A)) <=> in(z, cartesianProduct(x, B)))
        <=> (cartesianProduct(x, A) === cartesianProduct(x, B))
    ) by Tautology.from(extensionalityAxiom of (x -> cartesianProduct(x, A), y -> cartesianProduct(x, B)))
    thenHave(
      forall(z, in(z, cartesianProduct(x, A)) <=> in(z, cartesianProduct(x, B)))
    ) by Tautology
    val ss1 = thenHave(
      (in(pair(a, b), cartesianProduct(x, A)) <=> in(pair(a, b), cartesianProduct(x, B)))
    ) by InstantiateForall(pair(a, b))

    val ss2 = have((in(pair(a, b), cartesianProduct(x, A)) <=> in(a, x) /\ in(b, A))) by Tautology.from(pairInCartesianProduct of (y -> A))
    val ss3 = have((in(pair(a, b), cartesianProduct(x, B)) <=> in(a, x) /\ in(b, B))) by Tautology.from(pairInCartesianProduct of (y -> B))

    have(
      in(a, x) /\ in(b, A) <=> in(a, x) /\ in(b, B)
    ) by Tautology.from(ss1, ss2, ss3)
    have(
      in(b, A) <=> in(b, B)
    ) by Tautology.from(lastStep, iffElimination of (p -> in(a, x), P -> lambda(X, in(b, X)), x -> A, y -> B))
    thenHave(forall(b, in(b, A) <=> in(b, B))) by RightForall
    have(A === B) by Tautology.from(lastStep, extensionalityAxiom of (x -> A, y -> B))
  }

  // Rovelli Gianmaria
  val AC2AC1aux1 = Lemma(
    !in(emptySet, A) ==> !in(emptySet, cartesianProductWithIdentity(A))
  ) {
    assume(!in(emptySet, A))

    // towards contradiction
    assume(in(emptySet, cartesianProductWithIdentity(A)))
    have(forall(t, in(t, cartesianProductWithIdentity(A)) <=> exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b)))))) by InstantiateForall(cartesianProductWithIdentity(A))(
      cartesianProductWithIdentity.definition
    )
    thenHave(in(emptySet, cartesianProductWithIdentity(A)) <=> exists(b, in(b, A) /\ (emptySet === cartesianProduct(b, singleton(b))))) by InstantiateForall(emptySet)
    val s1 = thenHave(exists(b, in(b, A) /\ (emptySet === cartesianProduct(b, singleton(b))))) by Tautology
    val s2 = have(
      ()
        |- (cartesianProduct(b, emptySet) === emptySet) /\ (cartesianProduct(emptySet, b) === emptySet)
    ) by Tautology.from(productWithEmptySetEmpty of (x -> b))

    have(
      in(b, A) /\ (emptySet === cartesianProduct(b, singleton(b))) |-
        !in(emptySet, cartesianProductWithIdentity(A))
    ) subproof {
      assume(in(b, A))
      val s = assume(emptySet === cartesianProduct(b, singleton(b)))

      val ss1 = have(
        (cartesianProduct(b, emptySet) === emptySet) /\ (cartesianProduct(emptySet, b) === emptySet)
      ) by Tautology.from(s2)
      val ss2 = thenHave(
        (cartesianProduct(b, emptySet) === cartesianProduct(b, singleton(b))) /\ (cartesianProduct(emptySet, b) === emptySet)
      ) by Substitution.ApplyRules(s)
      val ss3 = have(cartesianProduct(emptySet, b) === emptySet) by Tautology.from(ss2)
      val ss4 = have((cartesianProduct(b, emptySet) === cartesianProduct(b, singleton(b)))) by Tautology.from(ss2)
      have(emptySet === singleton(b)) by Tautology.from(lastStep, cartesianProductEquality of (x -> b, A -> emptySet, B -> singleton(b)))

      have(in(b, A) /\ (emptySet === cartesianProduct(b, singleton(b))) |- ()) by Tautology.from(lastStep, singletonNonEmpty of (x -> b))
      thenHave(
        in(b, A) /\ (emptySet === cartesianProduct(b, singleton(b))) |-
          !in(emptySet, cartesianProductWithIdentity(A))
      ) by Weakening
    }
    thenHave(
      exists(b, in(b, A) /\ (emptySet === cartesianProduct(b, singleton(b)))) |-
        !in(emptySet, cartesianProductWithIdentity(A))
    ) by LeftExists

    have(thesis) by Tautology.from(lastStep, s1)
  }

  // Rovelli Gianmaria
  val AC2AC1aux2TheUniqueness = Theorem(
    existsOne(y, (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)))
  ) {
    sorry
  }
  val AC2AC1aux2The = DEF(X, C) --> The(y, (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)))(AC2AC1aux2TheUniqueness)

  // Rovelli Gianmaria
  // the iff version holds too
  val singletonIsIntersection = Lemma(
    setIntersection(A, B) === singleton(x) |- in(x, setIntersection(A, B))
  ) {
    assume(setIntersection(A, B) === singleton(x))
    have((subset(setIntersection(A, B), singleton(x)) /\ subset(singleton(x), setIntersection(A, B)))) by Tautology.from(subsetEqualitySymmetry of (x -> setIntersection(A, B), y -> singleton(x)))
    thenHave(subset(singleton(x), setIntersection(A, B))) by Tautology
    have(forall(z, in(z, singleton(x)) ==> in(z, setIntersection(A, B)))) by Tautology.from(lastStep, subsetAxiom of (x -> singleton(x), y -> setIntersection(A, B)))
    val s1 = thenHave(in(x, singleton(x)) ==> in(x, setIntersection(A, B))) by InstantiateForall(x)

    have(in(x, singleton(x))) by Tautology.from(singletonHasNoExtraElements of (y -> x))
    have(in(x, setIntersection(A, B))) by Tautology.from(lastStep, s1)
  }

  // Rovelli Gianmaria
  val AC2AC1aux2 = Lemma(
    (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)) /\ in(X, A)
      |- in(AC2AC1aux2The(X, C), cartesianProduct(X, A))
  ) {
    assume((setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)))
    assume(in(X, A))

    have(
      (AC2AC1aux2The(X, C) === y)
        <=> (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y))
    ) by InstantiateForall(y)(AC2AC1aux2The.definition)
    val subs = thenHave((AC2AC1aux2The(X, C) === y)) by Tautology

    have(in(y, setIntersection(cartesianProduct(X, singleton(X)), C))) by Tautology.from(singletonIsIntersection of (A -> cartesianProduct(X, singleton(X)), B -> C, x -> y))
    have(in(y, cartesianProduct(X, singleton(X))) /\ in(y, C)) by Tautology.from(lastStep, setIntersectionMembership of (t -> y, x -> cartesianProduct(X, singleton(X)), y -> C))
    val s1 = thenHave(in(y, cartesianProduct(X, singleton(X)))) by Tautology

    have(
      forall(
        t,
        in(t, cartesianProduct(X, singleton(X)))
          <=> ((in(t, powerSet(powerSet(setUnion(X, singleton(X)))))) /\ (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, X) /\ in(b, singleton(X))))))
      )
    ) by InstantiateForall(cartesianProduct(X, singleton(X)))(cartesianProduct.definition of (x -> X, y -> singleton(X)))
    thenHave(
      in(y, cartesianProduct(X, singleton(X)))
        <=> ((in(y, powerSet(powerSet(setUnion(X, singleton(X)))))) /\ (∃(a, ∃(b, (y === pair(a, b)) /\ in(a, X) /\ in(b, singleton(X))))))
    ) by InstantiateForall(y)
    have(
      ((in(y, powerSet(powerSet(setUnion(X, singleton(X)))))) /\ (∃(a, ∃(b, (y === pair(a, b)) /\ in(a, X) /\ in(b, singleton(X))))))
    ) by Tautology.from(lastStep, s1)
    val s2 = thenHave((∃(a, ∃(b, (y === pair(a, b)) /\ in(a, X) /\ in(b, singleton(X)))))) by Tautology

    val s3 = have((y === pair(a, b)) /\ in(a, X) /\ in(b, singleton(X)) |- in(y, cartesianProduct(X, A))) subproof {
      val subs = assume((y === pair(a, b)))
      assume(in(a, X))
      assume(in(b, singleton(X)))
      val s1 = have(b === X) by Tautology.from(singletonHasNoExtraElements of (x -> X, y -> b))
      have(in(X, A)) by Hypothesis
      val s2 = thenHave(in(b, A)) by Substitution.ApplyRules(s1)
      have(in(pair(a, b), cartesianProduct(X, A))) by Tautology.from(s2, pairInCartesianProduct of (x -> X, y -> A))
      thenHave(in(y, cartesianProduct(X, A))) by Substitution.ApplyRules(subs)
    }

    thenHave(∃(b, (y === pair(a, b)) /\ in(a, X) /\ in(b, singleton(X))) |- in(y, cartesianProduct(X, A))) by LeftExists
    thenHave(∃(a, ∃(b, (y === pair(a, b)) /\ in(a, X) /\ in(b, singleton(X)))) |- in(y, cartesianProduct(X, A))) by LeftExists
    have(in(y, cartesianProduct(X, A))) by Tautology.from(lastStep, s2)
    thenHave(in(AC2AC1aux2The(X, C), cartesianProduct(X, A))) by Substitution.ApplyRules(subs)
  }

  val firstElementOfAC2AC1aux2TheUniqueness = Theorem(
    ∃!(g, ∀(t, in(t, g) <=> exists(x, in(x, A) /\ (t === firstInPair(AC2AC1aux2The(x, C))))))
  ) {
    sorry
  }
  val firstElementOfAC2AC1aux2The = DEF(A, C) -->
    The(g, ∀(t, in(t, g) <=> exists(x, in(x, A) /\ (t === firstInPair(AC2AC1aux2The(x, C))))))(firstElementOfAC2AC1aux2TheUniqueness)

  // val AC2AC1aux2The = DEF(X, C) --> The(y, (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)))(AC2AC1aux2TheUniqueness)
  // Rovelli Gianmaria
  val AC2AC1aux3 = Lemma(
    forall(D, in(D, cartesianProductWithIdentity(A)) ==> exists(y, setIntersection(D, C) === singleton(y)))
      ==> in(firstElementOfAC2AC1aux2The(A, C), Pi(A, identityFunction(A)))
  ) {
    assume(forall(D, in(D, cartesianProductWithIdentity(A)) ==> exists(y, setIntersection(D, C) === singleton(y))))

    val sub1 = have(functional(firstElementOfAC2AC1aux2The(A, C))) subproof {
      sorry
    }

    val sub2 = have(in(firstElementOfAC2AC1aux2The(A, C), powerSet(Sigma(A, identityFunction(A))))) subproof {
      sorry
    }

    val sub3 = have(subset(A, relationDomain(firstElementOfAC2AC1aux2The(A, C)))) subproof {
      sorry
    }

    sorry
  }

  // Rovelli Gianmaria
  val AC2AC1 = Lemma(
    forall(
      A,
      !in(emptySet, A) /\ pairwiseDisjoint(A)
        ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
    )
      ==>
        forall(A, !in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A))))))
  ) {
    assume(
      forall(
        A,
        !in(emptySet, A) /\ pairwiseDisjoint(A)
          ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
      )
    )
    thenHave(
      !in(emptySet, A) /\ pairwiseDisjoint(A)
        ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
    ) by InstantiateForall(A)

    val sub1 = have(!in(emptySet, A) ==> exists(f, in(f, Pi(A, identityFunction(A))))) subproof {
      assume(!in(emptySet, A))
      sorry
    }

    have(forall(A, !in(emptySet, A) ==> exists(f, in(f, Pi(A, identityFunction(A)))))) by RightForall(sub1)
  }

  // Well-Ordered Theorem

  // val wf = DEF(r) --> {
  //   forall(z, !(z === emptySet) \/ (exists(x, in(x, Z) /\ forall(y, in(pair(y, x), r) ==> !in(y, Z)))))
  // }
  //
  // val wf_on = DEF(A, r) --> wf(setIntersection(r, cartesianProduct(A, A)))
  //
  // val wellOrder2 = DEF(A, r) --> {
  //   totalOrder(r) /\ wf_on(A, r)
  // }

  val equiPollent = DEF(A, B) --> exists(f, bijective(f, A, B))

  val equiPollentReflexivity = Lemma(equiPollent(x, x)) {
    sorry
  }

  val WO2WO3 = Lemma(
    forall(A, exists(a, ordinal(a) /\ equiPollent(A, a)))
      ==>
        forall(A, exists(a, ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b))))
  ) {
    have(ordinal(a) /\ equiPollent(A, a) |- subset(a, a) /\ equiPollent(A, a)) by Tautology.from(subsetReflexivity of (x -> a))
    thenHave(ordinal(a) /\ equiPollent(A, a) |- exists(b, subset(b, a) /\ equiPollent(A, b))) by RightExists
    thenHave(ordinal(a) /\ equiPollent(A, a) |- ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b))) by Tautology
    thenHave(ordinal(a) /\ equiPollent(A, a) |- exists(a, ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b)))) by RightExists
    thenHave(exists(a, ordinal(a) /\ equiPollent(A, a)) |- exists(a, ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b)))) by LeftExists
    thenHave(forall(A, exists(a, ordinal(a) /\ equiPollent(A, a))) |- exists(a, ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b)))) by LeftForall
    thenHave(forall(A, exists(a, ordinal(a) /\ equiPollent(A, a))) |- forall(A, exists(a, ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b))))) by RightForall
    thenHave(
      forall(A, exists(a, ordinal(a) /\ equiPollent(A, a)))
        ==> forall(A, exists(a, ordinal(a) /\ exists(b, subset(b, a) /\ equiPollent(A, b))))
    ) by Tautology
  }

  val WO1WO3 = Lemma(
    forall(A, exists(R, in(R, A) /\ wellOrder(R)))
      ==>
        forall(A, exists(a, ordinal(a) /\ equiPollent(A, a)))
  ) {
    assume(forall(A, exists(R, in(R, A) /\ wellOrder(R))))
    // val wellOrder = DEF(p) --> {
    //   val A = firstInPair(p)
    //   val B = variable
    //   val `<p` = secondInPair(p)
    //   totalOrder(p) /\ forall(B, (subset(B, A) /\ !(B === emptySet)) ==> exists(z, in(z, B) /\ forall(x, in(x, B) ==> (in(pair(z, x), `<p`) \/ (z === x)))))
    // }

    // val equiPollent = DEF(A, B) --> exists(f, bijective(f, A, B))

    // val elementsOfOrdinalsAreOrdinals = Theorem(
    //   (ordinal(a), in(b, a)) |- ordinal(b)
    sorry
  }
}
