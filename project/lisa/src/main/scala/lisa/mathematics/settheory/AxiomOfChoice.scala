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
import lisa.mathematics.settheory.SetTheory.setWithNoElementsIsEmpty
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
  private val e = variable
  private val f = variable
  private val g = variable
  private val p = formulaVariable
  private val q = formulaVariable
  private val r = variable
  private val t = variable
  private val w = variable
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

  // Rovelli Gianmaria
  val domainType = Lemma(in(pair(a, b), f) /\ in(f, Pi(A, B)) |- in(a, A)) {
    assume(in(pair(a, b), f))
    assume(in(f, Pi(A, B)))

    // val subs = have(Sigma(A, B) === restrictedFunction(B, A)) by InstantiateForall(Sigma(A, B))(Sigma.definition of (x -> A, f -> B))

    have(subset(f, Sigma(A, B))) by Tautology.from(funIsRel)
    have(forall(z, in(z, f) ==> in(z, Sigma(A, B)))) by Tautology.from(lastStep, subsetAxiom of (x -> f, y -> Sigma(A, B)))
    thenHave(in(pair(a, b), f) ==> in(pair(a, b), Sigma(A, B))) by InstantiateForall(pair(a, b))
    val s1 = thenHave(in(pair(a, b), Sigma(A, B))) by Tautology

    have(forall(t, in(t, Sigma(A, B)) <=> ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a)))))) by InstantiateForall(
      Sigma(A, B)
    )(Sigma.definition of (f -> B, x -> A))
    thenHave(in(pair(a, b), Sigma(A, B)) <=> ∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ in(c, A) /\ in(d, app(B, c))))) by InstantiateForall(pair(a, b))
    val sigmaDef = have(∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ in(c, A) /\ in(d, app(B, c))))) by Tautology.from(s1, lastStep)

    val subs = have((pair(a, b) === pair(c, d)) /\ in(c, A) /\ in(d, app(B, c)) |- (a === c)) by Tautology.from(pairExtensionality)
    have((pair(a, b) === pair(c, d)) /\ in(c, A) /\ in(d, app(B, c)) |- in(c, A)) by Tautology.from(pairExtensionality)
    thenHave((pair(a, b) === pair(c, d)) /\ in(c, A) /\ in(d, app(B, c)) |- in(a, A)) by Substitution.ApplyRules(subs)
    thenHave(exists(d, (pair(a, b) === pair(c, d)) /\ in(c, A) /\ in(d, app(B, c))) |- in(a, A)) by LeftExists
    thenHave(exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, A) /\ in(d, app(B, c)))) |- in(a, A)) by LeftExists
    have(in(a, A)) by Tautology.from(sigmaDef, lastStep)
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
  val singletonEqualityImpliesInclusion = Lemma((A === singleton(y)) |- in(y, A)) {
    assume(A === singleton(y))

    have(forall(z, in(z, A) <=> in(z, singleton(y))) <=> (A === singleton(y))) by Tautology.from(extensionalityAxiom of (x -> A, y -> singleton(y)))
    thenHave(forall(z, in(z, A) <=> in(z, singleton(y)))) by Tautology
    thenHave(in(y, A) <=> in(y, singleton(y))) by InstantiateForall(y)
    have(in(y, A) <=> (y === y)) by Tautology.from(lastStep, singletonHasNoExtraElements of (y -> y, x -> y))
    thenHave(in(y, A)) by Tautology
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
  val applyPair = Lemma(
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

      have(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(pair(B, app(f, B)), f)) by Tautology.from(applyPair of (A -> A, B -> identityFunction(A), a -> B, f -> f))
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

  val cartesianProductWithIdentityUniqueness = Theorem(
    existsOne(g, forall(t, in(t, g) <=> in(t, powerSet(cartesianProduct(union(A), A))) /\ (exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b)))))))
  ) {
    have(thesis) by UniqueComprehension(
      powerSet(cartesianProduct(union(A), A)),
      lambda((t, c), (exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b))))))
    )
  }

  // all elements like {B*{B}. B ∈ A}
  val cartesianProductWithIdentity = DEF(A) -->
    The(g, forall(t, in(t, g) <=> in(t, powerSet(cartesianProduct(union(A), A))) /\ (exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b)))))))(cartesianProductWithIdentityUniqueness)

  // Rovelli Gianmaria
  val elementInNonEmptySet = Lemma(!(x === emptySet) |- exists(y, in(y, x))) {
    have(forall(y, !in(y, x)) |- (x === emptySet)) by Tautology.from(setWithNoElementsIsEmpty)
    thenHave(!(x === emptySet) |- !forall(y, !in(y, x))) by Tautology
    thenHave(!(x === emptySet) |- exists(y, in(y, x))) by Tautology
  }

  // Rovelli Gianmaria
  val elementInNonEmptySetIsNotEmptySet = Lemma(!in(emptySet, A) /\ in(b, A) |- !(b === emptySet)) {
    val subs = assume(b === emptySet)
    thenHave(!in(emptySet, A) /\ in(b, A) |- in(b, A)) by Restate
    thenHave(!in(emptySet, A) /\ in(b, A) |- in(emptySet, A)) by Substitution.ApplyRules(subs)
    thenHave(!in(emptySet, A) /\ in(b, A) |- ()) by Tautology
    thenHave(!in(emptySet, A) /\ in(b, A) |- !(b === emptySet)) by Weakening
  }

  // Rovelli Gianmaria
  val cartesianProductEquality = Lemma(
    (!(x === emptySet) /\ (cartesianProduct(x, A) === cartesianProduct(x, B))) ==> (A === B)
  ) {
    assume(cartesianProduct(x, A) === cartesianProduct(x, B))
    assume(!(x === emptySet))
    have(
      forall(z, in(z, cartesianProduct(x, A)) <=> in(z, cartesianProduct(x, B)))
        <=> (cartesianProduct(x, A) === cartesianProduct(x, B))
    ) by Tautology.from(extensionalityAxiom of (x -> cartesianProduct(x, A), y -> cartesianProduct(x, B)))
    thenHave(
      forall(z, in(z, cartesianProduct(x, A)) <=> in(z, cartesianProduct(x, B)))
    ) by Tautology
    val ss1 = thenHave(
      (in(pair(a, t), cartesianProduct(x, A)) <=> in(pair(a, t), cartesianProduct(x, B)))
    ) by InstantiateForall(pair(a, t))

    val fwd = have(in(t, A) ==> in(t, B)) subproof {
      assume(in(t, A))
      val ex = have(exists(a, in(a, x))) by Tautology.from(elementInNonEmptySet)
      have(in(a, x) |- in(pair(a, t), cartesianProduct(x, A))) by Tautology.from(pairInCartesianProduct of (b -> t, y -> A))
      have(in(a, x) |- in(pair(a, t), cartesianProduct(x, B))) by Tautology.from(lastStep, ss1)
      have(in(a, x) |- in(a, x) /\ in(t, B)) by Tautology.from(lastStep, pairInCartesianProduct of (b -> t, y -> B))
      thenHave(in(a, x) |- in(t, B)) by Tautology
      thenHave(exists(a, in(a, x)) |- in(t, B)) by LeftExists
      have(in(t, B)) by Tautology.from(lastStep, ex)
    }
    val bwd = have(in(t, B) ==> in(t, A)) subproof {
      assume(in(t, B))
      val ex = have(exists(a, in(a, x))) by Tautology.from(elementInNonEmptySet)
      have(in(a, x) |- in(pair(a, t), cartesianProduct(x, B))) by Tautology.from(pairInCartesianProduct of (b -> t, y -> B))
      have(in(a, x) |- in(pair(a, t), cartesianProduct(x, A))) by Tautology.from(lastStep, ss1)
      have(in(a, x) |- in(a, x) /\ in(t, A)) by Tautology.from(lastStep, pairInCartesianProduct of (b -> t, y -> A))
      thenHave(in(a, x) |- in(t, A)) by Tautology
      thenHave(exists(a, in(a, x)) |- in(t, A)) by LeftExists
      have(in(t, A)) by Tautology.from(lastStep, ex)
    }
    have(in(t, A) <=> in(t, B)) by Tautology.from(fwd, bwd)
    thenHave(forall(t, in(t, A) <=> in(t, B))) by RightForall

    have(
      (A === B)
    ) by Tautology.from(lastStep, extensionalityAxiom of (x -> A, y -> B))
  }

  // Rovelli Gianmaria
  val AC2AC1aux1 = Lemma(
    !in(emptySet, A) ==> !in(emptySet, cartesianProductWithIdentity(A))
  ) {
    assume(!in(emptySet, A))

    // towards contradiction
    assume(in(emptySet, cartesianProductWithIdentity(A)))
    have(forall(t, in(t, cartesianProductWithIdentity(A)) <=> in(t, powerSet(cartesianProduct(union(A), A))) /\ exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b)))))) by InstantiateForall(
      cartesianProductWithIdentity(A)
    )(
      cartesianProductWithIdentity.definition
    )
    thenHave(
      in(emptySet, cartesianProductWithIdentity(A)) <=> in(emptySet, powerSet(cartesianProduct(union(A), A))) /\ exists(b, in(b, A) /\ (emptySet === cartesianProduct(b, singleton(b))))
    ) by InstantiateForall(emptySet)
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

      val bNotEmptySet = have(!(b === emptySet)) by Tautology.from(elementInNonEmptySetIsNotEmptySet)

      val ss1 = have(
        (cartesianProduct(b, emptySet) === emptySet) /\ (cartesianProduct(emptySet, b) === emptySet)
      ) by Tautology.from(s2)
      val ss2 = thenHave(
        (cartesianProduct(b, emptySet) === cartesianProduct(b, singleton(b))) /\ (cartesianProduct(emptySet, b) === emptySet)
      ) by Substitution.ApplyRules(s)
      val ss3 = have(cartesianProduct(emptySet, b) === emptySet) by Tautology.from(ss2)
      val ss4 = have((cartesianProduct(b, emptySet) === cartesianProduct(b, singleton(b)))) by Tautology.from(ss2)
      have(emptySet === singleton(b)) by Tautology.from(lastStep, bNotEmptySet, cartesianProductEquality of (x -> b, A -> emptySet, B -> singleton(b)))

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
  // the iff version should hold too
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
  val AC2AC1aux2TheUniqueness = Theorem(
    existsOne(y, in(y, cartesianProduct(X, singleton(X))) /\ (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)))
  ) {
    sorry
  }
  val AC2AC1aux2The = DEF(X, C) --> The(y, in(y, cartesianProduct(X, singleton(X))) /\ (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)))(AC2AC1aux2TheUniqueness)

  // Rovelli Gianmaria
  val AC2AC1aux2 = Lemma(
    (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y)) /\ in(X, A)
      |- in(AC2AC1aux2The(X, C), cartesianProduct(X, A))
  ) {
    val intt = setIntersection(cartesianProduct(X, singleton(X)), C)
    assume((intt) === singleton(y))
    assume(in(X, A))

    val inCart = have(in(y, cartesianProduct(X, singleton(X)))) subproof {
      have(forall(z, in(z, intt) <=> in(z, singleton(y))) <=> (intt === singleton(y))) by Tautology.from(extensionalityAxiom of (x -> intt, y -> singleton(y)))
      thenHave(forall(z, in(z, intt) <=> in(z, singleton(y)))) by Tautology
      thenHave(in(z, intt) <=> in(z, singleton(y))) by InstantiateForall(z)
      have(in(z, intt) <=> (y === z)) by Tautology.from(lastStep, singletonHasNoExtraElements of (y -> z, x -> y))
      have(in(y, intt)) by Tautology.from(singletonEqualityImpliesInclusion of (A -> intt))
      have((in(y, cartesianProduct(X, singleton(X))) /\ in(y, C))) by Tautology.from(lastStep, setIntersectionMembership of (t -> y, x -> cartesianProduct(X, singleton(X)), y -> C))
      thenHave(in(y, cartesianProduct(X, singleton(X)))) by Tautology
    }

    have(
      (AC2AC1aux2The(X, C) === y)
        <=> in(y, cartesianProduct(X, singleton(X))) /\ (setIntersection(cartesianProduct(X, singleton(X)), C) === singleton(y))
    ) by InstantiateForall(y)(AC2AC1aux2The.definition)
    val subs = have((AC2AC1aux2The(X, C) === y)) by Tautology.from(lastStep, inCart)

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

  // Rovelli Gianmaria
  val firstElementOfAC2AC1aux2TheUniqueness = Theorem(
    ∃!(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(A, union(A))) /\ exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
  ) {
    have(thesis) by UniqueComprehension(
      cartesianProduct(A, union(A)),
      lambda((t, b), exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C))))))
    )
  }
  val firstElementOfAC2AC1aux2The = DEF(A, C) -->
    The(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(A, union(A))) /\ exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))(firstElementOfAC2AC1aux2TheUniqueness)

  // Rovelli Gianmaria
  val firstInPairOfAC2AC1aux2The = Lemma(in(t, A) |- in(firstInPair(AC2AC1aux2The(t, C)), t)) {
    assume(in(t, A))
    have(
      forall(
        d,
        in(d, cartesianProduct(t, singleton(t)))
          <=> ((in(d, powerSet(powerSet(setUnion(t, singleton(t)))))) /\ (∃(a, ∃(b, (d === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t))))))
      )
    ) by InstantiateForall(cartesianProduct(t, singleton(t)))(cartesianProduct.definition of (x -> t, y -> singleton(t)))
    val cartDef = thenHave(
      in(AC2AC1aux2The(t, C), cartesianProduct(t, singleton(t)))
        <=> ((in(AC2AC1aux2The(t, C), powerSet(powerSet(setUnion(t, singleton(t)))))) /\ (∃(a, ∃(b, (AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t))))))
    ) by InstantiateForall(AC2AC1aux2The(t, C))

    have(
      (AC2AC1aux2The(t, C) === AC2AC1aux2The(t, C))
        <=>
          in(AC2AC1aux2The(t, C), cartesianProduct(t, singleton(t))) /\ (setIntersection(cartesianProduct(t, singleton(t)), C) === singleton(AC2AC1aux2The(t, C)))
    ) by InstantiateForall(AC2AC1aux2The(t, C))(AC2AC1aux2The.definition of (X -> t))
    thenHave(
      in(AC2AC1aux2The(t, C), cartesianProduct(t, singleton(t)))
    ) by Tautology
    have((in(AC2AC1aux2The(t, C), powerSet(powerSet(setUnion(t, singleton(t)))))) /\ (∃(a, ∃(b, (AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t)))))) by Tautology.from(
      lastStep,
      cartDef
    )
    val ex = thenHave(∃(a, ∃(b, (AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t))))) by Tautology

    val subs = have((AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t)) |- (AC2AC1aux2The(t, C) === pair(a, b))) by Restate

    have((AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t)) |- firstInPair(pair(a, b)) === a) by Tautology.from(firstInPairReduction of (x -> a, y -> b))
    val subs2 = thenHave((AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t)) |- firstInPair(AC2AC1aux2The(t, C)) === a) by Substitution.ApplyRules(subs)

    have((AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t)) |- in(a, t)) by Restate
    thenHave((AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t)) |- in(firstInPair(AC2AC1aux2The(t, C)), t)) by Substitution.ApplyRules(subs2)
    thenHave(exists(b, (AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t))) |- in(firstInPair(AC2AC1aux2The(t, C)), t)) by LeftExists
    thenHave(exists(a, exists(b, (AC2AC1aux2The(t, C) === pair(a, b)) /\ in(a, t) /\ in(b, singleton(t)))) |- in(firstInPair(AC2AC1aux2The(t, C)), t)) by LeftExists
    have(in(firstInPair(AC2AC1aux2The(t, C)), t)) by Tautology.from(lastStep, ex)
  }

  // Rovelli Gianmaria
  val domainOfFirstElementOfAC2AC1aux2TheFunction = Lemma(relationDomain(firstElementOfAC2AC1aux2The(A, C)) === A) {
    val fe = firstElementOfAC2AC1aux2The(A, C)
    val fwd = have(in(t, relationDomain(fe)) ==> in(t, A)) subproof {
      assume(in(t, relationDomain(fe)))
      have(forall(t, in(t, relationDomain(fe)) <=> exists(a, in(pair(t, a), fe)))) by InstantiateForall(relationDomain(fe))(
        relationDomain.definition of (r -> fe)
      )
      val relDomDef = thenHave(in(t, relationDomain(fe)) <=> exists(a, in(pair(t, a), fe))) by InstantiateForall(t)
      val ex = thenHave(exists(a, in(pair(t, a), fe))) by Tautology

      have(
        forall(t, in(t, fe) <=> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
      ) by InstantiateForall(fe)(firstElementOfAC2AC1aux2The.definition)
      thenHave(
        in(pair(t, a), fe) <=> in(pair(t, a), cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (pair(t, a) === pair(x, firstInPair(AC2AC1aux2The(x, C))))))
      ) by InstantiateForall(pair(t, a))
      thenHave(
        in(pair(t, a), fe) |- in(pair(t, a), cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (pair(t, a) === pair(x, firstInPair(AC2AC1aux2The(x, C))))))
      ) by Tautology
      thenHave(
        in(pair(t, a), fe) |- in(pair(t, a), cartesianProduct(A, union(A)))
      ) by Tautology
      have(in(pair(t, a), fe) |- in(t, A)) by Tautology.from(lastStep, pairInCartesianProduct of (a -> t, b -> a, x -> A, y -> union(A)))
      thenHave(exists(a, in(pair(t, a), fe)) |- in(t, A)) by LeftExists
      have(in(t, A)) by Tautology.from(lastStep, ex)
    }

    val bwd = have(in(t, A) ==> in(t, relationDomain(fe))) subproof {
      assume(in(t, A))

      have(forall(t, in(t, relationDomain(fe)) <=> exists(a, in(pair(t, a), fe)))) by InstantiateForall(relationDomain(fe))(
        relationDomain.definition of (r -> fe)
      )
      val relDomDef = thenHave(in(t, relationDomain(fe)) <=> exists(a, in(pair(t, a), fe))) by InstantiateForall(t)

      have(
        forall(t, in(t, fe) <=> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
      ) by InstantiateForall(fe)(firstElementOfAC2AC1aux2The.definition)
      val feDef = thenHave(
        in(pair(t, firstInPair(AC2AC1aux2The(t, C))), fe)
          <=> in(pair(t, firstInPair(AC2AC1aux2The(t, C))), cartesianProduct(A, union(A)))
          /\ (exists(x, in(x, A) /\ (pair(t, firstInPair(AC2AC1aux2The(t, C))) === pair(x, firstInPair(AC2AC1aux2The(x, C))))))
      ) by InstantiateForall(pair(t, firstInPair(AC2AC1aux2The(t, C))))

      // i need
      //  in(pair(t, a), cartesianProduct(A, union(A)))
      //  (exists(x, in(x, A) /\ (pair(t, a) === pair(x, firstInPair(AC2AC1aux2The(x, C)))
      //
      // i already have in(t, A)
      //
      // i need to prove that
      //  in(firstInPair(AC2AC1aux2The(t, C)), union(A))
      // so that
      //  exists(y, in(y, A) /\ in(firstInPair(AC2AC1aux2The(t, C)), y))
      // but i know that
      //  in(t, A)
      // so i need
      //  in(firstInPair(AC2AC1aux2The(t, C)), t)

      have(in(t, A) |- in(t, A) /\ in(firstInPair(AC2AC1aux2The(t, C)), t)) by Tautology.from(firstInPairOfAC2AC1aux2The)
      val ex = thenHave(in(t, A) |- exists(y, in(y, A) /\ in(firstInPair(AC2AC1aux2The(t, C)), y))) by RightExists
      have(in(t, A) |- in(firstInPair(AC2AC1aux2The(t, C)), union(A))) by Tautology.from(lastStep, unionAxiom of (x -> A, z -> firstInPair(AC2AC1aux2The(t, C))))
      val s1 = thenHave(in(firstInPair(AC2AC1aux2The(t, C)), union(A))) by Tautology

      val inCart = have(in(t, A) |- in(pair(t, firstInPair(AC2AC1aux2The(t, C))), cartesianProduct(A, union(A)))) by Tautology.from(
        s1,
        pairInCartesianProduct of (a -> t, b -> firstInPair(AC2AC1aux2The(t, C)), x -> A, y -> union(A))
      )

      have(in(t, A) |- in(t, A) /\ (pair(t, firstInPair(AC2AC1aux2The(t, C))) === pair(t, firstInPair(AC2AC1aux2The(t, C))))) by Restate
      val exf = thenHave(in(t, A) |- exists(x, in(x, A) /\ (pair(t, firstInPair(AC2AC1aux2The(t, C))) === pair(x, firstInPair(AC2AC1aux2The(x, C)))))) by RightExists
      have(in(pair(t, firstInPair(AC2AC1aux2The(t, C))), fe)) by Tautology.from(exf, inCart, feDef)
      thenHave(exists(a, in(pair(t, a), fe))) by RightExists

      have(in(t, relationDomain(fe))) by Tautology.from(lastStep, relDomDef)
    }

    have(in(t, relationDomain(fe)) <=> in(t, A)) by Tautology.from(fwd, bwd)
    thenHave(forall(t, in(t, relationDomain(fe)) <=> in(t, A))) by RightForall
    have(relationDomain(fe) === A) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationDomain(fe), y -> A))
  }

  // Rovelli Gianmaria
  val AC2AC1aux3 = Lemma(
    forall(D, in(D, cartesianProductWithIdentity(A)) ==> exists(y, setIntersection(D, C) === singleton(y)))
      ==> in(firstElementOfAC2AC1aux2The(A, C), Pi(A, identityFunction(A)))
  ) {
    assume(forall(D, in(D, cartesianProductWithIdentity(A)) ==> exists(y, setIntersection(D, C) === singleton(y))))

    val fe = firstElementOfAC2AC1aux2The(A, C)
    val sub1 = have(functional(fe)) subproof {

      val rel = have(relation(fe)) subproof {
        have(
          forall(t, in(t, fe) <=> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
        ) by InstantiateForall(fe)(firstElementOfAC2AC1aux2The.definition)
        thenHave(
          forall(t, in(t, fe) ==> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
        ) by Tautology
        thenHave(
          forall(t, in(t, fe) ==> in(t, cartesianProduct(A, union(A))))
        ) by Tautology
        have(relationBetween(fe, A, union(A))) by Tautology.from(
          lastStep,
          subsetAxiom of (x -> fe, y -> cartesianProduct(A, union(A))),
          relationBetween.definition of (r -> fe, a -> A, b -> union(A))
        )
        thenHave(exists(b, relationBetween(fe, A, b))) by RightExists
        thenHave(exists(a, exists(b, relationBetween(fe, a, b)))) by RightExists
        have(thesis) by Tautology.from(lastStep, relation.definition of r -> fe)
      }
      val uniq = have(forall(a, exists(b, in(pair(a, b), fe)) ==> existsOne(b, in(pair(a, b), fe)))) subproof {
        have(in(pair(a, b), fe) |- in(pair(a, b), fe)) by Tautology
        thenHave((in(pair(a, b), fe), (z === b)) |- in(pair(a, z), fe)) by RightSubstEq.withParameters(List((z, b)), lambda(z, in(pair(a, z), fe)))
        val dir1 = thenHave(in(pair(a, b), fe) |- (z === b) ==> in(pair(a, z), fe)) by Tautology

        val dir2 = have(in(pair(a, b), fe) /\ in(pair(a, z), fe) |- (z === b)) subproof {
          assume(in(pair(a, b), fe))
          assume(in(pair(a, z), fe))

          have(
            forall(t, in(t, fe) <=> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
          ) by InstantiateForall(fe)(firstElementOfAC2AC1aux2The.definition)
          val ex1 = thenHave(
            (exists(x, in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C))))))
          ) by InstantiateForall(pair(a, b))
          have(
            forall(t, in(t, fe) <=> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
          ) by InstantiateForall(fe)(firstElementOfAC2AC1aux2The.definition)
          val ex2 = thenHave(
            (exists(x, in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C))))))
          ) by InstantiateForall(pair(a, z))

          val eq1 = have(
            in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (a === x) /\ (b === firstInPair(AC2AC1aux2The(x, C)))
          ) by Tautology.from(
            pairExtensionality of (c -> x, d -> firstInPair(AC2AC1aux2The(x, C)))
          )
          val subs1 = have(
            in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (a === x)
          ) by Tautology.from(
            pairExtensionality of (c -> x, d -> firstInPair(AC2AC1aux2The(x, C)))
          )
          have(
            in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (b === firstInPair(AC2AC1aux2The(x, C)))
          ) by Tautology.from(eq1)
          thenHave(
            in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (b === firstInPair(AC2AC1aux2The(a, C)))
          ) by Substitution.ApplyRules(subs1)
          val s1 = thenHave(
            exists(x, in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C)))))
              |- (b === firstInPair(AC2AC1aux2The(a, C)))
          ) by LeftExists

          val eq2 = have(
            in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (a === x) /\ (z === firstInPair(AC2AC1aux2The(x, C)))
          ) by Tautology.from(
            pairExtensionality of (b -> z, c -> x, d -> firstInPair(AC2AC1aux2The(x, C)))
          )
          val subs2 = have(
            in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (a === x)
          ) by Tautology.from(
            pairExtensionality of (b -> z, c -> x, d -> firstInPair(AC2AC1aux2The(x, C)))
          )
          have(
            in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (z === firstInPair(AC2AC1aux2The(x, C)))
          ) by Tautology.from(eq2)
          thenHave(
            in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- (z === firstInPair(AC2AC1aux2The(a, C)))
          ) by Substitution.ApplyRules(subs2)
          val s2 = thenHave(
            exists(x, in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C)))))
              |- (z === firstInPair(AC2AC1aux2The(a, C)))
          ) by LeftExists

          have(
            exists(x, in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C))))) /\
              exists(x, in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C)))))
              |- (z === firstInPair(AC2AC1aux2The(a, C)))
          ) by Tautology.from(s2)
          thenHave(
            exists(x, in(x, A) /\ (pair(a, b) === pair(x, firstInPair(AC2AC1aux2The(x, C))))) /\
              exists(x, in(x, A) /\ (pair(a, z) === pair(x, firstInPair(AC2AC1aux2The(x, C)))))
              |- (z === b)
          ) by Substitution.ApplyRules(s1)

          have(z === b) by Tautology.from(lastStep, ex1, ex2)
        }
        val dir22 = thenHave(in(pair(a, b), fe) |- in(pair(a, z), fe) ==> (z === b)) by Tautology

        val equiv_z = have(in(pair(a, b), fe) |- (z === b) <=> in(pair(a, z), fe)) by Tautology.from(dir1, dir22)
        thenHave(in(pair(a, b), fe) |- forall(z, (z === b) <=> in(pair(a, z), fe))) by RightForall
        thenHave(in(pair(a, b), fe) |- exists(b, forall(z, (z === b) <=> in(pair(a, z), fe)))) by RightExists
        thenHave(in(pair(a, b), fe) |- existsOne(b, in(pair(a, b), fe))) by RightExistsOne
        thenHave(exists(b, in(pair(a, b), fe)) |- existsOne(b, in(pair(a, b), fe))) by LeftExists
        thenHave(exists(b, in(pair(a, b), fe)) ==> existsOne(b, in(pair(a, b), fe))) by Restate
        thenHave(thesis) by RightForall
      }

      have(thesis) by Tautology.from(rel, uniq, functional.definition of f -> fe)
    }

    val sub2 = have(in(fe, powerSet(Sigma(A, identityFunction(A))))) subproof {
      have(in(t, fe) ==> in(t, Sigma(A, identityFunction(A)))) subproof {
        assume(in(t, (fe)))

        have(
          forall(t, in(t, fe) <=> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))))
        ) by InstantiateForall(fe)(firstElementOfAC2AC1aux2The.definition)
        thenHave(in(t, fe) <=> in(t, cartesianProduct(A, union(A))) /\ (exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C))))))) by InstantiateForall(
          t
        )
        val s1 = thenHave(exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))) by Tautology

        val sub1 = have(
          in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C))))
            |- in(firstInPair(AC2AC1aux2The(x, C)), x)
        ) subproof {
          assume(in(x, A))
          assume(t === pair(x, firstInPair(AC2AC1aux2The(x, C))))

          val aux = have(
            (t === pair(x, firstInPair(AC2AC1aux2The(x, C))))
              |- exists(y, (t === pair(x, firstInPair(y))) /\ (AC2AC1aux2The(x, C) === y))
          ) subproof {
            assume(t === pair(x, firstInPair(AC2AC1aux2The(x, C))))
            have((t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) /\ (AC2AC1aux2The(x, C) === AC2AC1aux2The(x, C))) by Restate
            thenHave(exists(y, (t === pair(x, firstInPair(y))) /\ (AC2AC1aux2The(x, C) === y))) by RightExists
          }

          val eq = have(
            exists(y, (t === pair(x, firstInPair(y))) /\ (AC2AC1aux2The(x, C) === y))
          ) by Tautology.from(aux)
          have(
            (AC2AC1aux2The(x, C) === y)
              <=>
                in(y, cartesianProduct(x, singleton(x))) /\ (setIntersection(cartesianProduct(x, singleton(x)), C) === singleton(y))
          ) by InstantiateForall(y)(AC2AC1aux2The.definition of (X -> x))
          val s1 = have((t === pair(x, firstInPair(y))) /\ (AC2AC1aux2The(x, C) === y) |- (setIntersection(cartesianProduct(x, singleton(x)), C) === singleton(y))) by Tautology.from(lastStep)

          val s2 = have((t === pair(x, firstInPair(y))) /\ (AC2AC1aux2The(x, C) === y) |- in(AC2AC1aux2The(x, C), cartesianProduct(x, A))) by Tautology.from(s1, AC2AC1aux2 of (X -> x))
          have((t === pair(x, firstInPair(y))) /\ (AC2AC1aux2The(x, C) === y) |- in(firstInPair(AC2AC1aux2The(x, C)), x)) by Tautology.from(
            lastStep,
            firstInPairType of (x -> AC2AC1aux2The(x, C), A -> x, B -> A)
          )
          thenHave(exists(y, (t === pair(x, firstInPair(y))) /\ (AC2AC1aux2The(x, C) === y)) |- in(firstInPair(AC2AC1aux2The(x, C)), x)) by LeftExists
          have(in(firstInPair(AC2AC1aux2The(x, C)), x)) by Tautology.from(lastStep, aux)
        }

        val subs = have(in(x, A) |- app(identityFunction(A), x) === x) by Tautology.from(functionalApplicationOfIdentity of (B -> x))

        have(forall(t, in(t, Sigma(A, identityFunction(A))) <=> ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(identityFunction(A), a)))))) by InstantiateForall(
          Sigma(A, identityFunction(A))
        )(Sigma.definition of (f -> identityFunction(A), x -> A))
        val sigmaDef = thenHave(in(t, Sigma(A, identityFunction(A))) <=> ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(identityFunction(A), a))))) by InstantiateForall(t)

        have(
          in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) |-
            (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) /\ in(x, A) /\ in(firstInPair(AC2AC1aux2The(x, C)), x)
        ) by Tautology.from(sub1)
        thenHave(
          in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) |-
            (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) /\ in(x, A) /\ in(firstInPair(AC2AC1aux2The(x, C)), app(identityFunction(A), x))
        ) by Substitution.ApplyRules(subs)
        thenHave(
          in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) |-
            exists(d, (t === pair(x, d)) /\ in(x, A) /\ in(d, app(identityFunction(A), x)))
        ) by RightExists
        thenHave(
          in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) |-
            exists(x, exists(d, (t === pair(x, d)) /\ in(x, A) /\ in(d, app(identityFunction(A), x))))
        ) by RightExists

        have(
          in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))) |-
            in(t, Sigma(A, identityFunction(A)))
        ) by Tautology.from(lastStep, sigmaDef)
        thenHave(
          exists(x, in(x, A) /\ (t === pair(x, firstInPair(AC2AC1aux2The(x, C)))))
            |- in(t, Sigma(A, identityFunction(A)))
        ) by LeftExists
        have(in(t, Sigma(A, identityFunction(A)))) by Tautology.from(lastStep, s1)
      }
      thenHave(forall(t, in(t, fe) ==> in(t, Sigma(A, identityFunction(A))))) by RightForall
      have(subset(fe, Sigma(A, identityFunction(A)))) by Tautology.from(
        lastStep,
        subsetAxiom of (x -> fe, y -> Sigma(A, identityFunction(A)))
      )
      have(in(fe, powerSet(Sigma(A, identityFunction(A))))) by Tautology.from(
        lastStep,
        powerAxiom of (x -> fe, y -> Sigma(A, identityFunction(A)))
      )
    }

    val sub3 = have(subset(A, relationDomain(fe))) subproof {
      val subs = have(relationDomain(fe) === A) by Tautology.from(domainOfFirstElementOfAC2AC1aux2TheFunction)
      have(subset(A, A)) by Tautology.from(subsetReflexivity of (x -> A))
      thenHave(subset(A, relationDomain(fe))) by Substitution.ApplyRules(subs)
    }

    have(forall(t, in(t, Pi(A, identityFunction(A))) <=> (in(t, powerSet(Sigma(A, identityFunction(A)))) /\ (subset(A, relationDomain(t)) /\ functional(t))))) by InstantiateForall(
      Pi(A, identityFunction(A))
    )(Pi.definition of (x -> A, f -> identityFunction(A)))
    thenHave(
      in(fe, Pi(A, identityFunction(A)))
        <=> (in(fe, powerSet(Sigma(A, identityFunction(A)))) /\ (subset(A, relationDomain(fe)) /\ functional(fe)))
    ) by InstantiateForall(fe)
    have(in(fe, Pi(A, identityFunction(A)))) by Tautology.from(lastStep, sub1, sub2, sub3)
  }

  // Rovelli Gianmaria
  val cartWithIdIsPairwiseDisjoint = Lemma(pairwiseDisjoint(cartesianProductWithIdentity(A))) {
    val cartWithId = cartesianProductWithIdentity(A)
    val pairDisjDef = have(pairwiseDisjoint(cartWithId) <=> forall(B, forall(C, in(B, cartWithId) /\ in(C, cartWithId) ==> ((!(setIntersection(B, C) === emptySet)) ==> (B === C))))) by Tautology.from(
      pairwiseDisjoint.definition of (A -> cartWithId)
    )

    have(in(B, cartWithId) /\ in(C, cartWithId) ==> ((!(setIntersection(B, C) === emptySet)) ==> (B === C))) subproof {
      assume(in(B, cartWithId))
      assume(in(C, cartWithId))
      assume(!(setIntersection(B, C) === emptySet))

      have(!(forall(w, in(w, setIntersection(B, C)) <=> in(w, emptySet)))) by Tautology.from(extensionalityAxiom of (x -> setIntersection(B, C), y -> emptySet))
      val exw = thenHave(exists(w, (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(w, emptySet) /\ !in(w, setIntersection(B, C))))) by Tautology

      have(
        (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(w, emptySet) /\ !in(w, setIntersection(B, C)))
          |- in(w, setIntersection(B, C))
      ) by Tautology.from(emptySetAxiom of (x -> w))
      val tzBC = have(
        (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(w, emptySet) /\ !in(w, setIntersection(B, C)))
          |- in(w, B) /\ in(w, C)
      ) by Tautology.from(lastStep, setIntersectionMembership of (t -> w, x -> B, y -> C))

      val cartIdDef = have(
        forall(t, in(t, cartesianProductWithIdentity(A)) <=> in(t, powerSet(cartesianProduct(union(A), A))) /\ exists(b, in(b, A) /\ (t === cartesianProduct(b, singleton(b)))))
      ) by InstantiateForall(
        cartesianProductWithIdentity(A)
      )(
        cartesianProductWithIdentity.definition
      )
      have(
        in(B, cartesianProductWithIdentity(A)) <=> in(B, powerSet(cartesianProduct(union(A), A))) /\ exists(b, in(b, A) /\ (B === cartesianProduct(b, singleton(b))))
      ) by InstantiateForall(B)(cartIdDef)
      val exb = thenHave(
        exists(b, in(b, A) /\ (B === cartesianProduct(b, singleton(b))))
      ) by Tautology

      have(
        in(C, cartesianProductWithIdentity(A)) <=> in(C, powerSet(cartesianProduct(union(A), A))) /\ exists(b, in(b, A) /\ (C === cartesianProduct(b, singleton(b))))
      ) by InstantiateForall(C)(cartIdDef)
      val exc = thenHave(
        exists(c, in(c, A) /\ (C === cartesianProduct(c, singleton(c))))
      ) by Tautology

      val xyBC = have(
        in(b, A) /\ (B === cartesianProduct(b, singleton(b))) /\ in(c, A) /\ (C === cartesianProduct(c, singleton(c)))
          /\ in(w, B) /\ in(w, C)
          |- in(d, B) <=> in(d, C)
      ) subproof {
        assume(in(b, A))
        val subsB = assume((B === cartesianProduct(b, singleton(b))))
        assume(in(c, A))
        val subsC = assume((C === cartesianProduct(c, singleton(c))))

        have(
          forall(
            w,
            in(w, cartesianProduct(b, singleton(b)))
              <=> ((in(w, powerSet(powerSet(setUnion(b, singleton(b)))))) /\ (∃(t, ∃(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b))))))
          )
        ) by InstantiateForall(cartesianProduct(b, singleton(b)))(cartesianProduct.definition of (x -> b, y -> singleton(b)))
        val wDefB = thenHave(
          in(w, cartesianProduct(b, singleton(b)))
            <=> ((in(w, powerSet(powerSet(setUnion(b, singleton(b)))))) /\ (∃(t, ∃(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b))))))
        ) by InstantiateForall(w)
        have(
          forall(
            w,
            in(w, cartesianProduct(c, singleton(c)))
              <=> ((in(w, powerSet(powerSet(setUnion(c, singleton(c)))))) /\ (∃(t, ∃(z, (w === pair(t, z)) /\ in(t, c) /\ in(z, singleton(c))))))
          )
        ) by InstantiateForall(cartesianProduct(c, singleton(c)))(cartesianProduct.definition of (x -> c, y -> singleton(c)))
        val wDefC = thenHave(
          in(w, cartesianProduct(c, singleton(c)))
            <=> ((in(w, powerSet(powerSet(setUnion(c, singleton(c)))))) /\ (∃(t, ∃(z, (w === pair(t, z)) /\ in(t, c) /\ in(z, singleton(c))))))
        ) by InstantiateForall(w)

        // B
        assume(in(w, B))
        thenHave(in(w, cartesianProduct(b, singleton(b)))) by Substitution.ApplyRules(subsB)
        val etzB = have(∃(t, ∃(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b))))) by Tautology.from(lastStep, wDefB)

        have((w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)) |- in(z, singleton(b))) by Tautology
        val zb = have((w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)) |- z === b) by Tautology.from(lastStep, singletonHasNoExtraElements of (y -> z, x -> b))

        // C
        assume(in(w, C))
        thenHave(in(w, cartesianProduct(c, singleton(c)))) by Substitution.ApplyRules(subsC)
        val efgC = have(∃(f, ∃(g, (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c))))) by Tautology.from(lastStep, wDefC)

        have((w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)) |- in(g, singleton(c))) by Tautology
        val gc = have((w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)) |- g === c) by Tautology.from(lastStep, singletonHasNoExtraElements of (y -> g, x -> c))

        val subsp = have((w === pair(t, z)) /\ (w === pair(f, g)) |- w === pair(t, z)) by Restate
        have((w === pair(t, z)) /\ (w === pair(f, g)) |- w === pair(f, g)) by Restate
        thenHave((w === pair(t, z)) /\ (w === pair(f, g)) |- pair(t, z) === pair(f, g)) by Substitution.ApplyRules(subsp)
        val zg = have((w === pair(t, z)) /\ (w === pair(f, g)) |- z === g) by Tautology.from(lastStep, pairExtensionality of (a -> t, b -> z, c -> f, d -> g))

        have(
          (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)) /\
            (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)) |-
            z === b
        ) by Tautology.from(zb)
        thenHave(
          (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)) /\
            (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)) |-
            g === b
        ) by Substitution.ApplyRules(zg)
        thenHave(
          (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)) /\
            (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)) |-
            c === b
        ) by Substitution.ApplyRules(gc)
        thenHave(
          exists(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)) /\ (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c))) |-
            c === b
        ) by LeftExists
        thenHave(
          exists(t, exists(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)) /\ (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)))) |-
            c === b
        ) by LeftExists
        thenHave(
          exists(t, exists(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)))) /\ (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)) |-
            c === b
        ) by Tableau
        thenHave(
          exists(g, exists(t, exists(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)))) /\ (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c))) |-
            c === b
        ) by LeftExists
        thenHave(
          exists(f, exists(g, exists(t, exists(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b)))) /\ (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c)))) |-
            c === b
        ) by LeftExists
        thenHave(
          exists(t, exists(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b))))
            /\
              exists(f, exists(g, (w === pair(f, g)) /\ in(f, c) /\ in(g, singleton(c))))
              |-
              c === b
        ) by Tableau

        val bc = have(b === c) by Tautology.from(lastStep, etzB, efgC)

        val fwd = have(
          in(b, A) /\ (B === cartesianProduct(b, singleton(b))) /\ in(c, A) /\ (C === cartesianProduct(c, singleton(c)))
            /\ in(w, B) /\ in(w, C)
            |- in(d, B) ==> in(d, C)
        ) subproof {
          have(
            forall(
              w,
              in(w, cartesianProduct(b, singleton(b)))
                <=> ((in(w, powerSet(powerSet(setUnion(b, singleton(b)))))) /\ (∃(t, ∃(z, (w === pair(t, z)) /\ in(t, b) /\ in(z, singleton(b))))))
            )
          ) by InstantiateForall(cartesianProduct(b, singleton(b)))(cartesianProduct.definition of (x -> b, y -> singleton(b)))
          val wDefBd = thenHave(
            in(d, cartesianProduct(b, singleton(b)))
              <=> ((in(d, powerSet(powerSet(setUnion(b, singleton(b)))))) /\ (∃(x, ∃(y, (d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b))))))
          ) by InstantiateForall(d)

          // B
          assume(in(d, B))
          thenHave(in(d, cartesianProduct(b, singleton(b)))) by Substitution.ApplyRules(subsB)
          val exyB = have(∃(x, ∃(y, (d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b))))) by Tautology.from(lastStep, wDefBd)

          have((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- in(y, singleton(b))) by Tautology
          val zb = have((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- y === b) by Tautology.from(lastStep, singletonHasNoExtraElements of (y -> y, x -> b))
          thenHave((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- y === c) by Substitution.ApplyRules(bc)
          val yc = have((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- in(y, singleton(c))) by Tautology.from(lastStep, singletonHasNoExtraElements of (x -> c))

          // i need in(x, c)
          have((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- in(x, b)) by Restate
          val xc = thenHave((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- in(x, c)) by Substitution.ApplyRules(bc)

          val subsd = have((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- d === pair(x, y)) by Restate

          have((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- in(pair(x, y), cartesianProduct(c, singleton(c)))) by Tautology.from(
            yc,
            xc,
            pairInCartesianProduct of (a -> x, b -> y, x -> c, y -> singleton(c))
          )
          thenHave((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- in(pair(x, y), C)) by Substitution.ApplyRules(subsC)
          thenHave((d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)) |- in(d, C)) by Substitution.ApplyRules(subsd)
          thenHave(exists(y, (d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b))) |- in(d, C)) by LeftExists
          thenHave(exists(x, exists(y, (d === pair(x, y)) /\ in(x, b) /\ in(y, singleton(b)))) |- in(d, C)) by LeftExists
          have(in(d, C)) by Tautology.from(lastStep, exyB)
        }

        val bwd = have(
          in(b, A) /\ (B === cartesianProduct(b, singleton(b))) /\ in(c, A) /\ (C === cartesianProduct(c, singleton(c)))
            /\ in(w, B) /\ in(w, C)
            |- in(d, C) ==> in(d, B)
        ) subproof {
          have(
            forall(
              w,
              in(w, cartesianProduct(c, singleton(c)))
                <=> ((in(w, powerSet(powerSet(setUnion(c, singleton(c)))))) /\ (∃(t, ∃(z, (w === pair(t, z)) /\ in(t, c) /\ in(z, singleton(c))))))
            )
          ) by InstantiateForall(cartesianProduct(c, singleton(c)))(cartesianProduct.definition of (x -> c, y -> singleton(c)))
          val wDefBc = thenHave(
            in(d, cartesianProduct(c, singleton(c)))
              <=> ((in(d, powerSet(powerSet(setUnion(c, singleton(c)))))) /\ (∃(x, ∃(y, (d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c))))))
          ) by InstantiateForall(d)

          // C
          assume(in(d, C))
          thenHave(in(d, cartesianProduct(c, singleton(c)))) by Substitution.ApplyRules(subsC)
          val exyB = have(∃(x, ∃(y, (d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c))))) by Tautology.from(lastStep, wDefBc)

          have((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- in(y, singleton(c))) by Tautology
          val zc = have((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- y === c) by Tautology.from(lastStep, singletonHasNoExtraElements of (y -> y, x -> c))
          thenHave((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- y === b) by Substitution.ApplyRules(bc)
          val yb = have((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- in(y, singleton(b))) by Tautology.from(lastStep, singletonHasNoExtraElements of (x -> b))

          // i need in(x, b)
          have((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- in(x, c)) by Restate
          val xb = thenHave((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- in(x, b)) by Substitution.ApplyRules(bc)

          val subsd = have((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- d === pair(x, y)) by Restate

          have((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- in(pair(x, y), cartesianProduct(b, singleton(b)))) by Tautology.from(
            yb,
            xb,
            pairInCartesianProduct of (a -> x, b -> y, x -> b, y -> singleton(b))
          )
          thenHave((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- in(pair(x, y), B)) by Substitution.ApplyRules(subsB)
          thenHave((d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)) |- in(d, B)) by Substitution.ApplyRules(subsd)
          thenHave(exists(y, (d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c))) |- in(d, B)) by LeftExists
          thenHave(exists(x, exists(y, (d === pair(x, y)) /\ in(x, c) /\ in(y, singleton(c)))) |- in(d, B)) by LeftExists
          have(in(d, B)) by Tautology.from(lastStep, exyB)
        }
        have(thesis) by Tautology.from(fwd, bwd)
      }

      have(
        in(b, A) /\ (B === cartesianProduct(b, singleton(b))) /\ in(c, A) /\ (C === cartesianProduct(c, singleton(c))) /\ (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(w, emptySet) /\ !in(
          w,
          setIntersection(B, C)
        ))
          |- in(d, B) <=> in(d, C)
      ) by Tautology.from(tzBC, lastStep)
      thenHave(
        exists(
          b,
          in(b, A) /\ (B === cartesianProduct(b, singleton(b))) /\ in(c, A) /\ (C === cartesianProduct(c, singleton(c))) /\ (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(
            w,
            emptySet
          ) /\ !in(w, setIntersection(B, C)))
        )
          |- in(d, B) <=> in(d, C)
      ) by LeftExists
      thenHave(
        exists(b, in(b, A) /\ (B === cartesianProduct(b, singleton(b)))) /\ in(c, A) /\ (C === cartesianProduct(c, singleton(c))) /\ (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(
          w,
          emptySet
        ) /\ !in(w, setIntersection(B, C)))
          |- in(d, B) <=> in(d, C)
      ) by Tableau
      thenHave(
        exists(
          c,
          exists(b, in(b, A) /\ (B === cartesianProduct(b, singleton(b)))) /\ in(c, A) /\ (C === cartesianProduct(c, singleton(c))) /\ (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(
            w,
            emptySet
          ) /\ !in(w, setIntersection(B, C)))
        )
          |- in(d, B) <=> in(d, C)
      ) by LeftExists
      thenHave(
        exists(b, in(b, A) /\ (B === cartesianProduct(b, singleton(b))))
          /\
            exists(c, in(c, A) /\ (C === cartesianProduct(c, singleton(c))))
            /\
            (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(w, emptySet) /\ !in(w, setIntersection(B, C)))

            |- in(d, B) <=> in(d, C)
      ) by Tableau
      thenHave(
        exists(
          w,
          exists(b, in(b, A) /\ (B === cartesianProduct(b, singleton(b))))
            /\
              exists(c, in(c, A) /\ (C === cartesianProduct(c, singleton(c))))
              /\
              (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(w, emptySet) /\ !in(w, setIntersection(B, C)))
        )
          |- in(d, B) <=> in(d, C)
      ) by LeftExists
      thenHave(
        exists(b, in(b, A) /\ (B === cartesianProduct(b, singleton(b))))
          /\
            exists(c, in(c, A) /\ (C === cartesianProduct(c, singleton(c))))
            /\
            exists(
              w,
              (in(w, setIntersection(B, C)) /\ !in(w, emptySet)) \/ (in(w, emptySet) /\ !in(w, setIntersection(B, C)))
            )

            |- in(d, B) <=> in(d, C)
      ) by Tableau

      have(
        in(d, B) <=> in(d, C)
      ) by Tautology.from(lastStep, exw, exb, exc)
      thenHave(
        forall(d, in(d, B) <=> in(d, C))
      ) by RightForall
      have(B === C) by Tautology.from(lastStep, extensionalityAxiom of (x -> B, y -> C))
    }
    thenHave(forall(C, (in(B, cartWithId) /\ in(C, cartWithId) ==> ((!(setIntersection(B, C) === emptySet)) ==> (B === C))))) by RightForall
    thenHave(forall(B, forall(C, (in(B, cartWithId) /\ in(C, cartWithId) ==> ((!(setIntersection(B, C) === emptySet)) ==> (B === C)))))) by RightForall
    have(thesis) by Tautology.from(lastStep, pairDisjDef)
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
    val cartWithId = cartesianProductWithIdentity(A)
    assume(
      forall(
        A,
        !in(emptySet, A) /\ pairwiseDisjoint(A)
          ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
      )
    )
    val hp = thenHave(
      !in(emptySet, cartWithId) /\ pairwiseDisjoint(cartWithId)
        ==> exists(C, forall(B, in(B, cartWithId) ==> exists(y, setIntersection(B, C) === singleton(y))))
    ) by InstantiateForall(cartWithId)

    val sub1 = have(!in(emptySet, A) ==> exists(f, in(f, Pi(A, identityFunction(A))))) subproof {
      assume(!in(emptySet, A))
      val s1 = have(!in(emptySet, cartWithId)) by Tautology.from(AC2AC1aux1)
      val s2 = have(pairwiseDisjoint(cartWithId)) by Tautology.from(cartWithIdIsPairwiseDisjoint)
      val s3 = have(exists(C, forall(B, in(B, cartWithId) ==> exists(y, setIntersection(B, C) === singleton(y))))) by Tautology.from(s1, s2, hp)

      have(
        forall(B, in(B, cartWithId) ==> exists(y, setIntersection(B, C) === singleton(y)))
          |- in(firstElementOfAC2AC1aux2The(A, C), Pi(A, identityFunction(A)))
      ) by Tautology.from(AC2AC1aux3)
      thenHave(
        forall(B, in(B, cartWithId) ==> exists(y, setIntersection(B, C) === singleton(y)))
          |- exists(f, in(f, Pi(A, identityFunction(A))))
      ) by RightExists
      thenHave(
        exists(C, forall(B, in(B, cartWithId) ==> exists(y, setIntersection(B, C) === singleton(y))))
          |- exists(f, in(f, Pi(A, identityFunction(A))))
      ) by LeftExists
      have(
        exists(f, in(f, Pi(A, identityFunction(A))))
      ) by Tautology.from(lastStep, s3)
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
