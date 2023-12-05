package lisa.mathematics
package settheory

import lisa.prooflib.Substitution

import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.settheory.SetTheoryTactics.*

import lisa.mathematics.settheory.SetTheory.pair
import lisa.mathematics.settheory.SetTheory.setIntersection
import lisa.mathematics.settheory.SetTheory.functional
import lisa.mathematics.settheory.SetTheory.functionalOver
import lisa.mathematics.settheory.SetTheory.functionalOverApplication
import lisa.mathematics.settheory.SetTheory.relationDomain
import lisa.mathematics.settheory.SetTheory.relationRange
import lisa.mathematics.settheory.SetTheory.singleton
import lisa.mathematics.settheory.SetTheory.singletonHasNoExtraElements
import lisa.mathematics.settheory.SetTheory.singletonExtensionality
import lisa.mathematics.settheory.SetTheory.setIntersection
import lisa.mathematics.settheory.SetTheory.setIntersectionMembership
import lisa.mathematics.settheory.SetTheory.restrictedFunction
import lisa.mathematics.settheory.SetTheory.setWithElementNonEmpty
import lisa.mathematics.settheory.SetTheory.Sigma
import lisa.mathematics.settheory.SetTheory.Pi
import lisa.mathematics.settheory.SetTheory.piUniqueness
import lisa.mathematics.settheory.SetTheory.app
import lisa.mathematics.settheory.SetTheory.relation
import lisa.mathematics.settheory.SetTheory.relationBetween
import lisa.mathematics.settheory.SetTheory.cartesianProduct

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
  private val D = variable

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
    ∃!(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(x, x)) /\ existsOne(y, in(y, x) /\ (t === pair(y, y)))))
  ) {
    have(∃!(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(x, x)) /\ existsOne(y, in(y, x) /\ (t === pair(y, y)))))) by UniqueComprehension(
      cartesianProduct(x, x),
      lambda((t, b), existsOne(y, in(y, x) /\ (t === pair(y, y))))
    )
  }
  // builds the identity function as set of pairs like pair(pair(x,x), pair(x,x))
  // TODO: not sure about existsOne
  //val identityFunction = DEF(x) --> The(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(x, x)) /\ ∃!(y, t === pair(y, y))))(identityFunctionUniqueness)
  val identityFunction = DEF(x) --> The(g, ∀(t, in(t, g) <=> in(t, cartesianProduct(x, x)) /\ ∃!(y, in(y, x) /\ (t === pair(y, y)))))(identityFunctionUniqueness)

  // this could be hard
  // see `pairSingletonIsFunctional`
  val identityFunctionIsFunctional = Theorem(functional(identityFunction(A))) {

    var id = identityFunction(A)

    var rel = have(relation(id)) subproof {
      have(forall(t, in(t, id) <=> in(t, cartesianProduct(A, A)) /\ existsOne(y, in(y, A) /\ (t === pair(y, y))))) by InstantiateForall(id)(
        identityFunction.definition of (x -> A),
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

    sorry
  }

  val restrictedFunctionOverIdentity = Lemma(restrictedFunction(identityFunction(A), A) === A) {
    sorry
  }

  val functionalApplicationOverIdentity = Lemma(app(identityFunction(A), A) === A) {
    sorry
  }

  val functionalApplicationOverSubset = Lemma(in(B, A) |- (app(identityFunction(A), B) === B)) {
    sorry
  }

  val relationDomainEquality = Lemma((x === y) /\ in(x, relationDomain(f)) |- in(y, relationDomain(f))) {
    val step1 = assume(x === y)
    assume(in(x, relationDomain(f)))
    thenHave(thesis) by Substitution.ApplyRules(step1)
  }
  val relationDomainNotEquality = Lemma((x === y) /\ !in(x, relationDomain(f)) |- !in(y, relationDomain(f))) {
    val step1 = assume(x === y)
    assume(!in(x, relationDomain(f)))
    thenHave(thesis) by Substitution.ApplyRules(step1)
  }

  val functionalExtensionality = Lemma(functional(f) |- ((x === y) ==> (app(f, x) === app(f, y)))) {
    assume(x === y)
    have(forall(z, in(z, x) <=> in(z, y)) <=> (x === y)) by Tautology.from(extensionalityAxiom)
    thenHave(forall(z, in(z, x) <=> in(z, y))) by Tautology
    thenHave(in(z, x) <=> in(z, y)) by InstantiateForall(z)

    // (app(f, x) === app(f, y)) <=> (((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, app(f, y)), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (app(f, y) === ∅)))

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
  // // by(fast elim !: apply_type)
  //

  // lemma Pi_iff:
  //   "f ∈ Pi(A,B) ⟷ function(f) ∧ f<=Sigma(A,B) ∧ A<=domain(f)"
  val Pi_iff = Lemma(
    in(f, Pi(A, B)) <=> (functional(f) /\ subset(f, Sigma(A, B)) /\ subset(A, relationDomain(f)))
  ) {
    sorry
  }

  // lemma function_apply_Pair: "⟦function(f);  a ∈ domain(f)⟧ ⟹ <a,f`a>: f"
  val function_apply_pair = Lemma(functional(f) /\ in(a, relationDomain(f)) |- in(pair(a, app(f, a)), f)) {
    assume(functional(f) /\ in(a, relationDomain(f)))
    val appDef = have(
      (app(f, a) === b) <=> (((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, b), f)) /\ ((!functional(f) \/ !in(a, relationDomain(f))) ==> (b === ∅)))
    ) by InstantiateForall(b)(app.definition of x -> a)
    val fwd = have(in(pair(a, b), f) |- app(f, a) === b) by Tautology.from(appDef)

    sorry
  }

  // lemma apply_Pair: "⟦f ∈ Pi(A,B);  a ∈ A⟧ ⟹ <a,f`a>: f"
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

  // // lemma apply_type [TC]: "⟦f ∈ Pi(A,B);  a ∈ A⟧ ⟹ f`a ∈ B(a)"
  // // by (blast intro: apply_Pair dest: fun_is_rel)
  //
  val apply_type = Lemma(
    in(f, Pi(A, B)) /\ in(a, A) |- in(app(f, a), app(B, a))
  ) {
    // in(f, Pi(A, B)) /\ in(a, A) |- in(pair(a, app(f, a)), f)
    // since in(f, Pi(A,B)) => subset(A, relationDomain(f)) /\ functional(f)
    // functional(f) /\ in(a, relationDomain(f)) |- in(pair(a, b), f) <=> (app(f, a) === b)
    // so app(f,a) === b
    sorry
  }

  val AC1_AC2_aux1 = Lemma({
    in(f, Pi(A, identityFunction(A))) /\ in(B, A) /\ !in(emptySet, A) |- subset(singleton(app(f, B)), setIntersection(B, relationRange(f)))
  }) {

    assume(in(f, Pi(A, identityFunction(A))))
    assume(in(B, A))
    assume(!in(emptySet, A))

    val sub1 = have(in(a, singleton(app(f, B))) |- in(a, B)) subproof {
      assume(in(B, A))
      assume(in(a, singleton(app(f, B))))

      val step1 = have(in(a, singleton(app(f, B))) |- a === app(f, B)) by Tautology.from(singletonHasNoExtraElements of (y -> a, x -> app(f, B)))

      have(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(app(f, B), app(identityFunction(A), B))) by Tautology.from(apply_type of (f -> f, A -> A, B -> identityFunction(A), a -> B))
      thenHave(in(f, Pi(A, identityFunction(A))) /\ in(B, A) |- in(app(f, B), B)) by Substitution.ApplyRules(functionalApplicationOverSubset)
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
//         "⟦pairwise_disjoint(A); B ∈ A; C ∈ A; D ∈ B; D ∈ C⟧ ⟹ f`B = f`C"
// there is just one sorry in this proof related to setIntersectionMembership
  val AC1_AC2_aux2 = Lemma((pairwiseDisjoint(A), in(B, A), in(C, A), in(D, B), in(D, C), functional(f)) |- app(f, B) === app(f, C)) {

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

  // lemma AC1_AC2: "AC1 ⟹ AC2"
  val AC1_AC2 = Lemma(
    forall(A, !in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A))))))
      ==>
        forall(
          A,
          !in(emptySet, A) /\ pairwiseDisjoint(A)
            ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
        )
  ) {
    assume(forall(A, !in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A)))))))

    var sub1 = have(
      !in(emptySet, A) /\ pairwiseDisjoint(A)
        ==> exists(C, forall(B, in(B, A) ==> exists(y, setIntersection(B, C) === singleton(y))))
    ) subproof {
      assume(!in(emptySet, A))
      assume(pairwiseDisjoint(A))

      have(!in(emptySet, A) ==> (exists(f, in(f, Pi(A, identityFunction(A)))))) by InstantiateForall
      have(exists(f, in(f, Pi(A, identityFunction(A))))) by Tautology.from(lastStep)

      // lemma1
      // in(f, Pi(A, identityFunction(A))) /\ in(B, A) /\ !in(emptySet, A)
      //  |- subset(singleton(app(f, B)), setIntersection(B, relationRange(f)))

      sorry
    }

    sorry
  }
}
