import lisa.prooflib.Substitution.ApplyRules as Substitution
import lisa.automation.Tableau
import scala.util.Try

object Lab05 extends lisa.Main {

  val x = variable
  val y = variable
  val z = variable

  // We introduce the signature of lattices
  val <= = ConstantPredicateLabel("<=", 2)
  addSymbol(<=)
  val u = ConstantFunctionLabel("u", 2) // join (union for sets, disjunction in boolean algebras)
  addSymbol(u)
  val n = ConstantFunctionLabel("n", 2) // meet (interestion for sets, conjunction in boolean algebras)
  addSymbol(n)

  // Enables infix notation
  extension (left: Term) {
    def <=(right: Term): Formula = Lab05.<=(left, right)
    def u(right: Term): Term = Lab05.u(left, right)
    def n(right: Term): Term = Lab05.n(left, right)
  }

  // We will now prove some statement about partial orders, which we axiomatize

  val reflexivity = Axiom("reflexivity", x <= x)
  val antisymmetry = Axiom("antisymmetry", ((x <= y) /\ (y <= x)) ==> (x === y))
  val transitivity = Axiom("transitivity", ((x <= y) /\ (y <= z)) ==> (x <= z))
  val lub = Axiom("lub", ((x <= z) /\ (y <= z)) <=> ((x u y) <= z))
  val glb = Axiom("glb", ((z <= x) /\ (z <= y)) <=> (z <= (x n y)))

  // Now we'll need to reason with equality. We can do so with the Substitution tactic, which substitutes equals for equals.
  // The argument of Substitutions can be either an equality (s===t). In this case, the result should contain (s===t) in assumptions.
  // Or it can be a previously proven step showing a formula of the form (s===t). In this case, (s===t) does not
  // need to be in the left side of the conclusion, but assumptions of this precedently proven fact do.

  // Note however that Restate and Tautology now by themselves that t === t, for any t.

  val joinLowerBound = Theorem((x <= (x u y)) /\ (y <= (x u y))) {
    have(thesis) by Tautology.from(lub of (z := (x u y)), reflexivity of (x := (x u y)))
  }

  val joinCommutative = Theorem((x u y) === (y u x)) {
    val s1 = have((x u y) <= (y u x)) by Tautology.from(lub of (z := (y u x)), joinLowerBound of (x := y, y := x))
    have(thesis) by Tautology.from(s1, s1 of (x := y, y := x), antisymmetry of (x := x u y, y := y u x))
  }

  val joinAbsorption = Theorem((x <= y) |- (x u y) === y) {
    val h1 = have((x <= y) |- (y <= (x u y))) by Tautology.from(joinLowerBound)
    val h2 = have((x <= y) |- ((x u y) <= y)) by Tautology.from(reflexivity of (x := y), lub of (z := y))
    have(thesis) by Tautology.from(h1, h2, antisymmetry of (x := (x u y)))
  }

  val meetUpperBound = Theorem(((x n y) <= x) /\ ((x n y) <= y)) {
    // (x n y) <= (x n y)
    val h1 = have((x n y) <= (x n y)) by Tautology.from(reflexivity of (x := (x n y)))
    have(thesis) by Tautology.from(h1, glb of (z := (x n y)))
  }

  val meetCommutative = Theorem((x n y) === (y n x)) {
    // ((x n y) <= y) /\ ((x n y) <= x) => ((x n y) <= (y n x))
    // ((y n x) <= x) /\ ((y n x) <= y) => ((y n x) <= (x n y))
    val h1 = have((x n y) <= (y n x)) by Tautology.from(meetUpperBound, glb of (z := (x n y), x := y, y := x))
    val h2 = have((y n x) <= (x n y)) by Tautology.from(meetUpperBound of (x := y, y := x), glb of (z := (y n x)))
    have(thesis) by Tautology.from(h1, h2, antisymmetry of (x := (x n y), y := (y n x)))
  }

  val meetAbsorption = Theorem((x <= y) |- (x n y) === x) {
    // x <= (x n y)
    // ((x <= x) /\ (x <= y)) => (x <= (x n y))
    val h1 = have((x <= y) |- ((x n y) <= x)) by Tautology.from(meetUpperBound)
    val h2 = have((x <= y) |- (x <= (x n y))) by Tautology.from(reflexivity, glb of (z := x))
    have(thesis) by Tautology.from(h1, h2, antisymmetry of (x := (x n y), y := x))
  }

  val joinAssociative = Theorem((x u (y u z)) === ((x u y) u z)) {
    val sub1 = have((x u (y u z)) <= ((x u y) u z)) subproof {
      val h1 = have(((x u y) <= ((x u y) u z)) /\ (z <= ((x u y) u z))) by Tautology.from(joinLowerBound of (x := (x u y), y := z))
      val h2 = have((x <= ((x u y) u z))) by Tautology.from(h1, lub of (z := ((x u y) u z)))
      val h3 = have((y <= ((x u y) u z))) by Tautology.from(h1, lub of (z := ((x u y) u z)))
      val h4 = have((y u z) <= ((x u y) u z)) by Tautology.from(h1, h3, lub of (x := y, y := z, z := ((x u y) u z)))
      have(thesis) by Tautology.from(h2, h4, lub of (x := x, y := (y u z), z := ((x u y) u z)))
    }
    val sub2 = have(((x u y) u z) <= (x u (y u z))) subproof {
      val h1 = have((x <= (x u (y u z))) /\ ((y u z) <= (x u (y u z)))) by Tautology.from(joinLowerBound of (y := (y u z), z := (x u (y u z))))
      val h2 = have(y <= (x u (y u z))) by Tautology.from(h1, lub of (x := y, y := z, z := (x u (y u z))))
      val h3 = have(z <= (x u (y u z))) by Tautology.from(h1, lub of (x := y, y := z, z := (x u (y u z))))
      val h4 = have((x u y) <= (x u (y u z))) by Tautology.from(h1, h2, lub of (z := (x u (y u z))))
      have(thesis) by Tautology.from(h3, h4, lub of (x := (x u y), y := z, z := (x u (y u z))))
    }

    have(thesis) by Tautology.from(sub1, sub2, antisymmetry of (x := (x u (y u z)), y := ((x u y) u z)))
  }

  // Tedious, isn't it
  // Can we automate this?
  // Yes, we can!

  import lisa.prooflib.ProofTacticLib.ProofTactic
  import lisa.prooflib.Library

  object Whitman extends ProofTactic {
    def solve(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
      if goal.left.nonEmpty || goal.right.size != 1 then proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t")
      else
        TacticSubproof { // Starting the proof of `goal`

          goal.right.head match {
            case <=(Seq(left: Term, right: Term)) => {
              // We have different cases to consider
              (left, right) match {
                // 1. left is a join. In that case, lub gives us the decomposition
                case (u(Seq(a: Term, b: Term)), _) =>
                  // solve recursively a <= right and b <= right
                  val s1 = solve(a <= right)
                  val s2 = solve(b <= right)
                  // check if the recursive calls succedded
                  if s1.isValid & s2.isValid then have(left <= right) by Tautology.from(lub of (x := a, y := b, z := right), have(s1), have(s2))
                  else fail("The inequality is not true in general")

                // 2. right is a meet. In that case, glb gives us the decomposition
                case (_, n(Seq(a: Term, b: Term))) =>
                  // solve recursively a <= right and b <= right
                  // (a n b) <= a
                  val s1 = solve(left <= a)
                  // _ <= b
                  val s2 = solve(left <= b)
                  // _ <= a /\ _ <= b =>  _ <= (a n b)
                  // check if the recursive calls succedded
                  if s1.isValid & s2.isValid then have(left <= right) by Tautology.from(glb of (x := a, y := b, z := left), have(s1), have(s2))
                  else fail("The inequality is not true in general")

                // 3. left is a meet, right is a join. In that case, we try all pairs.
                case (n(Seq(a: Term, b: Term)), u(Seq(c: Term, d: Term))) =>
                  // (a n b) <= (c u d)
                  // solve recursively a <= right and b <= right
                  val s1 = solve(a <= right)
                  val s2 = solve(b <= right)

                  if s1.isValid then
                    have(left <= right) by Tautology.from(
                      // a <= (c u d)
                      have(s1),
                      // (a n b) <= a /\ (a n b) <= b
                      meetUpperBound of (x := a, y := b),
                      // (((a n b) <= a) /\ (a <= (c u d))) ==> ((a n b) <= (c u d))
                      transitivity of (x := left, y := a, z := right)
                    )
                  else if s2.isValid then
                    have(left <= right) by Tautology.from(
                      // b <= (c u d)
                      have(s2),
                      // (a n b) <= a /\ (a n b) <= b
                      meetUpperBound of (x := a, y := b),
                      // (((a n b) <= b) /\ (b <= (c u d))) ==> ((a n b) <= (c u d))
                      transitivity of (x := left, y := b, z := right)
                    )
                  else fail("The inequality is not true in general")

                // 4. left is a meet, right is a variable or unknown term.
                case (n(Seq(a: Term, b: Term)), _) =>
                  // We try to find a proof for either a <= right or b <= right
                  LazyList(a, b)
                    .map { e =>
                      (e, solve(e <= right))
                    }
                    .find {
                      _._2.isValid
                    }
                    .map { case (e, step) =>
                      have(left <= right) by Tautology.from(
                        // a <= _ or b <= _
                        have(step),
                        // (a n b) <= a /\ (a n b) <= b
                        meetUpperBound of (x := a, y := b),
                        // (((a n b) <= a) /\ (a <= _)) ==>  ((a n b) <= _ )
                        transitivity of (x := left, y := e, z := right)
                      )
                    }
                    .getOrElse(fail("The inequality is not true in general"))

                // 5. left is a variable or unknown term, right is a join.
                case (_, u(Seq(c: Term, d: Term))) =>
                  val s1 = solve(left <= c)
                  val s2 = solve(left <= d)
                  if s1.isValid then
                    have(left <= right) by Tautology.from(
                      // left <= c
                      have(s1),
                      //  c <= (c u d) /\ d <= (c u d)
                      joinLowerBound of (x := c, y := d),
                      // (left <= c /\ c <= (c u d))
                      transitivity of (x := left, y := c, z := (c u d))
                    )
                  else if s2.isValid then
                    have(left <= right) by Tautology.from(
                      // left <= d
                      have(s2),
                      //  c <= (c u d) /\ d <= (c u d)
                      joinLowerBound of (x := c, y := d),
                      // (left <= d /\ d <= (c u d))
                      transitivity of (x := left, y := d, z := (c u d))
                    )
                  else fail("The inequality is not true in general")

                // 6. left and right are variables or unknown terms.
                case _ =>
                  if (left == right) then have(left <= right) by Tautology.from(reflexivity of (x := left))
                  else fail("The inequality is not true in general")
              }
            }

            case ===(Seq(left: Term, right: Term)) =>
              val s1 = solve(left <= right)
              val s2 = solve(right <= left)
              if s1.isValid && s2.isValid then have(left === right) by Tautology.from(have(s1), have(s2), antisymmetry of (x := left, y := right))
              else fail("The inequality is not true in general")
            case _ => fail("Whitman can only be applied to solve goals of the form () |- s <= t or () |- s === t")
          }
        }

    }

  }

  // uncomment when the tactic is implemented

  val test1 = Theorem(x <= x) {
    have(thesis) by Whitman.solve
  }
  val test2 = Theorem(x <= (x u y)) {
    have(thesis) by Whitman.solve
  }
  val test3 = Theorem((y n x) <= x) {
    have(thesis) by Whitman.solve
  }
  val test4 = Theorem((x n y) <= (y u z)) {
    have(thesis) by Whitman.solve
  }
  val idempotence = Theorem((x u x) === x) {
    have(thesis) by Whitman.solve
  }
  val meetAssociative = Theorem((x n (y n z)) === ((x n y) n z)) {
    have(thesis) by Whitman.solve
  }
  val semiDistributivITY = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
    have(thesis) by Whitman.solve
  }

}
