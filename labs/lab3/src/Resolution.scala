import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*
import stainless.lang.Map.ToMapOps

import Utils.*
import Formulas.*

object Resolution {

  /** Make sure that all bound variables are uniquely named, and with names
    * different from free variables. This will simplify a lot future
    * transformations. The specific renaming can be arbitrary.
    */
  def makeVariableNamesUnique(f: Formula): Formula = {
    /*
     * A generator of fresh names
     * Any call to `get` should be followed by a call to `next`
     */
    case class FreshNames(i: BigInt) {
      require(i >= 0)

      // Return a fresh identifier
      def get: Identifier = Synthetic(i)
      // Update (functionally) this generator
      def next = FreshNames(i + 1)
    }

    def mVNUForm(
        subst: Map[Identifier, Term]
    )(f: Formula, freshId0: FreshNames): (Formula, FreshNames) = {
      decreases(f)
      f match {
        case Predicate(name, children) =>
          (Predicate(name, children.map(t => t.substitute(subst))), freshId0)
        case And(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (And(nLeft, nRight), freshId2)
        case Or(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (Or(nLeft, nRight), freshId2)
        case Implies(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (Implies(nLeft, nRight), freshId2)
        case Neg(inner) =>
          val (nInner, freshId1) = mVNUForm(subst)(inner, freshId0)
          (Neg(nInner), freshId1)
        case Forall(Var(id), inner) =>
          val x = Var(freshId0.get)
          val p = mVNUForm(subst + ((id, x)))(inner, freshId0.next)
          (Forall(x, p._1), p._2)
        case Exists(Var(id), inner) =>
          val x = Var(freshId0.get)
          val p = mVNUForm(subst + ((id, x)))(inner, freshId0.next)
          (Exists(x, p._1), p._2)
      }
    }

    // Generate fresh names for free variables
    val (alreadyTaken, freshId) = statefulLeftMap(
      f.freeVariables,
      FreshNames(0),
      (v: Identifier, id: FreshNames) => ((v, Var(id.get): Term), id.next)
    )
    mVNUForm(alreadyTaken.toMap)(f, freshId)._1
  }

  /* Part one: transforming formulas */

  /*
   * Put the formula in Negation Normal Form.
   */
  def negationNormalForm(f: Formula): Formula = {
    decreases(f)
    f match {
      case Predicate(_, _) => f
      case And(l, r)       => And(negationNormalForm(l), negationNormalForm(r))
      case Or(l, r)        => Or(negationNormalForm(l), negationNormalForm(r))
      case Implies(l, r) =>
        Or(negationNormalForm(Neg(l)), negationNormalForm(r))

      case Neg(Predicate(_, _)) => f
      case Neg(And(l, r)) =>
        Or(negationNormalForm(Neg(l)), negationNormalForm(Neg(r)))
      case Neg(Or(l, r)) =>
        And(negationNormalForm(Neg(l)), negationNormalForm(Neg(r)))
      case Neg(Implies(l, r)) =>
        And(negationNormalForm(l), negationNormalForm(Neg(r)))
      case Neg(Neg(n))        => negationNormalForm(n)
      case Neg(Forall(v, in)) => Exists(v, negationNormalForm(Neg(in)))
      case Neg(Exists(v, in)) => Forall(v, negationNormalForm(Neg(in)))

      case Forall(v, in) => Forall(v, negationNormalForm(in))
      case Exists(v, in) => Exists(v, negationNormalForm(in))
    }
  }.ensuring(res => res.isNNF)

  def skolemRec(f: Formula, subst: Map[Identifier, Term]): Formula = {
    decreases(f)
    require(f.isNNF)

    f match {
      case Predicate(id, children) =>
        Predicate(id, children.map(_.substitute(subst)))
      case And(l, r)     => And(skolemRec(l, subst), skolemRec(r, subst))
      case Or(l, r)      => Or(skolemRec(l, subst), skolemRec(r, subst))
      case Implies(l, r) => Implies(skolemRec(l, subst), skolemRec(r, subst))
      case Neg(in)       => Neg(skolemRec(in, subst))
      case Forall(Var(id), in) => Forall(Var(id), skolemRec(in, subst))
      case Exists(Var(id), in) => {
        val m = subst + (id -> Function(id, f.freeVariables.map(Var(_))))
        skolemRec(in, m)
      }
    }
  }.ensuring(res => res.isNNF && res.containsNoExistential)

  /** Perform the following steps:
    *   - Make variable names unique (using [[makeVariableNamesUnique]]);
    *   - Put the formula in negation normal form (using
    *     [[negationNormalForm]]);
    *   - Eliminate existential quantifiers using Skolemization.
    */
  def skolemizationNegation(f0: Formula): Formula = {
    val f = makeVariableNamesUnique(f0)
    val n = negationNormalForm(f)
    skolemRec(n, Map())
  }.ensuring(res => res.isNNF && res.containsNoExistential)

  def prenexRec(f: Formula): Formula = {
    decreases(f)
    require(f.isNNF && f.containsNoExistential)

    f match {
      case Predicate(_, _)     => f
      case And(l, r)           => And(prenexRec(l), prenexRec(r))
      case Or(l, r)            => Or(prenexRec(l), prenexRec(r))
      case Implies(l, r)       => Implies(prenexRec(l), prenexRec(r))
      case Neg(in)             => Neg(prenexRec(in))
      case Forall(Var(id), in) => prenexRec(in)
    }
  }.ensuring(res =>
    res.isNNF && res.containsNoUniversal && res.containsNoExistential
  )

  /** Perform the following steps:
    *   - Put the formula in negation normal, skolemized form (using
    *     [[skolemizationNegation]]);
    *   - Return the matrix of the formula.
    */
  def prenexSkolemizationNegation(f: Formula): Formula = {
    val s = skolemizationNegation(f)
    prenexRec(s)
  }.ensuring(res =>
    res.isNNF && res.containsNoUniversal && res.containsNoExistential
  )

  def cnfRec(f: Formula): Formula = {
    decreases(f)
    require(f.isNNF && f.containsNoUniversal && f.containsNoExistential)

    f match {
      case Or(And(li, ri), r) => And(cnfRec(Or(li, r)), cnfRec(Or(ri, r)))
      case Or(l, And(li, ri)) => And(cnfRec(Or(l, li)), cnfRec(Or(l, ri)))

      case Predicate(_, _) => f
      case Or(l, r)        => Or(cnfRec(l), cnfRec(r))
      case And(l, r)       => And(cnfRec(l), cnfRec(r))
      case Implies(l, r)   => Implies(cnfRec(l), cnfRec(r))
      case Neg(in)         => Neg(cnfRec(in))
    }
  }

  def toClause(f: Formula, ll: Clause): Clause = {
    decreases(f)

    f match {
      case Predicate(_, _)      => ll :+ Literal(f)
      case Neg(Predicate(_, _)) => ll :+ Literal(f)
      case Or(l, r)             => toClause(l, ll) ++ toClause(r, ll)
      case _                    => ll // cant happend
    }
  }

  def toCnfList(f: Formula, ll: List[Clause]): List[Clause] = {
    decreases(f)

    f match {
      case Predicate(_, _)      => ll :+ toClause(f, List())
      case Neg(Predicate(_, _)) => ll :+ toClause(f, List())
      case Or(_, _) =>
        ll :+ toClause(f, List())
      case And(l, r) => toCnfList(l, ll) ++ toCnfList(r, ll)
      case _         => ll // cant happend
    }
  }

  /** Perform the following steps:
    *   - Put the formula in prenex, negation normal, skolemized form (using
    *     [[prenexSkolemizationNegation]]);
    *   - Put the formula in conjunctive normal form (CNF).
    *
    * Note that the formula might grow exponentially in size. If we only want to
    * preserve satisfiability, we could avoid it by introducing fresh variables.
    * This function should NOT do that.
    */
  def conjunctionPrenexSkolemizationNegation(f: Formula): List[Clause] = {
    val p = prenexSkolemizationNegation(f)
    val c = cnfRec(p)
    toCnfList(c, List())
  }

  /* Part two: proof checking */

  /** A clause in a proof is either assumed, i.e. it is an hypothesis, or it is
    * deduced from previous clauses. A proof is written in a specific order, and
    * a justification should not refer to a subsequent step.
    */
  sealed abstract class Justification
  case object Assumed extends Justification
  case class Deduced(premises: (BigInt, BigInt), subst: Map[Identifier, Term])
      extends Justification

  type ResolutionProof = List[(Clause, Justification)]

  sealed trait ProofCheckResult {
    def valid = this match {
      case Valid      => true
      case Invalid(_) => false
    }
  }
  case object Valid extends ProofCheckResult
  case class Invalid(reason: String = "Unspecified") extends ProofCheckResult {
    @extern
    override def toString(): String = {
      reason
    }
  }

  /** Verify that [[proof]] is a valid proof, i.e. that every clause is
    * correctly justified (unless assumed). It is quite easy to miss some corner
    * cases. We thus recommend that you:
    *   - Have a look at the provided methods on Literal, as you will most
    *     likely need them;
    *   - "Keep It Simple, Stupid!": efficiency is not taken into account, so no
    *     need for fancy efficient checks;
    *   - On the other hand, checking that the conclusion of a resolution step
    *     is valid might be a bit more involved than it seems;
    *   - As a consequence of the previous point: add more tests;
    *   - You should return [[Valid]] when the proof is valid, and [[Invalid]]
    *     otherwise. In the latter case, you are free to set any string as the
    *     reason. Having precise failure reasons will help you a lot in the
    *     third part of this lab.
    *
    * Note: in order to use string interpolation in stainless, you need to wrap
    * it in an extern function, e.g.
    * @extern
    *   def mkErrorMessage = s"This is an error at step ${k}"
    *   Invalid(mkErrorMessage)
    */
  def checkDeduced(
      c: Clause,
      premises: (BigInt, BigInt),
      subst: Map[Identifier, Term],
      proof: ResolutionProof
  ): Boolean = {
    require(
      premises._1 >= 0 && premises._2 >= 0 && premises._1 < proof.size && premises._2 < proof.size
    )
    val pf1 = proof.apply(premises._1)
    val pf2 = proof.apply(premises._2)
    val fst = pf1._1.map(_.substitute(subst))
    val snd = pf2._1.map(_.substitute(subst))
    val fstf = fst.filter(e => !snd.contains(e.negation))
    val sndf = snd.filter(e => !fst.contains(e.negation))
    val u = fstf ++ sndf
    var r = c.filter(u.contains(_))
    r.size == c.size
  }

  def checkClause(
      c: Clause,
      j: Justification,
      proof: ResolutionProof
  ): Boolean = {
    j match {
      case Assumed => true
      case Deduced(premises, subst) => {
        if (
          premises._1 >= 0 && premises._2 >= 0 && premises._1 < proof.size && premises._2 < proof.size
        )
          checkDeduced(c, premises, subst, proof)
        else
          false
      }
    }
  }

  def checkResolutionProof(proof: ResolutionProof): ProofCheckResult = {
    proof match {
      case Nil() => {
        Valid
      }
      case _ => {
        val r =
          proof.filter((c, j) => !checkClause(c, j, proof))
        if (!r.isEmpty)
          Invalid("meh")
        else
          Valid
      }
    }
  }

  def assumptions(proof: ResolutionProof): List[Clause] = {
    proof
      .filter(_._2 match {
        case Assumed       => true
        case Deduced(_, _) => false
      })
      .map(_._1)
  }

  def conclusion(proof: ResolutionProof): Clause = {
    require(!proof.isEmpty)
    proof(proof.length - 1)._1
  }

  /* Part three: The Dreadsbury Mansion Mystery */
  object MansionFragments {
    import Mansion.*

    /** You can use the (scala) variable killer to refer to the killer E.g. of a
      * proof step using it: The killer is one of the characters (
      * List(eqv(killer, a), eqv(killer, b), eqv(killer, c)), Deduced((0, 5),
      * Map(id(1) -> killer)) )
      */

    def charlesInnocent: ResolutionProof = {
      List(
        (
          List(Literal(Neg(killedp(c, a)))),
          Deduced((6, 8), Map(id(2) -> c, id(3) -> a, id(4) -> a))
        )
      )
    }

    /*
     * k is the index your first step will have in the final proof.
     * You can use it to refer to previous steps relatively to this index,
     * so that your proof won't break if you go back and change your previous one.
     *
     * Mansion.buildFullProof contains all of the steps we implemented in your stead
     * and indexed them relatively to k.
     */
    def agathaKilledAgatha(k: BigInt): ResolutionProof = {
      List(
        (
          List(Literal(killedp(a, a))),
          Deduced((17, 15), Map(id(15) -> b, id(16) -> a, id(14) -> a))
        )
      )
    }
  }

  /*
   * To show that a formula phi is valid, we show that it's negation is unsatisfiable, i.e. !phi -> false.
   * Hence if a Proof contains an empty clause, then the negation of the conjunction of all assumed clauses has to be valid
   */
  def extractTheorem(proof: ResolutionProof): Formula = {
    require(
      !assumptions(proof).isEmpty && assumptions(proof).forall(!_.isEmpty)
    ) // Has "reasonable" assumptions
    require(proof.last._1 == Nil()) // Concludes unsat

    def toFormulas(clauses: List[Clause]): List[Formula] = {
      require(clauses.forall(!_.isEmpty))

      clauses match {
        case Nil()       => Nil()
        case Cons(c, cs) => Cons(or(c.map(_.get)), toFormulas(cs))
      }
    }

    val assumpts = toFormulas(assumptions(proof))
    assert(!assumpts.isEmpty)

    Neg(and(assumpts))
  }

}
