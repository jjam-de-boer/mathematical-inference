import Thesis.Probability.RationalPolynomial

namespace Thesis
namespace Probability
namespace RationalPolynomial

variable {variables : Nat}

/-!
# Sound executable checking of exact polynomial identities

The checker groups all terms having the first monomial's exponent vector,
tests their total rational coefficient for exact zero, and recurses after
removing that monomial.  Zero coefficients, duplicate terms, arbitrary term
order and unreduced signed fractions are accepted without a preprocessing
promise from a certificate producer.

The recursion strictly decreases the actual term-list length.  Its soundness
theorem proves that every accepted identity holds for every signed rational
assignment, not just finitely many numerical samples.  This is an algebraic
identity checker; it does not itself prove a causal bound, certify feasibility
of a model class, or solve a general optimization problem.
-/

def coefficientAt (powers : RationalMonomial.Powers variables) : Polynomial variables → SignedRatio
  | [] => SignedRatio.zero
  | term :: rest =>
      if term.powers = powers then SignedRatio.add term.coefficient (coefficientAt powers rest) else coefficientAt powers rest

def withoutMonomial (powers : RationalMonomial.Powers variables) (polynomial : Polynomial variables) : Polynomial variables :=
  polynomial.filter (fun term => decide (term.powers ≠ powers))

theorem withoutMonomial_cons_same (powers : RationalMonomial.Powers variables) (term : Term variables)
    (rest : Polynomial variables) (same : term.powers = powers) :
    withoutMonomial powers (term :: rest) = withoutMonomial powers rest := by
  have rejected : decide (term.powers ≠ powers) = false := decide_eq_false (fun different => different same)
  simp only [withoutMonomial, List.filter_cons, rejected, Bool.false_eq_true, if_false]

theorem withoutMonomial_cons_other (powers : RationalMonomial.Powers variables) (term : Term variables)
    (rest : Polynomial variables) (different : term.powers ≠ powers) :
    withoutMonomial powers (term :: rest) = term :: withoutMonomial powers rest := by
  have accepted := decide_eq_true different
  simp only [withoutMonomial, List.filter_cons, accepted, if_true]

theorem withoutMonomial_length_le (powers : RationalMonomial.Powers variables) (polynomial : Polynomial variables) :
    (withoutMonomial powers polynomial).length ≤ polynomial.length := by
  induction polynomial with
  | nil => exact Nat.le_refl 0
  | cons term rest inductionHypothesis =>
      by_cases same : term.powers = powers
      · rw [withoutMonomial_cons_same powers term rest same]
        simp only [List.length_cons]
        omega
      · rw [withoutMonomial_cons_other powers term rest same]
        exact Nat.succ_le_succ inductionHypothesis

/-- Integrating the collected coefficient and all other monomials gives the
same value as the original sparse list.  Only a decidable finite exponent
comparison is used to split the terms. -/
theorem evaluate_split_monomial (powers : RationalMonomial.Powers variables) (polynomial : Polynomial variables)
    (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate polynomial values)
      (SignedRatio.add (SignedRatio.mul (coefficientAt powers polynomial) (RationalMonomial.evaluate powers values))
        (evaluate (withoutMonomial powers polynomial) values)) := by
  induction polynomial with
  | nil =>
      exact SignedRatio.equiv_symm (SignedRatio.equiv_trans
        (SignedRatio.add_congr (SignedRatio.zero_mul _) (SignedRatio.equiv_refl SignedRatio.zero)) (SignedRatio.add_zero _))
  | cons term rest inductionHypothesis =>
      by_cases same : term.powers = powers
      · rw [withoutMonomial_cons_same powers term rest same, coefficientAt, if_pos same]
        have termSame : term.evaluate values = SignedRatio.mul term.coefficient (RationalMonomial.evaluate powers values) := by
          rw [Term.evaluate, same]
        change SignedRatio.Equiv (SignedRatio.add (term.evaluate values) (evaluate rest values)) _
        rw [termSame]
        exact SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _) inductionHypothesis)
          (SignedRatio.equiv_trans (SignedRatio.equiv_symm (SignedRatio.add_assoc _ _ _))
            (SignedRatio.add_congr (SignedRatio.equiv_symm (SignedRatio.add_mul _ _ _)) (SignedRatio.equiv_refl _)))
      · rw [withoutMonomial_cons_other powers term rest same, coefficientAt, if_neg same]
        change SignedRatio.Equiv (SignedRatio.add (term.evaluate values) (evaluate rest values))
          (SignedRatio.add _ (SignedRatio.add (term.evaluate values) _))
        exact SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _) inductionHypothesis)
          (SignedRatio.add_left_comm _ _ _)

def zeroCheck (polynomial : Polynomial variables) : Bool :=
  match polynomial with
  | [] => true
  | term :: rest => decide (SignedRatio.Equiv (coefficientAt term.powers (term :: rest)) SignedRatio.zero) &&
      zeroCheck (withoutMonomial term.powers rest)
termination_by polynomial.length
decreasing_by
  have bounded := withoutMonomial_length_le term.powers rest
  simp only [List.length_cons]
  omega

theorem zeroCheck_sound (polynomial : Polynomial variables) (accepted : zeroCheck polynomial = true)
    (values : Fin variables → SignedRatio) : SignedRatio.Equiv (evaluate polynomial values) SignedRatio.zero := by
  cases polynomial with
  | nil => exact SignedRatio.equiv_refl SignedRatio.zero
  | cons term rest =>
      rw [zeroCheck] at accepted
      have parts := Bool.and_eq_true_iff.mp accepted
      have vanished : SignedRatio.Equiv (coefficientAt term.powers (term :: rest)) SignedRatio.zero := of_decide_eq_true parts.1
      have remaining := zeroCheck_sound (withoutMonomial term.powers rest) parts.2 values
      have split := evaluate_split_monomial term.powers (term :: rest) values
      rw [withoutMonomial_cons_same term.powers term rest rfl] at split
      exact SignedRatio.equiv_trans split (SignedRatio.equiv_trans
        (SignedRatio.add_congr (SignedRatio.equiv_trans (SignedRatio.mul_congr vanished (SignedRatio.equiv_refl _))
          (SignedRatio.zero_mul _)) remaining) (SignedRatio.add_zero SignedRatio.zero))
termination_by polynomial.length
decreasing_by
  have bounded := withoutMonomial_length_le term.powers rest
  simp only [List.length_cons]
  omega

def equalityCheck (left right : Polynomial variables) : Bool := zeroCheck (sub left right)

theorem equalityCheck_sound (left right : Polynomial variables) (accepted : equalityCheck left right = true)
    (values : Fin variables → SignedRatio) : SignedRatio.Equiv (evaluate left values) (evaluate right values) := by
  have vanished := zeroCheck_sound (sub left right) accepted values
  exact (SignedRatio.sub_equiv_zero_iff _ _).mp
    (SignedRatio.equiv_trans (SignedRatio.equiv_symm (evaluate_sub left right values)) vanished)

end RationalPolynomial
end Probability
end Thesis
