import Thesis.Probability.RationalPolynomialIdentity
import Thesis.Probability.RationalPolynomialFinite
import Thesis.Probability.SignedRatioOrder

namespace Thesis
namespace Probability
namespace PolynomialBoundCertificate

open RationalPolynomial
variable {variables nonnegativeCount zeroCount : Nat}

/-!
# Sound checking of supplied rational polynomial bound certificates

A certificate decomposes the requested nonnegative target into a finite sum
of nonnegative rational weights times polynomial squares times products of
supplied nonnegative constraints, plus arbitrary polynomial multiples of
supplied zero constraints.  Equality with that decomposition is checked by
the exact polynomial identity checker, not accepted as a producer's premise.

Constraint indices are finite typed data.  Negative weights are rejected;
the squared bases and equality multipliers may have arbitrary signed values.
Repeated constraint factors, zero weights and empty certificate lists are
permitted.  Coefficients are rational presentations with positive natural
denominators, never floating-point approximations or normalized `Rat` values.

The soundness theorem quantifies over every parameter assignment satisfying
the displayed constraints.  It does not prove those constraints for a causal
model by itself: probability compilation and model binding must do that.
Nor does rejection mean that the proposed bound is false or unprovable; no
complete certificate search or general optimizer is asserted here.
-/

structure SquareTerm (variables nonnegativeCount : Nat) where
  weight : SignedRatio
  base : Polynomial variables
  factors : List (Fin nonnegativeCount)

structure ZeroTerm (variables zeroCount : Nat) where
  constraint : Fin zeroCount
  multiplier : Polynomial variables

structure Certificate (variables nonnegativeCount zeroCount : Nat) where
  squareTerms : List (SquareTerm variables nonnegativeCount)
  zeroTerms : List (ZeroTerm variables zeroCount)

def SquareTerm.expression (constraints : Fin nonnegativeCount → Polynomial variables) (term : SquareTerm variables nonnegativeCount) :
    Polynomial variables :=
  mul (constant term.weight) (mul (mul term.base term.base) (product (term.factors.map constraints)))

def ZeroTerm.expression (constraints : Fin zeroCount → Polynomial variables) (term : ZeroTerm variables zeroCount) : Polynomial variables :=
  mul term.multiplier (constraints term.constraint)

def decomposition (nonnegativeConstraints : Fin nonnegativeCount → Polynomial variables) (zeroConstraints : Fin zeroCount → Polynomial variables)
    (certificate : Certificate variables nonnegativeCount zeroCount) : Polynomial variables :=
  add (sum (certificate.squareTerms.map (SquareTerm.expression nonnegativeConstraints)))
    (sum (certificate.zeroTerms.map (ZeroTerm.expression zeroConstraints)))

def check (nonnegativeConstraints : Fin nonnegativeCount → Polynomial variables) (zeroConstraints : Fin zeroCount → Polynomial variables)
    (target : Polynomial variables) (certificate : Certificate variables nonnegativeCount zeroCount) : Bool :=
  certificate.squareTerms.all (fun term => decide (SignedRatio.Nonnegative term.weight)) &&
    equalityCheck target (decomposition nonnegativeConstraints zeroConstraints certificate)

private theorem sum_nonnegative (polynomials : List (Polynomial variables)) (values : Fin variables → SignedRatio)
    (positive : forall polynomial, polynomial ∈ polynomials → SignedRatio.Nonnegative (evaluate polynomial values)) :
    SignedRatio.Nonnegative (evaluate (sum polynomials) values) := by
  induction polynomials with
  | nil => exact SignedRatio.nonnegative_zero
  | cons polynomial rest inductionHypothesis =>
      apply (SignedRatio.nonnegative_congr (evaluate_add polynomial (sum rest) values)).mpr
      exact SignedRatio.nonnegative_add (positive polynomial (List.mem_cons.mpr (Or.inl rfl)))
        (inductionHypothesis (fun next member => positive next (List.mem_cons.mpr (Or.inr member))))

private theorem product_nonnegative (polynomials : List (Polynomial variables)) (values : Fin variables → SignedRatio)
    (positive : forall polynomial, polynomial ∈ polynomials → SignedRatio.Nonnegative (evaluate polynomial values)) :
    SignedRatio.Nonnegative (evaluate (product polynomials) values) := by
  induction polynomials with
  | nil => exact (SignedRatio.nonnegative_congr (evaluate_constant SignedRatio.one values)).mpr SignedRatio.nonnegative_one
  | cons polynomial rest inductionHypothesis =>
      apply (SignedRatio.nonnegative_congr (evaluate_mul polynomial (product rest) values)).mpr
      exact SignedRatio.nonnegative_mul (positive polynomial (List.mem_cons.mpr (Or.inl rfl)))
        (inductionHypothesis (fun next member => positive next (List.mem_cons.mpr (Or.inr member))))

private theorem sum_zero (polynomials : List (Polynomial variables)) (values : Fin variables → SignedRatio)
    (vanished : forall polynomial, polynomial ∈ polynomials → SignedRatio.Equiv (evaluate polynomial values) SignedRatio.zero) :
    SignedRatio.Equiv (evaluate (sum polynomials) values) SignedRatio.zero := by
  induction polynomials with
  | nil => exact SignedRatio.equiv_refl SignedRatio.zero
  | cons polynomial rest inductionHypothesis =>
      exact SignedRatio.equiv_trans (evaluate_add polynomial (sum rest) values) (SignedRatio.equiv_trans
        (SignedRatio.add_congr (vanished polynomial (List.mem_cons.mpr (Or.inl rfl)))
          (inductionHypothesis (fun next member => vanished next (List.mem_cons.mpr (Or.inr member)))))
        (SignedRatio.add_zero SignedRatio.zero))

theorem SquareTerm.nonnegative (constraints : Fin nonnegativeCount → Polynomial variables) (term : SquareTerm variables nonnegativeCount)
    (values : Fin variables → SignedRatio) (weightPositive : SignedRatio.Nonnegative term.weight)
    (constraintsPositive : forall index, SignedRatio.Nonnegative (evaluate (constraints index) values)) :
    SignedRatio.Nonnegative (evaluate (term.expression constraints) values) := by
  have squared : SignedRatio.Nonnegative (evaluate (mul term.base term.base) values) :=
    (SignedRatio.nonnegative_congr (evaluate_mul term.base term.base values)).mpr (SignedRatio.nonnegative_square _)
  have constrained := product_nonnegative (term.factors.map constraints) values (by
    intro polynomial member
    rcases List.mem_map.mp member with ⟨index, _listed, rfl⟩
    exact constraintsPositive index)
  have combined : SignedRatio.Nonnegative (evaluate (mul (mul term.base term.base) (product (term.factors.map constraints))) values) :=
    (SignedRatio.nonnegative_congr (evaluate_mul _ _ values)).mpr (SignedRatio.nonnegative_mul squared constrained)
  exact (SignedRatio.nonnegative_congr (evaluate_mul _ _ values)).mpr
    (SignedRatio.nonnegative_mul ((SignedRatio.nonnegative_congr (evaluate_constant term.weight values)).mpr weightPositive) combined)

theorem ZeroTerm.vanishes (constraints : Fin zeroCount → Polynomial variables) (term : ZeroTerm variables zeroCount)
    (values : Fin variables → SignedRatio) (constraintsZero : forall index, SignedRatio.Equiv (evaluate (constraints index) values) SignedRatio.zero) :
    SignedRatio.Equiv (evaluate (term.expression constraints) values) SignedRatio.zero :=
  SignedRatio.equiv_trans (evaluate_mul term.multiplier (constraints term.constraint) values)
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (constraintsZero term.constraint)) (SignedRatio.mul_zero _))

/-- Every accepted decomposition proves the target nonnegative throughout
the supplied constraint domain.  No numerical optimization result, unchecked
identity, or nonnegativity assertion from the certificate producer is trusted. -/
theorem check_sound (nonnegativeConstraints : Fin nonnegativeCount → Polynomial variables) (zeroConstraints : Fin zeroCount → Polynomial variables)
    (target : Polynomial variables) (certificate : Certificate variables nonnegativeCount zeroCount)
    (accepted : check nonnegativeConstraints zeroConstraints target certificate = true) (values : Fin variables → SignedRatio)
    (nonnegative : forall index, SignedRatio.Nonnegative (evaluate (nonnegativeConstraints index) values))
    (vanished : forall index, SignedRatio.Equiv (evaluate (zeroConstraints index) values) SignedRatio.zero) :
    SignedRatio.Nonnegative (evaluate target values) := by
  have parts := Bool.and_eq_true_iff.mp accepted
  have squarePositive := sum_nonnegative (certificate.squareTerms.map (SquareTerm.expression nonnegativeConstraints)) values (by
    intro polynomial member
    rcases List.mem_map.mp member with ⟨term, listed, rfl⟩
    exact term.nonnegative nonnegativeConstraints values (of_decide_eq_true ((List.all_eq_true.mp parts.1) term listed)) nonnegative)
  have zeroVanished := sum_zero (certificate.zeroTerms.map (ZeroTerm.expression zeroConstraints)) values (by
    intro polynomial member
    rcases List.mem_map.mp member with ⟨term, _listed, rfl⟩
    exact term.vanishes zeroConstraints values vanished)
  have decomposed : SignedRatio.Nonnegative (evaluate (decomposition nonnegativeConstraints zeroConstraints certificate) values) :=
    (SignedRatio.nonnegative_congr (evaluate_add _ _ values)).mpr
      (SignedRatio.nonnegative_add squarePositive (SignedRatio.nonnegative_of_equiv_zero zeroVanished))
  exact (SignedRatio.nonnegative_congr (equalityCheck_sound _ _ parts.2 values)).mpr decomposed

end PolynomialBoundCertificate
end Probability
end Thesis
