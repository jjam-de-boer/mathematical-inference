import Thesis.Probability.PolynomialBoundCertificate

namespace Thesis
namespace Probability
namespace Examples
namespace PolynomialBoundCertificate

open RationalPolynomial Probability.PolynomialBoundCertificate

/-!
# Accepted and rejected exact bound certificates

The unit-interval example proves `x - x^2` nonnegative from `x ≥ 0` and
`1 - x ≥ 0`, using their product.  The unconstrained-square example permits
negative parameter values and an unreduced positive coefficient.  An ideal
term tests an arbitrary negative multiplier of a supplied zero constraint.

Two invalid certificates are rejected for different reasons: a negative
square weight, and a false polynomial identity despite a positive weight.
Checking these certificates is not asserted to discover them automatically.
-/

def x : Polynomial 1 := coordinate 0
def unitConstraints : Fin 2 → Polynomial 1 := fun index =>
  if index.val = 0 then x else sub (constant SignedRatio.one) x
def noZeroConstraints : Fin 0 → Polynomial 1 := fun index => Fin.elim0 index
def varianceTarget := sub x (mul x x)
def varianceCertificate : Certificate 1 2 0 := ⟨[⟨SignedRatio.one, constant SignedRatio.one, [0, 1]⟩], []⟩
theorem variance_checked : check unitConstraints noZeroConstraints varianceTarget varianceCertificate = true := by decide +kernel
theorem variance_nonnegative (values : Fin 1 → SignedRatio)
    (supported : forall index, SignedRatio.Nonnegative (evaluate (unitConstraints index) values)) :
    SignedRatio.Nonnegative (evaluate varianceTarget values) :=
  check_sound _ _ _ _ variance_checked values supported (fun index => Fin.elim0 index)

def noConstraints : Fin 0 → Polynomial 1 := fun index => Fin.elim0 index
def squareCertificate : Certificate 1 0 0 := ⟨[⟨⟨2, 2, by decide⟩, x, []⟩], []⟩
theorem square_checked : check noConstraints noConstraints (mul x x) squareCertificate = true := by decide +kernel
theorem square_nonnegative_for_every_assignment (values : Fin 1 → SignedRatio) :
    SignedRatio.Nonnegative (evaluate (mul x x) values) :=
  check_sound _ _ _ _ square_checked values (fun index => Fin.elim0 index) (fun index => Fin.elim0 index)

def negativeWeight : Certificate 1 0 0 := ⟨[⟨⟨-1, 1, by decide⟩, constant SignedRatio.one, []⟩], []⟩
def falseIdentity : Certificate 1 0 0 := ⟨[⟨SignedRatio.one, constant SignedRatio.one, []⟩], []⟩
theorem negative_weight_rejected : check noConstraints noConstraints (constant ⟨-1, 1, by decide⟩) negativeWeight = false := by decide +kernel
theorem false_identity_rejected : check noConstraints noConstraints (constant ⟨-1, 1, by decide⟩) falseIdentity = false := by decide +kernel

def normalizedPair : Fin 1 → Polynomial 2 := fun _ => sub (add (coordinate 0) (coordinate 1)) (constant SignedRatio.one)
def noPairConstraints : Fin 0 → Polynomial 2 := fun index => Fin.elim0 index
def negativeMultiplier : Polynomial 2 := constant ⟨-2, 3, by decide⟩
def zeroTarget := mul negativeMultiplier (normalizedPair 0)
def zeroCertificate : Certificate 2 0 1 := ⟨[], [⟨0, negativeMultiplier⟩]⟩
theorem negative_equality_multiplier_checked : check noPairConstraints normalizedPair zeroTarget zeroCertificate = true := by decide +kernel
theorem equality_term_vanishes (values : Fin 2 → SignedRatio)
    (normalized : forall index, SignedRatio.Equiv (evaluate (normalizedPair index) values) SignedRatio.zero) :
    SignedRatio.Nonnegative (evaluate zeroTarget values) :=
  check_sound _ _ _ _ negative_equality_multiplier_checked values (fun index => Fin.elim0 index) normalized

end PolynomialBoundCertificate
end Examples
end Probability
end Thesis
