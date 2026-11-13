import Thesis.Probability.RationalNorm

namespace Thesis.Examples.RationalNorm
open Probability

private def a : SignedRatio := ⟨-3, 4, by decide⟩
private def b : SignedRatio := ⟨7, 6, by decide⟩
private def c : SignedRatio := ⟨-2, 3, by decide⟩
private def d : SignedRatio := ⟨5, 4, by decide⟩

example : QProb.Equiv (SignedRatio.sub (SignedRatio.mul a b) (SignedRatio.mul c d)).magnitude
    (⟨1, 24, by decide⟩ : QProb) := by decide +kernel

/-- Both inputs and both product-error terms may involve negative values. -/
example : QProb.LE (SignedRatio.sub (SignedRatio.mul a b) (SignedRatio.mul c d)).magnitude
    (QProb.add (QProb.mul ⟨1, 12, by decide⟩ ⟨7, 6, by decide⟩)
      (QProb.mul ⟨2, 3, by decide⟩ ⟨1, 12, by decide⟩)) :=
  SignedRatio.product_error_bound a b c d _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : QProb.Equiv (SignedRatio.add a (SignedRatio.neg a)).magnitude QProb.zero := by decide +kernel
example : QProb.Equiv (⟨-2, 4, by decide⟩ : SignedRatio).magnitude (⟨-3, 6, by decide⟩ : SignedRatio).magnitude :=
  SignedRatio.magnitude_congr (by decide +kernel)
example (value : SignedRatio) (bound : QProb) :
    QProb.LE value.magnitude bound ↔ SignedRatio.LE value bound.toSignedRatio ∧ SignedRatio.LE (SignedRatio.neg value) bound.toSignedRatio :=
  SignedRatio.magnitude_le_iff value bound

end Thesis.Examples.RationalNorm
