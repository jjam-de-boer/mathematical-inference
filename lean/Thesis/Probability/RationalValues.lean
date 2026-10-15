import Thesis.Probability.SignedRatio

namespace Thesis
namespace Probability
namespace QProb

/-!
# Probability values in constructive signed rational arithmetic

Actual probability records and weights remain unchanged.  This exact
embedding supplies nonnegative `SignedRatio` values to auxiliary linear
algebra and polynomial certificates.  It never uses normalized `Rat`, whose
construction failed the project's transitive axiom policy.  Denominators
remain explicit positive naturals and equality remains cross-multiplication.

The bidirectional equivalence and operation identities lose no original
probability information.  Signed differences are auxiliary coefficients,
not signed probability weights.  General source compression is still a
separate obligation beyond this arithmetic bridge.
-/

def toSignedRatio (value : QProb) : SignedRatio := ⟨(value.num : Int), value.den, value.den_pos⟩

theorem toSignedRatio_equiv_iff (left right : QProb) :
    SignedRatio.Equiv left.toSignedRatio right.toSignedRatio ↔ Equiv left right := by
  simp only [SignedRatio.Equiv, toSignedRatio, ← Int.natCast_mul, Int.ofNat_inj, Equiv]

theorem toSignedRatio_congr {left right : QProb} (same : Equiv left right) :
    SignedRatio.Equiv left.toSignedRatio right.toSignedRatio := (toSignedRatio_equiv_iff left right).mpr same

theorem toSignedRatio_nonnegative (value : QProb) : 0 ≤ value.toSignedRatio.num := Int.natCast_nonneg _
theorem toSignedRatio_zero : zero.toSignedRatio = SignedRatio.zero := rfl
theorem toSignedRatio_one : one.toSignedRatio = SignedRatio.one := rfl

theorem toSignedRatio_add (left right : QProb) :
    (add left right).toSignedRatio = SignedRatio.add left.toSignedRatio right.toSignedRatio := by
  simp only [toSignedRatio, add, SignedRatio.add, Int.natCast_add, Int.natCast_mul]

theorem toSignedRatio_mul (left right : QProb) :
    (mul left right).toSignedRatio = SignedRatio.mul left.toSignedRatio right.toSignedRatio := by
  simp only [toSignedRatio, mul, SignedRatio.mul, Int.natCast_mul]

end QProb
end Probability
end Thesis
