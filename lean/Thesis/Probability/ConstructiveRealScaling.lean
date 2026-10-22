import Thesis.Probability.ConstructiveRealAdditive

namespace Thesis.Probability.SignedRatio

theorem divideNat_le_iff (a b : SignedRatio) (n : Nat) (positive : 0 < n) :
    LE (divideNat a n positive) (divideNat b n positive) ↔ LE a b :=
  (divideNat_le_divideNat_iff a b n n positive positive).trans
    (scaleInt_le_iff (n : Int) (by omega) a b)

theorem divideNat_add (a b : SignedRatio) (n : Nat) (positive : 0 < n) :
    Equiv (divideNat (add a b) n positive) (add (divideNat a n positive) (divideNat b n positive)) := by
  simp only [Equiv, divideNat, add, Int.natCast_mul, Int.add_mul]
  ac_rfl

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.PositiveRatio

theorem divide_scaled_precision (precision : PositiveRatio) (n : Nat) (positive : 0 < n) :
    SignedRatio.Equiv
      (SignedRatio.divideNat (precision.mul (ofNat n positive)).toSignedRatio n positive) precision.toSignedRatio := by
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, toSignedRatio, toQProb, QProb.toSignedRatio,
    mul, ofNat, Nat.mul_one, Int.natCast_mul]
  ac_rfl

end Thesis.Probability.PositiveRatio

namespace Thesis.Probability.ConstructiveReal

/-- Division refines the input to `n` times the requested output precision.
The denominator is a positive natural, never an arbitrary real comparison. -/
def divideNat (x : ConstructiveReal) (n : Nat) (positive : 0 < n) : ConstructiveReal where
  enclose precision := {
    lower := SignedRatio.divideNat (x.enclose (precision.mul (PositiveRatio.ofNat n positive))).lower n positive
    upper := SignedRatio.divideNat (x.enclose (precision.mul (PositiveRatio.ofNat n positive))).upper n positive
    ordered := (SignedRatio.divideNat_le_iff _ _ n positive).mpr (x.enclose _).ordered
    width := by
      have original := (SignedRatio.divideNat_le_iff _ _ n positive).mpr (x.enclose (precision.mul (PositiveRatio.ofNat n positive))).width
      have separated := SignedRatio.equiv_trans
        (SignedRatio.divideNat_add (x.enclose (precision.mul (PositiveRatio.ofNat n positive))).lower
          (precision.mul (PositiveRatio.ofNat n positive)).toSignedRatio n positive)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) (precision.divide_scaled_precision n positive))
      exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) separated).mp original }
  coherent _ _ := (SignedRatio.divideNat_le_iff _ _ n positive).mpr (x.coherent _ _)

theorem divideNat_mono {x y : ConstructiveReal} (bounded : LE x y) (n : Nat) (positive : 0 < n) :
    LE (divideNat x n positive) (divideNat y n positive) :=
  fun first second => (SignedRatio.divideNat_le_iff _ _ n positive).mpr (bounded _ _)

theorem divideNat_congr {x y : ConstructiveReal} (same : Equiv x y) (n : Nat) (positive : 0 < n) :
    Equiv (divideNat x n positive) (divideNat y n positive) :=
  ⟨divideNat_mono same.1 n positive, divideNat_mono same.2 n positive⟩

def scaleNat : Nat → ConstructiveReal → ConstructiveReal
  | 0, _ => zero
  | n + 1, x => add (scaleNat n x) x

theorem scaleNat_mono {x y : ConstructiveReal} (bounded : LE x y) (n : Nat) : LE (scaleNat n x) (scaleNat n y) := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact add_le_add ih bounded

theorem scaleNat_congr {x y : ConstructiveReal} (same : Equiv x y) (n : Nat) : Equiv (scaleNat n x) (scaleNat n y) :=
  ⟨scaleNat_mono same.1 n, scaleNat_mono same.2 n⟩

def scaleRatio (weight : QProb) (x : ConstructiveReal) : ConstructiveReal :=
  divideNat (scaleNat weight.num x) weight.den weight.den_pos

theorem scaleRatio_congr {x y : ConstructiveReal} (same : Equiv x y) (weight : QProb) :
    Equiv (scaleRatio weight x) (scaleRatio weight y) := divideNat_congr (scaleNat_congr same _) _ _

end Thesis.Probability.ConstructiveReal
