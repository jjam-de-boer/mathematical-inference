import Thesis.Probability.ConstructiveDerivativeWithinAlgebra
import Thesis.Probability.ConstructiveDerivativeWithinScaling
import Thesis.Probability.ConstructiveRealIntervalPartition

namespace Thesis.Probability.ConstructiveReal

/-- A derivative with one computed remainder modulus for an entire explicit
domain. Functions respect equivalence of real presentations. This uniform
certificate is stronger than separate pointwise derivatives with unrelated
moduli, and supplies finite-partition control without a mean-value point. -/
structure UniformDerivativeWithin (domain : ConstructiveReal → Prop)
    (function slope : ∀ x, domain x → ConstructiveReal) where
  congr : ∀ x y admittedX admittedY, Equiv x y → Equiv (function x admittedX) (function y admittedY)
  modulus : PositiveRatio → PositiveRatio
  remainder : ∀ epsilon radius : PositiveRatio, PositiveRatio.LE radius (modulus epsilon) →
    ∀ x, ∀ admittedX : domain x, ∀ y, ∀ admittedY : domain y, Within radius.toQProb x y →
      Within (QProb.mul epsilon.toQProb radius.toQProb) (function y admittedY)
        (add (function x admittedX) (mul (sub y x) (slope x admittedX)))

namespace UniformDerivativeWithin

def atPoint {domain : ConstructiveReal → Prop} {f slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f slope) (point : ConstructiveReal) (inside : domain point) :
    HasDerivativeWithinAt domain f point inside (slope point inside) where
  modulus := derivative.modulus
  remainder epsilon radius small y admitted close := derivative.remainder epsilon radius small point inside y admitted close

/-- Domain restriction retains the same uniform modulus. -/
def restrict {domain : ConstructiveReal → Prop} {f slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f slope) (smaller : ConstructiveReal → Prop)
    (included : ∀ x, smaller x → domain x) :
    UniformDerivativeWithin smaller (fun x admitted => f x (included x admitted))
      (fun x admitted => slope x (included x admitted)) where
  congr x y hx hy same := derivative.congr x y (included x hx) (included y hy) same
  modulus := derivative.modulus
  remainder epsilon radius small x hx y hy close :=
    derivative.remainder epsilon radius small x (included x hx) y (included y hy) close

def slope_congr {domain : ConstructiveReal → Prop} {f first second : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f first) (same : ∀ x admitted, Equiv (first x admitted) (second x admitted)) :
    UniformDerivativeWithin domain f second where
  congr := derivative.congr
  modulus := derivative.modulus
  remainder epsilon radius small x hx y hy close :=
    (within_congr (equiv_refl _) (add_congr (equiv_refl _) (mul_congr (equiv_refl _) (same x hx)))).mp
      (derivative.remainder epsilon radius small x hx y hy close)

def neg {domain : ConstructiveReal → Prop} {f slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f slope) :
    UniformDerivativeWithin domain (fun x admitted => ConstructiveReal.neg (f x admitted))
      (fun x admitted => ConstructiveReal.neg (slope x admitted)) where
  congr x y hx hy same := neg_congr (derivative.congr x y hx hy same)
  modulus := derivative.modulus
  remainder epsilon radius small x hx y hy close := (derivative.atPoint x hx).neg.remainder epsilon radius small y hy close

def add {domain : ConstructiveReal → Prop} {f g sf sg : ∀ x, domain x → ConstructiveReal}
    (first : UniformDerivativeWithin domain f sf) (second : UniformDerivativeWithin domain g sg) :
    UniformDerivativeWithin domain (fun x admitted => ConstructiveReal.add (f x admitted) (g x admitted))
      (fun x admitted => ConstructiveReal.add (sf x admitted) (sg x admitted)) where
  congr x y hx hy same := add_congr (first.congr x y hx hy same) (second.congr x y hx hy same)
  modulus epsilon := if PositiveRatio.LE (first.modulus epsilon.half) (second.modulus epsilon.half)
    then first.modulus epsilon.half else second.modulus epsilon.half
  remainder epsilon radius small x hx y hy close :=
    ((first.atPoint x hx).add (second.atPoint x hx)).remainder epsilon radius small y hy close

def mul_constant {domain : ConstructiveReal → Prop} {f slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f slope) (factor : ConstructiveReal) :
    UniformDerivativeWithin domain (fun x admitted => mul (f x admitted) factor) (fun x admitted => mul (slope x admitted) factor) where
  congr x y hx hy same := mul_congr (derivative.congr x y hx hy same) (equiv_refl factor)
  modulus epsilon := derivative.modulus (epsilon.divideNat factor.rationalApproximation.magnitudeBound
    (by unfold RegularRationalApproximation.magnitudeBound; omega))
  remainder epsilon radius small x hx y hy close :=
    ((derivative.atPoint x hx).mul_constant factor).remainder epsilon radius small y hy close

/-- A uniform derivative upper bound integrates to a secant upper bound on
an interval of width at most one. Equal rational partitions telescope the
certified errors; no mean-value point, arbitrary real comparison, or compactness
axiom is used. The explicit inclusion admits every point of the interval. -/
theorem upper_bound {domain : ConstructiveReal → Prop} {f slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f slope) (a b bound : ConstructiveReal)
    (ordered : LE a b) (width : LE (sub b a) one)
    (admitted : ∀ x, LE a x → LE x b → domain x)
    (bounded : ∀ x hx, LE a x → LE x b → LE (slope x hx) bound) :
    LE (f b (admitted b ordered (le_refl b)))
      (ConstructiveReal.add (f a (admitted a (le_refl a) ordered)) (mul (sub b a) bound)) := by
  let insideA := admitted a (le_refl a) ordered
  let insideB := admitted b ordered (le_refl b)
  apply le_of_forall_rational_error
  intro precision
  let parts := (derivative.modulus precision).den
  have partsPositive : 0 < parts := (derivative.modulus precision).den_pos
  let radius : PositiveRatio := ⟨1, parts, by decide, partsPositive⟩
  let r := ofSignedRatio radius.toSignedRatio
  let h := mul r (sub b a)
  let step := ConstructiveReal.add (mul h bound) (ofSignedRatio (QProb.mul precision.toQProb radius.toQProb).toSignedRatio)
  let point := intervalPoint a b parts partsPositive
  have radiusSmall : PositiveRatio.LE radius (derivative.modulus precision) := by
    change 1 * (derivative.modulus precision).den ≤ (derivative.modulus precision).num * (derivative.modulus precision).den
    simpa only [Nat.one_mul] using Nat.le_mul_of_pos_left (derivative.modulus precision).den (derivative.modulus precision).num_pos
  have pointInside (k : Nat) (hk : k ≤ parts) : domain (point k) :=
    admitted _ (intervalPoint_bounds a b ordered parts partsPositive k hk).1 (intervalPoint_bounds a b ordered parts partsPositive k hk).2
  have hNonnegative : LE zero h := mul_nonnegative
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr radius.signed_nonnegative))
    ((zero_le_sub_iff b a).mpr ordered)
  have telescope (k : Nat) (hk : k ≤ parts) :
      LE (f (point k) (pointInside k hk)) (ConstructiveReal.add (f a insideA) (scaleNat k step)) := by
    induction k with
    | zero =>
        exact (le_congr (derivative.congr _ a _ insideA (intervalPoint_zero a b parts partsPositive)) (add_zero _)).mpr (le_refl _)
    | succ k ih =>
        have before : k ≤ parts := by omega
        have range := intervalPoint_bounds a b ordered parts partsPositive k before
        have estimate := derivative.remainder precision radius radiusSmall (point k) (pointInside k before)
          (point (k + 1)) (pointInside (k + 1) hk) (intervalPoint_within a b ordered width parts partsPositive k)
        have increment : Equiv (sub (point (k + 1)) (point k)) h := intervalPoint_increment a b parts partsPositive k
        have replaced := (le_congr (equiv_refl _) (add_congr (add_congr (equiv_refl _) (mul_congr increment (equiv_refl _))) (equiv_refl _))).mp estimate.1
        have slopeBound := mul_le_mul_nonnegative hNonnegative (bounded _ (pointInside k before) range.1 range.2)
        have increased := le_trans replaced (add_le_add (add_le_add (le_refl _) slopeBound) (le_refl _))
        have oneStep : LE (f (point (k + 1)) (pointInside (k + 1) hk)) (ConstructiveReal.add (f (point k) (pointInside k before)) step) :=
          (le_congr (equiv_refl _) (add_assoc _ _ _)).mp increased
        exact (le_congr (equiv_refl _) (add_assoc _ _ _)).mp
          (le_trans oneStep (add_le_add (ih before) (le_refl step)))
  let count := ofSignedRatio (QProb.ofNat parts).toSignedRatio
  have countRadius : Equiv (mul count r) one :=
    equiv_trans (mul_comm _ _) (equiv_trans (ofSignedRatio_mul _ _)
      ((ofSignedRatio_equiv_iff _ _).mpr (PositiveRatio.signed_mul_inv radius)))
  have countIncrement : Equiv (mul count h) (sub b a) :=
    equiv_trans (equiv_symm (mul_assoc count r (sub b a)))
      (equiv_trans (mul_congr countRadius (equiv_refl _)) (one_mul _))
  have linearSum : Equiv (mul count (mul h bound)) (mul (sub b a) bound) :=
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (mul_congr countIncrement (equiv_refl bound))
  have errorProduct : Equiv (ofSignedRatio (QProb.mul precision.toQProb radius.toQProb).toSignedRatio)
      (mul (ofSignedRatio precision.toSignedRatio) r) := by
    rw [QProb.toSignedRatio_mul]
    exact equiv_symm (ofSignedRatio_mul _ _)
  have errorSum : Equiv (mul count (ofSignedRatio (QProb.mul precision.toQProb radius.toQProb).toSignedRatio))
      (ofSignedRatio precision.toSignedRatio) :=
    equiv_trans (mul_congr (equiv_refl count) errorProduct)
      (equiv_trans (mul_congr (equiv_refl count) (mul_comm _ _))
        (equiv_trans (equiv_symm (mul_assoc _ _ _))
          (equiv_trans (mul_congr countRadius (equiv_refl _)) (one_mul _))))
  have total : Equiv (scaleNat parts step)
      (ConstructiveReal.add (mul (sub b a) bound) (ofSignedRatio precision.toSignedRatio)) :=
    equiv_trans (scaleNat_mul parts step) (equiv_trans (mul_add _ _ _) (add_congr linearSum errorSum))
  have right : Equiv (ConstructiveReal.add (f a insideA) (scaleNat parts step))
      (ConstructiveReal.add (ConstructiveReal.add (f a insideA) (mul (sub b a) bound)) (ofSignedRatio precision.toSignedRatio)) :=
    equiv_trans (add_congr (equiv_refl _) total) (equiv_symm (add_assoc _ _ _))
  exact (le_congr (derivative.congr _ b _ insideB (intervalPoint_last a b parts partsPositive)) right).mp (telescope parts (Nat.le_refl parts))

/-- The lower secant inequality is the same constructive partition theorem
applied to the negative function. The slope bound may have either sign. -/
theorem lower_bound {domain : ConstructiveReal → Prop} {f slope : ∀ x, domain x → ConstructiveReal}
    (derivative : UniformDerivativeWithin domain f slope) (a b bound : ConstructiveReal)
    (ordered : LE a b) (width : LE (sub b a) one)
    (admitted : ∀ x, LE a x → LE x b → domain x)
    (bounded : ∀ x hx, LE a x → LE x b → LE bound (slope x hx)) :
    LE (ConstructiveReal.add (f a (admitted a (le_refl a) ordered)) (mul (sub b a) bound))
      (f b (admitted b ordered (le_refl b))) := by
  let fa := f a (admitted a (le_refl a) ordered)
  let fb := f b (admitted b ordered (le_refl b))
  let length := sub b a
  have estimate := derivative.neg.upper_bound a b (ConstructiveReal.neg bound) ordered width admitted
    (fun x hx above below => (neg_le_neg_iff bound _).mpr (bounded x hx above below))
  have inverted : Equiv (ConstructiveReal.neg (ConstructiveReal.add (ConstructiveReal.neg fa) (mul length (ConstructiveReal.neg bound))))
      (ConstructiveReal.add fa (mul length bound)) :=
    equiv_trans (neg_add _ _) (add_congr (neg_neg fa)
      (equiv_trans (neg_congr (mul_neg length bound)) (neg_neg (mul length bound))))
  have flipped : LE (ConstructiveReal.neg (ConstructiveReal.add (ConstructiveReal.neg fa) (mul length (ConstructiveReal.neg bound))))
      (ConstructiveReal.neg (ConstructiveReal.neg fb)) := (neg_le_neg_iff _ _).mpr estimate
  exact (le_congr inverted (neg_neg fb)).mp flipped

end UniformDerivativeWithin
end Thesis.Probability.ConstructiveReal
