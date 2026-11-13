import Thesis.Probability.RationalApproximation

namespace Thesis.Probability

/-- An explicitly computed rational interval with certified width. -/
structure RationalEnclosure (precision : PositiveRatio) where
  lower : SignedRatio
  upper : SignedRatio
  ordered : SignedRatio.LE lower upper
  width : SignedRatio.LE upper (SignedRatio.add lower precision.toSignedRatio)

/-- An auxiliary constructive real, presented by mutually consistent rational
intervals at every positive rational precision. No comparison procedure for
arbitrary reals is included. Probability atom weights remain rational. -/
structure ConstructiveReal where
  enclose : (precision : PositiveRatio) → RationalEnclosure precision
  coherent : ∀ first second, SignedRatio.LE (enclose first).lower (enclose second).upper

namespace ConstructiveReal

/-- Closed order compares all rational lower and upper enclosures. -/
def LE (x y : ConstructiveReal) : Prop :=
  ∀ first second, SignedRatio.LE (x.enclose first).lower (y.enclose second).upper

def Equiv (x y : ConstructiveReal) : Prop := LE x y ∧ LE y x

theorem le_refl (x : ConstructiveReal) : LE x x := x.coherent

theorem le_trans {x y z : ConstructiveReal} (first : LE x y) (second : LE y z) : LE x z := by
  intro left right
  apply SignedRatio.le_of_forall_add_positive
  intro error
  have through := SignedRatio.le_trans (first left error) (y.enclose error).width
  exact SignedRatio.le_trans through
    (SignedRatio.add_le_add (second error right) (SignedRatio.le_refl _))

theorem equiv_refl (x : ConstructiveReal) : Equiv x x := ⟨le_refl x, le_refl x⟩
theorem equiv_symm {x y : ConstructiveReal} (same : Equiv x y) : Equiv y x := ⟨same.2, same.1⟩
theorem equiv_trans {x y z : ConstructiveReal} (first : Equiv x y) (second : Equiv y z) : Equiv x z :=
  ⟨le_trans first.1 second.1, le_trans second.2 first.2⟩

theorem le_congr {x x' y y' : ConstructiveReal} (first : Equiv x x') (second : Equiv y y') :
    LE x y ↔ LE x' y' :=
  ⟨fun bounded => le_trans first.2 (le_trans bounded second.1),
    fun bounded => le_trans first.1 (le_trans bounded second.2)⟩

/-- The exact rational embedding uses singleton intervals. -/
def ofSignedRatio (value : SignedRatio) : ConstructiveReal where
  enclose precision := ⟨value, value, SignedRatio.le_refl _,
    SignedRatio.le_add_of_nonnegative _ _ precision.signed_nonnegative⟩
  coherent _ _ := SignedRatio.le_refl _

theorem ofSignedRatio_le_iff (a b : SignedRatio) : LE (ofSignedRatio a) (ofSignedRatio b) ↔ SignedRatio.LE a b :=
  ⟨fun bounded => bounded PositiveRatio.one PositiveRatio.one, fun bounded _ _ => bounded⟩

theorem ofSignedRatio_equiv_iff (a b : SignedRatio) :
    Equiv (ofSignedRatio a) (ofSignedRatio b) ↔ SignedRatio.Equiv a b := by
  constructor
  · intro same
    exact SignedRatio.equiv_of_le_of_le ((ofSignedRatio_le_iff _ _).mp same.1) ((ofSignedRatio_le_iff _ _).mp same.2)
  · intro same
    have forward := (SignedRatio.le_congr (SignedRatio.equiv_refl a) same).mp (SignedRatio.le_refl a)
    have backward := (SignedRatio.le_congr same (SignedRatio.equiv_refl a)).mp (SignedRatio.le_refl a)
    exact ⟨(ofSignedRatio_le_iff _ _).mpr forward, (ofSignedRatio_le_iff _ _).mpr backward⟩

theorem lower_bound (x : ConstructiveReal) (precision : PositiveRatio) :
    LE (ofSignedRatio (x.enclose precision).lower) x := fun _ other => x.coherent precision other

theorem upper_bound (x : ConstructiveReal) (precision : PositiveRatio) :
    LE x (ofSignedRatio (x.enclose precision).upper) := fun other _ => x.coherent other precision

/-- An explicit enclosure is a certified approximation in the real order. -/
theorem enclosure_bounds (x : ConstructiveReal) (precision : PositiveRatio) :
    LE (ofSignedRatio (x.enclose precision).lower) x ∧ LE x (ofSignedRatio (x.enclose precision).upper) :=
  ⟨x.lower_bound precision, x.upper_bound precision⟩

/-- Reflection of the enclosure gives real negation. -/
def neg (x : ConstructiveReal) : ConstructiveReal where
  enclose precision := {
    lower := SignedRatio.neg (x.enclose precision).upper
    upper := SignedRatio.neg (x.enclose precision).lower
    ordered := (SignedRatio.neg_le_neg_iff _ _).mpr (x.enclose precision).ordered
    width := (SignedRatio.neg_le_add_iff _ _ _).mpr (x.enclose precision).width }
  coherent first second := (SignedRatio.neg_le_neg_iff _ _).mpr (x.coherent second first)

theorem neg_le_neg_iff (x y : ConstructiveReal) : LE (neg y) (neg x) ↔ LE x y := by
  constructor
  · intro compared first second
    exact (SignedRatio.neg_le_neg_iff _ _).mp (compared second first)
  · intro compared first second
    exact (SignedRatio.neg_le_neg_iff _ _).mpr (compared second first)

theorem neg_congr {x y : ConstructiveReal} (same : Equiv x y) : Equiv (neg x) (neg y) :=
  ⟨(neg_le_neg_iff _ _).mpr same.2, (neg_le_neg_iff _ _).mpr same.1⟩

/-- Addition computes each summand to half of the requested precision. -/
def add (x y : ConstructiveReal) : ConstructiveReal where
  enclose precision := {
    lower := SignedRatio.add (x.enclose precision.half).lower (y.enclose precision.half).lower
    upper := SignedRatio.add (x.enclose precision.half).upper (y.enclose precision.half).upper
    ordered := SignedRatio.add_le_add (x.enclose precision.half).ordered (y.enclose precision.half).ordered
    width := by
      have compared := SignedRatio.add_le_add (x.enclose precision.half).width (y.enclose precision.half).width
      have combined := SignedRatio.equiv_trans (SignedRatio.add_interchange (x.enclose precision.half).lower precision.half.toSignedRatio
        (y.enclose precision.half).lower precision.half.toSignedRatio)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) precision.half_add_half)
      exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) combined).mp compared }
  coherent first second := SignedRatio.add_le_add (x.coherent _ _) (y.coherent _ _)

theorem add_le_add {a b c d : ConstructiveReal} (first : LE a b) (second : LE c d) : LE (add a c) (add b d) :=
  fun left right => SignedRatio.add_le_add (first left.half right.half) (second left.half right.half)

theorem add_congr {a b c d : ConstructiveReal} (first : Equiv a b) (second : Equiv c d) : Equiv (add a c) (add b d) :=
  ⟨add_le_add first.1 second.1, add_le_add first.2 second.2⟩

def zero : ConstructiveReal := ofSignedRatio SignedRatio.zero
def one : ConstructiveReal := ofSignedRatio SignedRatio.one

def sub (x y : ConstructiveReal) : ConstructiveReal := add x (neg y)

end ConstructiveReal
end Thesis.Probability
