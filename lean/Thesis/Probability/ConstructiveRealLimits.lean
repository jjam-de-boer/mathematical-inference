import Thesis.Probability.ConstructiveRealAdditive

namespace Thesis.Probability.SignedRatio

theorem sub_half_add (value : SignedRatio) (precision : PositiveRatio) :
    Equiv (add (sub value precision.half.toSignedRatio) precision.toSignedRatio)
      (add value precision.half.toSignedRatio) := by
  have widened := add_congr (equiv_refl (sub value precision.half.toSignedRatio))
    (equiv_symm precision.half_add_half)
  have collected := equiv_symm (add_assoc (sub value precision.half.toSignedRatio)
    precision.half.toSignedRatio precision.half.toSignedRatio)
  exact equiv_trans widened (equiv_trans collected
    (add_congr (sub_add_cancel value precision.half.toSignedRatio) (equiv_refl _)))

end Thesis.Probability.SignedRatio

namespace Thesis.Probability

/-- A regular rational approximation net, with a proved error estimate at
every pair of positive rational precisions. The approximants are executable. -/
structure RegularRationalApproximation where
  value : PositiveRatio → SignedRatio
  regular : ∀ first second, SignedRatio.LE (value first)
    (SignedRatio.add (value second) (SignedRatio.add first.toSignedRatio second.toSignedRatio))

namespace RegularRationalApproximation

private theorem lower_le_upper (approximation : RegularRationalApproximation) (first second : PositiveRatio) :
    SignedRatio.LE (SignedRatio.sub (approximation.value first) first.toSignedRatio)
      (SignedRatio.add (approximation.value second) second.toSignedRatio) := by
  apply (SignedRatio.sub_le_iff_le_add _ _ _).mpr
  have reordered : SignedRatio.Equiv
      (SignedRatio.add (approximation.value second) (SignedRatio.add first.toSignedRatio second.toSignedRatio))
      (SignedRatio.add (SignedRatio.add (approximation.value second) second.toSignedRatio) first.toSignedRatio) :=
    SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _))
      (SignedRatio.equiv_symm (SignedRatio.add_assoc _ _ _))
  exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) reordered).mp (approximation.regular first second)

/-- Complete a regular rational net by explicit intervals. No subsequence or
limit point is selected from a proposition. -/
def limit (approximation : RegularRationalApproximation) : ConstructiveReal where
  enclose precision := {
    lower := SignedRatio.sub (approximation.value precision.half) precision.half.toSignedRatio
    upper := SignedRatio.add (approximation.value precision.half) precision.half.toSignedRatio
    ordered := approximation.lower_le_upper precision.half precision.half
    width := (SignedRatio.le_congr (SignedRatio.equiv_refl _)
      (SignedRatio.sub_half_add (approximation.value precision.half) precision)).mpr (SignedRatio.le_refl _) }
  coherent first second := approximation.lower_le_upper first.half second.half

/-- The constructed limit lies within the certified error of every supplied
rational approximant, rather than only within its internal enclosure points. -/
theorem approximation_bounds (approximation : RegularRationalApproximation) (precision : PositiveRatio) :
    ConstructiveReal.LE (ConstructiveReal.ofSignedRatio (SignedRatio.sub (approximation.value precision) precision.toSignedRatio))
      approximation.limit ∧
    ConstructiveReal.LE approximation.limit
      (ConstructiveReal.ofSignedRatio (SignedRatio.add (approximation.value precision) precision.toSignedRatio)) :=
  ⟨fun _ other => approximation.lower_le_upper precision other.half,
    fun other _ => approximation.lower_le_upper other.half precision⟩

/-- Any real presentation satisfying all these approximation bounds has the
constructed limit value. No general real equality test is required. -/
theorem limit_unique (approximation : RegularRationalApproximation) (x : ConstructiveReal)
    (bounds : ∀ precision,
      ConstructiveReal.LE (ConstructiveReal.ofSignedRatio (SignedRatio.sub (approximation.value precision) precision.toSignedRatio)) x ∧
      ConstructiveReal.LE x (ConstructiveReal.ofSignedRatio (SignedRatio.add (approximation.value precision) precision.toSignedRatio))) :
    ConstructiveReal.Equiv approximation.limit x :=
  ⟨fun first second => (bounds first.half).1 PositiveRatio.one second,
    fun first second => (bounds second.half).2 first PositiveRatio.one⟩

end RegularRationalApproximation

/-- An explicitly supplied Cauchy modulus for rational values. This is the
constructive data needed to compute a limit from a sequence. -/
structure RationalCauchySequence where
  value : Nat → SignedRatio
  modulus : PositiveRatio → Nat
  cauchy : ∀ precision n m, modulus precision ≤ n → modulus precision ≤ m →
    SignedRatio.LE (value n) (SignedRatio.add (value m) precision.toSignedRatio)

namespace RationalCauchySequence

/-- A common later index connects any two requested precisions, so no
monotonicity assumption on the supplied modulus is necessary. -/
def regular (sequence : RationalCauchySequence) : RegularRationalApproximation where
  value precision := sequence.value (sequence.modulus precision)
  regular first second := by
    let later := max (sequence.modulus first) (sequence.modulus second)
    have firstBound := sequence.cauchy first (sequence.modulus first) later (Nat.le_refl _) (Nat.le_max_left _ _)
    have secondBound := sequence.cauchy second later (sequence.modulus second) (Nat.le_max_right _ _) (Nat.le_refl _)
    have combined := SignedRatio.le_trans firstBound
      (SignedRatio.add_le_add secondBound (SignedRatio.le_refl _))
    have reordered := SignedRatio.equiv_trans (SignedRatio.add_assoc
      (sequence.value (sequence.modulus second)) second.toSignedRatio first.toSignedRatio)
      (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _))
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) reordered).mp combined

def limit (sequence : RationalCauchySequence) : ConstructiveReal := sequence.regular.limit

/-- Each computably selected Cauchy approximant comes with a certified limit
interval whose width is twice the requested precision. -/
theorem approximation_bounds (sequence : RationalCauchySequence) (precision : PositiveRatio) :
    ConstructiveReal.LE
      (ConstructiveReal.ofSignedRatio (SignedRatio.sub (sequence.value (sequence.modulus precision)) precision.toSignedRatio))
      sequence.limit ∧
    ConstructiveReal.LE sequence.limit
      (ConstructiveReal.ofSignedRatio (SignedRatio.add (sequence.value (sequence.modulus precision)) precision.toSignedRatio)) :=
  sequence.regular.approximation_bounds precision

/-- The explicit modulus controls every later approximant, not only the
particular indices used to construct the limit. -/
theorem tail_bounds (sequence : RationalCauchySequence) (precision : PositiveRatio) (n : Nat)
    (later : sequence.modulus precision.half ≤ n) :
    ConstructiveReal.LE (ConstructiveReal.ofSignedRatio (SignedRatio.sub (sequence.value n) precision.toSignedRatio)) sequence.limit ∧
    ConstructiveReal.LE sequence.limit (ConstructiveReal.ofSignedRatio (SignedRatio.add (sequence.value n) precision.toSignedRatio)) := by
  let center := sequence.value (sequence.modulus precision.half)
  have fixed := sequence.approximation_bounds precision.half
  have left : SignedRatio.LE (SignedRatio.sub (sequence.value n) precision.toSignedRatio)
      (SignedRatio.sub center precision.half.toSignedRatio) := by
    apply (SignedRatio.sub_le_iff_le_add _ _ _).mpr
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.sub_half_add center precision)).mpr
      (sequence.cauchy precision.half n (sequence.modulus precision.half) later (Nat.le_refl _))
  have right : SignedRatio.LE (SignedRatio.add center precision.half.toSignedRatio)
      (SignedRatio.add (sequence.value n) precision.toSignedRatio) := by
    have compared := SignedRatio.add_le_add
      (sequence.cauchy precision.half (sequence.modulus precision.half) n (Nat.le_refl _) later)
      (SignedRatio.le_refl precision.half.toSignedRatio)
    have combined := SignedRatio.equiv_trans (SignedRatio.add_assoc (sequence.value n)
      precision.half.toSignedRatio precision.half.toSignedRatio)
      (SignedRatio.add_congr (SignedRatio.equiv_refl _) precision.half_add_half)
    exact (SignedRatio.le_congr (SignedRatio.equiv_refl _) combined).mp compared
  exact ⟨ConstructiveReal.le_trans ((ConstructiveReal.ofSignedRatio_le_iff _ _).mpr left) fixed.1,
    ConstructiveReal.le_trans fixed.2 ((ConstructiveReal.ofSignedRatio_le_iff _ _).mpr right)⟩

end RationalCauchySequence
namespace ConstructiveReal

/-- Every real presentation supplies a regular net of computed rational
lower endpoints. This does not round coordinates of a constrained law. -/
def rationalApproximation (x : ConstructiveReal) : RegularRationalApproximation where
  value precision := (x.enclose precision).lower
  regular first second := by
    have increased : SignedRatio.LE second.toSignedRatio
        (SignedRatio.add first.toSignedRatio second.toSignedRatio) :=
      (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.add_comm _ _)).mp
        (SignedRatio.le_add_of_nonnegative second.toSignedRatio first.toSignedRatio first.signed_nonnegative)
    exact SignedRatio.le_trans (x.coherent first second)
      (SignedRatio.le_trans (x.enclose second).width
        (SignedRatio.add_le_add (SignedRatio.le_refl _) increased))

/-- Completing the computed rational approximants recovers the original real. -/
theorem rationalApproximation_limit (x : ConstructiveReal) : Equiv x.rationalApproximation.limit x := by
  constructor
  · intro first second
    have lowered : SignedRatio.LE
        (SignedRatio.sub (x.enclose first.half).lower first.half.toSignedRatio) (x.enclose first.half).lower :=
      (SignedRatio.sub_le_iff_le_add _ _ _).mpr
        (SignedRatio.le_add_of_nonnegative _ _ first.half.signed_nonnegative)
    exact SignedRatio.le_trans lowered (x.coherent _ _)
  · intro first second
    exact SignedRatio.le_trans (x.coherent first second.half) (x.enclose second.half).width

end ConstructiveReal
end Thesis.Probability
