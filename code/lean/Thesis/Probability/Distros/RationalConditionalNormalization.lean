import Thesis.Probability.Distros.RationalLinearHomogenization

namespace Thesis.Probability.Distros.RationalLinear.Conditional

/-!
# Exact evidence normalization as a finite rational linear system

A supported original assignment has denominator response `d · w` in `(0,1]`.
Set `t = 1 / (d · w)` and `z = t * w`. The original rows are homogenized,
`d · z = 1` is imposed by two integer rows, and `t ≥ 1` is retained explicitly.
Conversely every solution of those rows gives `w = z / t`, an original feasible
assignment whose denominator is positive and at most one. Both maps construct
their rational values directly, with no denominator bound or chosen witness.

The denominator's probability bound is an explicit part of the source domain.
Probability-law clients must prove it from their actual evidence event; it is
not inferred from arbitrary linear coefficients. The response theorem below
preserves every numerator divided by that denominator. No conditional optimizer
or native causal endpoint theorem is claimed by this normalization layer.
-/

variable {variables : Nat}

private theorem inverse_positive (value : SignedRatio) (positive : 0 < value.num) :
    0 < (positiveInverse value positive).num := by
  change 0 < (value.den : Int)
  have h := value.den_pos
  omega

private theorem one_le_inverse_iff (value : SignedRatio) (positive : 0 < value.num) :
    SignedRatio.LE SignedRatio.one (positiveInverse value positive) ↔ SignedRatio.LE value SignedRatio.one := by
  have recovered : (value.num.toNat : Int) = value.num := by omega
  simp only [SignedRatio.le_iff_cross, positiveInverse, SignedRatio.one,
    Int.natCast_one, Int.one_mul, Int.mul_one]
  rw [recovered]

private theorem inverse_le_one_iff (value : SignedRatio) (positive : 0 < value.num) :
    SignedRatio.LE (positiveInverse value positive) SignedRatio.one ↔ SignedRatio.LE SignedRatio.one value := by
  have recovered : (value.num.toNat : Int) = value.num := by omega
  simp only [SignedRatio.le_iff_cross, positiveInverse, SignedRatio.one,
    Int.natCast_one, Int.one_mul, Int.mul_one]
  rw [recovered]

private theorem positive_of_one_le {value : SignedRatio} (bounded : SignedRatio.LE SignedRatio.one value) :
    0 < value.num := by
  rw [SignedRatio.le_iff_cross] at bounded
  simp only [SignedRatio.one, Int.one_mul, Int.natCast_one, Int.mul_one] at bounded
  have h := value.den_pos
  omega

private theorem positive_of_equiv {left right : SignedRatio}
    (same : SignedRatio.Equiv left right) (positive : 0 < right.num) : 0 < left.num := by
  have productPositive : 0 < right.num * (left.den : Int) :=
    Int.mul_pos positive (by have h := left.den_pos; omega)
  rw [← same] at productPositive
  by_cases positiveLeft : 0 < left.num
  · exact positiveLeft
  · have nonpositive : left.num ≤ 0 := by omega
    have productNonpositive := Int.mul_nonpos_of_nonpos_of_nonneg nonpositive (Int.natCast_nonneg right.den)
    omega

/-- Evidence positivity is independent of its unreduced signed-rational
presentation. Law adapters use this to transfer the actual event support. -/
theorem num_pos_iff_of_equiv {left right : SignedRatio} (same : SignedRatio.Equiv left right) :
    0 < left.num ↔ 0 < right.num :=
  ⟨fun positive => positive_of_equiv (SignedRatio.equiv_symm same) positive,
    fun positive => positive_of_equiv same positive⟩

private theorem inverse_congr {left right : SignedRatio} (same : SignedRatio.Equiv left right)
    (leftPositive : 0 < left.num) (rightPositive : 0 < right.num) :
    SignedRatio.Equiv (positiveInverse left leftPositive) (positiveInverse right rightPositive) := by
  have leftRecovered : (left.num.toNat : Int) = left.num := by omega
  have rightRecovered : (right.num.toNat : Int) = right.num := by omega
  change (left.den : Int) * (right.num.toNat : Int) = (right.den : Int) * (left.num.toNat : Int)
  rw [leftRecovered, rightRecovered]
  simpa only [Int.mul_comm] using same.symm

private theorem inverse_inverse (value : SignedRatio) (positive : 0 < value.num) :
    SignedRatio.Equiv (positiveInverse (positiveInverse value positive) (inverse_positive value positive)) value := by
  have recovered : (value.num.toNat : Int) = value.num := by omega
  change (value.num.toNat : Int) * (value.den : Int) = value.num * ((value.den : Int).toNat : Int)
  rw [recovered]
  rfl

/-- Two ordinary rows impose the literal normalized evidence value one. -/
def evidenceRows (denominator : Fin variables → Int) : List (Inequality (variables + 1)) :=
  [(⟨denominator, SignedRatio.one⟩ : Inequality variables).extendZero,
    (⟨fun i => -denominator i, SignedRatio.neg SignedRatio.one⟩ : Inequality variables).extendZero]

theorem evidenceRows_iff (denominator : Fin variables → Int) (values : Fin variables → SignedRatio)
    (scale : SignedRatio) :
    Satisfies (evidenceRows denominator) (extend values scale) ↔
      SignedRatio.Equiv (dot variables denominator values) SignedRatio.one := by
  have upper : (⟨denominator, SignedRatio.one⟩ : Inequality variables).extendZero.Holds (extend values scale) ↔
      SignedRatio.LE (dot variables denominator values) SignedRatio.one :=
    Inequality.extendZero_holds_iff _ values scale
  have lower : (⟨fun i => -denominator i, SignedRatio.neg SignedRatio.one⟩ : Inequality variables).extendZero.Holds
      (extend values scale) ↔ SignedRatio.LE SignedRatio.one (dot variables denominator values) :=
    (Inequality.extendZero_holds_iff _ values scale).trans
      ((SignedRatio.le_congr (dot_neg_coefficients variables denominator values) (SignedRatio.equiv_refl _)).trans
        (SignedRatio.neg_le_neg_iff _ _))
  constructor
  · intro valid
    exact SignedRatio.equiv_of_le_of_le (upper.mp (valid _ (List.mem_cons_self ..)))
      (lower.mp (valid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  · intro normalized row member
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact upper.mpr ((SignedRatio.le_congr normalized (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl _))
    · have same := List.mem_singleton.mp later
      cases same
      exact lower.mpr ((SignedRatio.le_congr (SignedRatio.equiv_refl _) normalized).mpr (SignedRatio.le_refl _))

/-- A closed linear lower bound excludes zero scale without a strict-row
oracle. Evidence probabilities are at most one, so their reciprocals meet it. -/
def scaleRow (variables : Nat) : Inequality (variables + 1) :=
  ⟨fun i => if i = Fin.last variables then -1 else 0, SignedRatio.neg SignedRatio.one⟩

theorem scaleRow_iff (values : Fin variables → SignedRatio) (scale : SignedRatio) :
    (scaleRow variables).Holds (extend values scale) ↔ SignedRatio.LE SignedRatio.one scale := by
  have rewritten := SignedRatio.le_congr
    (dot_negative_unit (variables + 1) (Fin.last variables) (extend values scale))
    (SignedRatio.equiv_refl (SignedRatio.neg SignedRatio.one))
  simpa only [extend_last] using rewritten.trans (SignedRatio.neg_le_neg_iff _ _)

def normalizedRows (rows : List (Inequality variables)) (denominator : Fin variables → Int) :
    List (Inequality (variables + 1)) :=
  homogenizeRows rows ++ (evidenceRows denominator ++ [scaleRow variables])

theorem normalizedRows_iff (rows : List (Inequality variables)) (denominator : Fin variables → Int)
    (values : Fin variables → SignedRatio) (scale : SignedRatio) :
    Satisfies (normalizedRows rows denominator) (extend values scale) ↔
      Satisfies (homogenizeRows rows) (extend values scale) ∧
        SignedRatio.Equiv (dot variables denominator values) SignedRatio.one ∧ SignedRatio.LE SignedRatio.one scale := by
  constructor
  · intro valid
    refine ⟨fun row member => valid row (List.mem_append_left _ member), ?_, ?_⟩
    · exact (evidenceRows_iff denominator values scale).mp
        (fun row member => valid row (List.mem_append_right _ (List.mem_append_left _ member)))
    · exact (scaleRow_iff values scale).mp
        (valid _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _))))
  · rintro ⟨original, evidence, lower⟩ row member
    rcases List.mem_append.mp member with old | added
    · exact original row old
    · rcases List.mem_append.mp added with event | last
      · exact (evidenceRows_iff denominator values scale).mpr evidence row event
      · have same := List.mem_singleton.mp last
        cases same
        exact (scaleRow_iff values scale).mpr lower

structure SupportedAssignment (rows : List (Inequality variables)) (denominator : Fin variables → Int) where
  values : Fin variables → SignedRatio
  feasible : Satisfies rows values
  positive : 0 < (dot variables denominator values).num
  bounded : SignedRatio.LE (dot variables denominator values) SignedRatio.one

structure NormalizedAssignment (rows : List (Inequality variables)) (denominator : Fin variables → Int) where
  values : Fin (variables + 1) → SignedRatio
  feasible : Satisfies (normalizedRows rows denominator) values

namespace NormalizedAssignment

variable {rows : List (Inequality variables)} {denominator : Fin variables → Int}

def masses (point : NormalizedAssignment rows denominator) : Fin variables → SignedRatio :=
  fun i => point.values i.castSucc

def scale (point : NormalizedAssignment rows denominator) : SignedRatio := point.values (Fin.last variables)

theorem spec (point : NormalizedAssignment rows denominator) :
    Satisfies (homogenizeRows rows) (extend point.masses point.scale) ∧
      SignedRatio.Equiv (dot variables denominator point.masses) SignedRatio.one ∧
      SignedRatio.LE SignedRatio.one point.scale := by
  apply (normalizedRows_iff rows denominator point.masses point.scale).mp
  change Satisfies (normalizedRows rows denominator)
    (extend (fun i => point.values i.castSucc) (point.values (Fin.last variables)))
  rw [extend_restrict]
  exact point.feasible

theorem scale_positive (point : NormalizedAssignment rows denominator) : 0 < point.scale.num :=
  positive_of_one_le point.spec.2.2

private theorem decoded_evidence (point : NormalizedAssignment rows denominator) :
    SignedRatio.Equiv
      (dot variables denominator (fun i => SignedRatio.mul (positiveInverse point.scale point.scale_positive) (point.masses i)))
      (positiveInverse point.scale point.scale_positive) :=
  SignedRatio.equiv_trans (dot_mul_values variables denominator point.masses _)
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _) point.spec.2.1)
      (SignedRatio.mul_one _))

/-- Decode every normalized solution into the original supported domain.
The scale row supplies positivity and the probability upper bound; the old
row system, including any simplex constraints, is preserved by the inverse. -/
def toSupported (point : NormalizedAssignment rows denominator) : SupportedAssignment rows denominator where
  values := fun i => SignedRatio.mul (positiveInverse point.scale point.scale_positive) (point.masses i)
  feasible := (homogenizeRows_unscaled_iff rows point.masses point.scale point.scale_positive).mp point.spec.1
  positive := positive_of_equiv point.decoded_evidence (inverse_positive point.scale point.scale_positive)
  bounded := (SignedRatio.le_congr point.decoded_evidence (SignedRatio.equiv_refl _)).mpr
    ((inverse_le_one_iff point.scale point.scale_positive).mpr point.spec.2.2)

end NormalizedAssignment

namespace SupportedAssignment

variable {rows : List (Inequality variables)} {denominator : Fin variables → Int}

def evidence (source : SupportedAssignment rows denominator) : SignedRatio := dot variables denominator source.values

def conditionalValue (source : SupportedAssignment rows denominator) (numerator : Fin variables → Int) : SignedRatio :=
  SignedRatio.mul (positiveInverse source.evidence source.positive) (dot variables numerator source.values)

/-- Transfer the fraction to independently proved evidence and joint-event
values. The actual evidence positivity remains an explicit premise. -/
theorem conditionalValue_congr (source : SupportedAssignment rows denominator) (numerator : Fin variables → Int)
    (evidence joint : SignedRatio) (positive : 0 < evidence.num)
    (sameEvidence : SignedRatio.Equiv source.evidence evidence)
    (sameJoint : SignedRatio.Equiv (dot variables numerator source.values) joint) :
    SignedRatio.Equiv (source.conditionalValue numerator) (SignedRatio.mul (positiveInverse evidence positive) joint) :=
  SignedRatio.mul_congr (inverse_congr sameEvidence source.positive positive) sameJoint

/-- Every supported original point supplies an explicit normalized point.
No search for a positive-evidence witness is performed in this constructor. -/
def normalize (source : SupportedAssignment rows denominator) : NormalizedAssignment rows denominator where
  values := extend (fun i => SignedRatio.mul (positiveInverse source.evidence source.positive) (source.values i))
    (positiveInverse source.evidence source.positive)
  feasible := (normalizedRows_iff rows denominator _ _).mpr
    ⟨(homogenizeRows_scaled_iff rows source.values _ (inverse_positive source.evidence source.positive)).mpr source.feasible,
      SignedRatio.equiv_trans (dot_mul_values variables denominator source.values _)
        (SignedRatio.equiv_trans (SignedRatio.mul_comm _ _) (mul_positiveInverse source.evidence source.positive)),
      (one_le_inverse_iff source.evidence source.positive).mpr source.bounded⟩

theorem normalize_response (source : SupportedAssignment rows denominator) (numerator : Fin variables → Int) :
    SignedRatio.Equiv (dot variables numerator source.normalize.masses) (source.conditionalValue numerator) := by
  change SignedRatio.Equiv
    (dot variables numerator (fun i => (extend (fun j => SignedRatio.mul (positiveInverse source.evidence source.positive)
      (source.values j)) (positiveInverse source.evidence source.positive)) i.castSucc)) _
  simp only [extend_castSucc]
  exact dot_mul_values variables numerator source.values _

end SupportedAssignment

namespace NormalizedAssignment

variable {rows : List (Inequality variables)} {denominator : Fin variables → Int}

/-- Every numerator response is preserved when decoding an arbitrary linear
solution. This supplies the objective bridge needed for sharp endpoint laws. -/
theorem toSupported_response (point : NormalizedAssignment rows denominator) (numerator : Fin variables → Int) :
    SignedRatio.Equiv (point.toSupported.conditionalValue numerator) (dot variables numerator point.masses) := by
  have reciprocal : SignedRatio.Equiv (positiveInverse point.toSupported.evidence point.toSupported.positive) point.scale :=
    SignedRatio.equiv_trans
      (inverse_congr point.decoded_evidence point.toSupported.positive (inverse_positive point.scale point.scale_positive))
      (inverse_inverse point.scale point.scale_positive)
  exact SignedRatio.equiv_trans
    (SignedRatio.mul_congr reciprocal (dot_mul_values variables numerator point.masses _))
    (rescale_unscale point.scale point.scale_positive _)

/-- Normalization cannot assign a conditional value to an identically null
denominator, regardless of the other supplied rows or rational coordinates. -/
theorem zero_denominator_impossible (point : NormalizedAssignment rows (fun _ => 0)) : False := by
  have impossible : SignedRatio.Equiv SignedRatio.zero SignedRatio.one :=
    SignedRatio.equiv_trans (SignedRatio.equiv_symm (dot_zero variables point.masses)) point.spec.2.1
  exact (by decide +kernel : ¬ SignedRatio.Equiv SignedRatio.zero SignedRatio.one) impossible

end NormalizedAssignment

end Thesis.Probability.Distros.RationalLinear.Conditional
