import Thesis.Probability.FiniteBooleanCovariance
import Thesis.Probability.FiniteProductBlocks
import Thesis.Probability.FiniteBooleanBasis

namespace Thesis
namespace Probability
namespace FiniteBooleanInteraction

open FiniteProduct

/-!
# A character gap separates the complete original outcome cylinder

The two-copy covariance theorem concerns homogeneous characters.  A query
instead asks for the joint event of *all* its outcome coordinates.  Replacing
that event with one coordinate would not implement the original query.

Here the exact false-valued outcome indicator is expanded into every subset
character, with a positive explicit finite-product scale.  The subset support
is repetition-free: off-outcome coordinates have only their false choice.
After summing over the unchanged conditioning cylinder, the scaled outcome-
event covariance is the sum of all those complete character covariances.

All summands are nonnegative under the proved positive interaction model,
so one explicitly supplied strict subset character makes the *full outcome*
covariance strictly positive.  The strictness constructor can use the actual
odd direction and matching interaction selection from the two-copy theorem;
it does not assume a positive event gap or add a matched-evidence premise.

These are exact finite integer identities before probability normalization.
An SCM application must still connect the weights and phases to its actual
likelihood and construct the parity data from the required active path.
Neither that graph coverage nor universal completeness is asserted here.
-/

/-- One actual coordinate is a homogeneous phase on the complete cube. -/
def coordinatePhase (count : Nat) (coordinate : Fin count) : HomogeneousPhase count where
  value := fun sample => sample coordinate
  at_zero := rfl
  xor_additive := fun _ _ => rfl

/-- The character of one supplied subset of outcome coordinates. -/
def maskPhase (count : Nat) (mask : Fin count -> Bool) : HomogeneousPhase count :=
  selectedPhase count count mask (coordinatePhase count)

/-- The actual coefficient of an outcome-subset character at a supplied
coordinate direction is its literal mask bit.  This applies to any dimension
and mask, including fixed coordinates, without enumerating a concrete cube. -/
theorem maskPhase_basis (count : Nat) (mask : Fin count -> Bool) (coordinate : Fin count) :
    (maskPhase count mask).value (basisAssignment count coordinate) = mask coordinate := by
  rw [maskPhase, selectedPhase_value_eq_foldl]
  exact basisAssignment_masked_foldl count coordinate mask

/-- Every true outcome coordinate permits both subset-mask choices; every
other coordinate permits only false.  This avoids a repeated-mask factor
which would arise by masking an unrestricted cube after enumeration. -/
def outcomeMasks (count : Nat) (outcome : Fin count -> Bool) : List (Fin count -> Bool) :=
  falseCylinderEnumeration count (fun index => !(outcome index))

/-- Literal positive scale of the outcome-indicator expansion.  It has a
factor two exactly at each original outcome coordinate, and unit elsewhere.
No external cardinality or probability denominator is substituted for it. -/
def cylinderScale (count : Nat) (outcome : Fin count -> Bool) : Nat :=
  natProduct count (fun index => if outcome index then 2 else 1)

theorem cylinderScale_positive (count : Nat) (outcome : Fin count -> Bool) :
    0 < cylinderScale count outcome := by
  apply natProduct_positive
  intro index
  cases outcome index <;> decide

/-- Exact full-subset expansion of the outcome indicator.  Its value is
the positive scale on the whole requested false cylinder and zero at every
conflicting sample; empty and overlapping outcome/conditioning sets are valid. -/
theorem outcome_character_sum (count : Nat) (outcome sample : Fin count -> Bool) :
    ((outcomeMasks count outcome).map (fun mask =>
      FiniteProbRecord.characterSign ((maskPhase count mask).value sample))).sum =
      if falseCylinder count outcome sample then (cylinderScale count outcome : Int) else 0 := by
  have expanded : ((outcomeMasks count outcome).map (fun mask =>
      FiniteProbRecord.characterSign ((maskPhase count mask).value sample))).sum =
      iProduct count (fun index => if outcome index then
        1 + FiniteProbRecord.characterSign (sample index) else 1) := by
    simp only [maskPhase, selectedPhase_sign_product, coordinatePhase]
    unfold outcomeMasks falseCylinderEnumeration
    rw [← iProduct_finite_sum count (fun _ => Bool)
      (falseCylinderChoices count (fun index => !(outcome index)))
      (fun index picked => if picked then FiniteProbRecord.characterSign (sample index) else 1)]
    apply iProduct_congr count
    intro index
    cases inside : outcome index <;>
      simp only [falseCylinderChoices, inside, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_false, if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
  rw [expanded]
  cases selected : falseCylinder count outcome sample with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases falseCylinder_conflict_of_false count outcome sample selected with ⟨index, inside, conflicting⟩
      apply iProduct_eq_zero count _ index
      rw [inside, conflicting]
      rfl
  | true =>
      simp only [if_true]
      unfold cylinderScale
      rw [← iProduct_nat]
      apply iProduct_congr count
      intro index
      cases inside : outcome index with
      | false => rfl
      | true =>
          rw [(falseCylinder_eq_true_iff count outcome sample).mp selected index inside]
          rfl

private theorem sum_filter_scaled (values : List α) (event : α -> Bool) (term : α -> Int) (scale : Int) :
    scale * ((values.filter event).map term).sum =
      (values.map (fun value => term value * (if event value then scale else 0))).sum := by
  induction values with
  | nil => exact Int.mul_zero scale
  | cons value rest inductionHypothesis =>
      cases selected : event value with
      | false => simp only [List.filter_cons, selected, Bool.false_eq_true, if_false,
          List.map_cons, List.sum_cons, Int.mul_zero, Int.zero_add, inductionHypothesis]
      | true => simp only [List.filter_cons, selected, if_true, List.map_cons,
          List.sum_cons, Int.mul_add, inductionHypothesis]; rw [Int.mul_comm scale (term value)]

/-- Expand a complete original-outcome event sum against any integer
integrand and any supplied assignment list.  All list occurrences are kept;
the subset sum is interchanged only after the literal indicator identity. -/
theorem scaled_cylinder_sum (count : Nat) (outcome : Fin count -> Bool)
    (values : List (Fin count -> Bool)) (term : (Fin count -> Bool) -> Int) :
    (cylinderScale count outcome : Int) * ((values.filter (falseCylinder count outcome)).map term).sum =
      ((outcomeMasks count outcome).map (fun mask =>
        (values.map (fun sample => term sample *
          FiniteProbRecord.characterSign ((maskPhase count mask).value sample))).sum)).sum := by
  rw [sum_filter_scaled]
  have rows : (values.map (fun sample => term sample *
      (if falseCylinder count outcome sample then (cylinderScale count outcome : Int) else 0))).sum =
      (values.map (fun sample => ((outcomeMasks count outcome).map (fun mask =>
        term sample * FiniteProbRecord.characterSign ((maskPhase count mask).value sample))).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro sample _listed
    rw [FiniteSupportedSum.sum_mul_left, outcome_character_sum]
  rw [rows, FiniteSupportedSum.sum_swap]

/-- The full outcome-event moment of a supplied homogeneous character on
the unchanged conditioning support.  Every requested outcome is fixed, not
only the endpoint of a selected path. -/
def cylinderMoment (count factors : Nat) (fixed outcome : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) : Int :=
  (((falseCylinderEnumeration count fixed).filter (falseCylinder count outcome)).map (fun sample =>
    weight count factors capacity amplitude phases sample *
      FiniteProbRecord.characterSign (character.value sample))).sum

private theorem cylinder_union_perm_filter (count : Nat) (fixed outcome : Fin count -> Bool) :
    (falseCylinderEnumeration count (fun index => fixed index || outcome index)).Perm
      ((falseCylinderEnumeration count fixed).filter (falseCylinder count outcome)) := by
  letI : DecidableEq (Fin count -> Bool) := assignmentDecidableEq count (fun _ => Bool) (fun _ => inferInstance)
  apply ConstructivePermutation.perm_of_nodup_mem_iff
  · exact falseCylinderEnumeration_nodup count _
  · exact List.Pairwise.filter _ (falseCylinderEnumeration_nodup count fixed)
  · intro sample
    rw [falseCylinderEnumeration_member_iff, List.mem_filter,
      falseCylinderEnumeration_member_iff, falseCylinder_eq_true_iff]
    constructor
    · intro consistent
      exact ⟨fun index selected => consistent index (by rw [selected]; rfl),
        fun index selected => consistent index (by rw [selected]; exact Bool.or_true _)⟩
    · intro consistent index selected
      rcases Bool.or_eq_true_iff.mp selected with earlier | later
      · exact consistent.1 index earlier
      · exact consistent.2 index later

/-- Projecting the full outcome on the unchanged conditioning support is
exactly the moment on their combined false cylinder.  The equality follows
from a complete support permutation, including overlap and empty masks;
it does not assume independence or remove a repeated assignment occurrence. -/
theorem cylinderMoment_eq_moment_union (count factors : Nat) (fixed outcome : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) :
    cylinderMoment count factors fixed outcome capacity amplitude phases character =
      moment count factors (fun index => fixed index || outcome index) capacity amplitude phases character := by
  exact FiniteSupportedSum.sum_eq_of_perm ((cylinder_union_perm_filter count fixed outcome).symm.map
    (fun sample => weight count factors capacity amplitude phases sample *
      FiniteProbRecord.characterSign (character.value sample)))

/-- Full outcome projection is exactly the scaled sum of its subset
character moments.  The character product is evaluated on the same samples
as the original weighted event, before any conditioning ratio is compared. -/
theorem scaled_cylinderMoment (count factors : Nat) (fixed outcome : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) :
    (cylinderScale count outcome : Int) * cylinderMoment count factors fixed outcome capacity amplitude phases character =
      ((outcomeMasks count outcome).map (fun mask =>
        moment count factors fixed capacity amplitude phases (character.xor (maskPhase count mask)))).sum := by
  unfold cylinderMoment
  rw [scaled_cylinder_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro mask _listed
  unfold moment
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample _selected
  simp only [HomogeneousPhase.xor, FiniteProbRecord.characterSign_xor]
  exact Int.mul_assoc _ _ _

/-- Covariance of one full outcome cylinder with one homogeneous
interaction.  This is the entire normalized-response cross-product; the
conditioning interaction term is retained even when it is nonzero. -/
def cylinderCovarianceNumerator (count factors : Nat) (fixed outcome : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) : Int :=
  cylinderMoment count factors fixed outcome capacity amplitude phases character *
      moment count factors fixed capacity amplitude phases (HomogeneousPhase.unit count) -
    moment count factors fixed capacity amplitude phases character *
      cylinderMoment count factors fixed outcome capacity amplitude phases (HomogeneousPhase.unit count)

private theorem sum_mul_right (values : List α) (term : α -> Int) (factor : Int) :
    (values.map (fun value => term value * factor)).sum = (values.map term).sum * factor := by
  have rows := List.map_congr_left (l := values) (fun value _listed => Int.mul_comm (term value) factor)
  rw [rows, FiniteSupportedSum.sum_mul_left, Int.mul_comm]

private theorem sum_sub (values : List α) (left right : α -> Int) :
    (values.map (fun value => left value - right value)).sum =
      (values.map left).sum - (values.map right).sum := by
  simp only [Int.sub_eq_add_neg]
  rw [FiniteSupportedSum.sum_add, FiniteSupportedSum.sum_neg]

/-- The exact full-event covariance is a positively scaled sum of *all*
outcome-subset covariances.  There is no discarded remainder which could
cancel the strict contribution of a selected outcome character. -/
theorem scaled_cylinderCovarianceNumerator (count factors : Nat) (fixed outcome : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) :
    (cylinderScale count outcome : Int) *
        cylinderCovarianceNumerator count factors fixed outcome capacity amplitude phases character =
      ((outcomeMasks count outcome).map (fun mask =>
        covarianceNumerator count factors fixed capacity amplitude phases character (maskPhase count mask))).sum := by
  unfold cylinderCovarianceNumerator
  rw [Int.mul_sub]
  have regroupFirst (scale first second : Int) : scale * (first * second) = (scale * first) * second := by ac_rfl
  have regroupSecond (scale first second : Int) : scale * (first * second) = first * (scale * second) := by ac_rfl
  rw [regroupFirst, regroupSecond, scaled_cylinderMoment, scaled_cylinderMoment,
    ← sum_mul_right, ← FiniteSupportedSum.sum_mul_left, ← sum_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro mask _listed
  simp only [covarianceNumerator, moment, HomogeneousPhase.unit, HomogeneousPhase.xor, Bool.false_xor]

private theorem positive_scale_of_positive_product (scale value : Int)
    (scalePositive : 0 < scale) (productPositive : 0 < scale * value) : 0 < value := by
  by_cases positive : 0 < value
  · exact positive
  · have nonpositive : value <= 0 := by omega
    have opposite : 0 <= scale * (-value) := Int.mul_nonneg (Int.le_of_lt scalePositive) (by omega)
    rw [Int.mul_neg] at opposite
    omega

/-- A strict complete covariance for one explicitly listed outcome subset
separates the full original outcome event.  Other outcome coordinates are
not removed: their entire nonnegative subset expansion remains in the sum. -/
theorem cylinderCovarianceNumerator_positive_of_covariance
    (count factors : Nat) (fixed outcome : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index)
    (mask : Fin count -> Bool) (listed : mask ∈ outcomeMasks count outcome)
    (strict : 0 < covarianceNumerator count factors fixed capacity amplitude phases character (maskPhase count mask)) :
    0 < cylinderCovarianceNumerator count factors fixed outcome capacity amplitude phases character := by
  have positive := FiniteSupportedSum.sum_pos_of_mem (outcomeMasks count outcome)
    (fun mask => covarianceNumerator count factors fixed capacity amplitude phases character (maskPhase count mask))
    (fun mask _listed => covarianceNumerator_nonneg count factors fixed capacity amplitude phases
      character (maskPhase count mask) amplitudes_nonneg room) mask listed strict
  rw [← scaled_cylinderCovarianceNumerator] at positive
  have scalePositive : (0 : Int) < cylinderScale count outcome := by
    have := cylinderScale_positive count outcome
    omega
  exact positive_scale_of_positive_product _ _ scalePositive positive

/-- Full outcome-event strictness from the explicit path-facing parity
data: an odd cylinder direction and an even, positive interaction selection
whose complete character matches the small/outcome-subset character.
The theorem leaves no unproved weighted gap or positive integral premise. -/
theorem cylinderCovarianceNumerator_positive_of_selected_phase
    (count factors : Nat) (fixed outcome : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index)
    (mask : Fin count -> Bool) (maskListed : mask ∈ outcomeMasks count outcome)
    (direction : Fin count -> Bool) (directionListed : direction ∈ falseCylinderEnumeration count fixed)
    (character_odd : character.value direction = true) (outcome_odd : (maskPhase count mask).value direction = true)
    (selected : Fin factors -> Bool)
    (selected_even : forall index, selected index = true -> (phases index).value direction = false)
    (selected_positive : forall index, selected index = true -> 0 < amplitude index)
    (matching : forall sample, sample ∈ falseCylinderEnumeration count fixed ->
      (character.xor (maskPhase count mask)).value sample =
        (selectedPhase count factors selected phases).value sample) :
    0 < cylinderCovarianceNumerator count factors fixed outcome capacity amplitude phases character :=
  cylinderCovarianceNumerator_positive_of_covariance count factors fixed outcome capacity amplitude phases
    character amplitudes_nonneg room mask maskListed
    (covarianceNumerator_positive_of_selected_phase count factors fixed capacity amplitude phases
      character (maskPhase count mask) amplitudes_nonneg room direction directionListed character_odd outcome_odd
      selected selected_even selected_positive matching)

end FiniteBooleanInteraction
end Probability
end Thesis
