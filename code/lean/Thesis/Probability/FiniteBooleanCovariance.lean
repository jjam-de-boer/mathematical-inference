import Thesis.Probability.FiniteBooleanInteraction

namespace Thesis
namespace Probability
namespace FiniteBooleanInteraction

open FiniteProduct

/-!
# Complete two-copy covariance identities for Boolean interactions

A conditional response is a normalized correlation, not a first character
moment.  Two positive first moments can cancel in its cross-product.  Here
the covariance numerator is rewritten using two copies of the *same complete*
false-cylinder support and their explicit XOR difference.

XOR translation permutes this support only when the supplied direction is
itself in the cylinder.  The proof verifies that condition, nonrepetition
and the actual inverse before changing variables.  Every paired weight is
the product of the original two weights, with no newly assumed coupling.

The paired-row theorem expresses its inner character sum with nonnegative
coefficients.  The remaining two sign differences are either zero or four.
Thus all complete homogeneous-character covariance numerators are
nonnegative.  A strictly positive inner sum at an explicitly supplied odd
direction gives strict separation.  Constructing such a direction from an
arbitrary active path is a separate graph obligation, not inferred here
from one positive assignment or from the absence of a separating cut.
-/

/-- Unnormalized covariance of two complete character observables.  The
ordinary partition factor is the moment of the unit character, so no actual
probability denominator or potentially zero evidence mass is divided out. -/
def covarianceNumerator (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (left right : HomogeneousPhase count) : Int :=
  moment count factors fixed capacity amplitude phases (left.xor right) *
      moment count factors fixed capacity amplitude phases (HomogeneousPhase.unit count) -
    moment count factors fixed capacity amplitude phases left *
      moment count factors fixed capacity amplitude phases right

private def doubleSum (values : List α) (term : α -> α -> Int) : Int :=
  (values.map (fun first => (values.map (term first)).sum)).sum

private theorem doubleSum_congr (values : List α) (left right : α -> α -> Int)
    (same : forall first, first ∈ values -> forall second, second ∈ values ->
      left first second = right first second) : doubleSum values left = doubleSum values right := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro first listed
  apply congrArg List.sum
  exact List.map_congr_left (same first listed)

private theorem sum_mul_right (values : List α) (term : α -> Int) (factor : Int) :
    (values.map (fun value => term value * factor)).sum = (values.map term).sum * factor := by
  have rows := List.map_congr_left (l := values) (fun value _listed => Int.mul_comm (term value) factor)
  rw [rows, FiniteSupportedSum.sum_mul_left, Int.mul_comm]

private theorem sum_sub (values : List α) (left right : α -> Int) :
    (values.map (fun value => left value - right value)).sum =
      (values.map left).sum - (values.map right).sum := by
  simp only [Int.sub_eq_add_neg]
  rw [FiniteSupportedSum.sum_add, FiniteSupportedSum.sum_neg]

private theorem doubleSum_add (values : List α) (left right : α -> α -> Int) :
    doubleSum values (fun first second => left first second + right first second) =
      doubleSum values left + doubleSum values right := by
  unfold doubleSum
  simp only [FiniteSupportedSum.sum_add]

private theorem doubleSum_sub (values : List α) (left right : α -> α -> Int) :
    doubleSum values (fun first second => left first second - right first second) =
      doubleSum values left - doubleSum values right := by
  unfold doubleSum
  simp only [sum_sub]

private theorem doubleSum_rectangular (values : List α) (left right : α -> Int) :
    doubleSum values (fun first second => left first * right second) =
      (values.map left).sum * (values.map right).sum := by
  unfold doubleSum
  simp only [FiniteSupportedSum.sum_mul_left]
  exact sum_mul_right values left (values.map right).sum

private theorem row_polarization (firstWeight secondWeight : Int)
    (leftFirst leftSecond rightFirst rightSecond : Bool) :
    firstWeight * secondWeight *
        (FiniteProbRecord.characterSign leftFirst - FiniteProbRecord.characterSign leftSecond) *
        (FiniteProbRecord.characterSign rightFirst - FiniteProbRecord.characterSign rightSecond) =
      (firstWeight * FiniteProbRecord.characterSign (Bool.xor leftFirst rightFirst)) * secondWeight +
      firstWeight * (secondWeight * FiniteProbRecord.characterSign (Bool.xor leftSecond rightSecond)) -
      (firstWeight * FiniteProbRecord.characterSign leftFirst) *
        (secondWeight * FiniteProbRecord.characterSign rightSecond) -
      (firstWeight * FiniteProbRecord.characterSign rightFirst) *
        (secondWeight * FiniteProbRecord.characterSign leftSecond) := by
  cases leftFirst <;> cases leftSecond <;> cases rightFirst <;> cases rightSecond <;>
    simp [FiniteProbRecord.characterSign, Int.mul_neg, Int.neg_mul] <;> omega

private theorem polarization (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (left right : HomogeneousPhase count) :
    doubleSum (falseCylinderEnumeration count fixed) (fun first second =>
      weight count factors capacity amplitude phases first * weight count factors capacity amplitude phases second *
        (FiniteProbRecord.characterSign (left.value first) - FiniteProbRecord.characterSign (left.value second)) *
        (FiniteProbRecord.characterSign (right.value first) - FiniteProbRecord.characterSign (right.value second))) =
      2 * covarianceNumerator count factors fixed capacity amplitude phases left right := by
  rw [doubleSum_congr _ _ _ (fun first _listed second _selected => row_polarization _ _ _ _ _ _),
    doubleSum_sub, doubleSum_sub, doubleSum_add,
    doubleSum_rectangular, doubleSum_rectangular, doubleSum_rectangular, doubleSum_rectangular]
  change moment count factors fixed capacity amplitude phases (left.xor right) *
        ((falseCylinderEnumeration count fixed).map (weight count factors capacity amplitude phases)).sum +
      ((falseCylinderEnumeration count fixed).map (weight count factors capacity amplitude phases)).sum *
        moment count factors fixed capacity amplitude phases (left.xor right) -
      moment count factors fixed capacity amplitude phases left * moment count factors fixed capacity amplitude phases right -
      moment count factors fixed capacity amplitude phases right * moment count factors fixed capacity amplitude phases left = _
  have unitMoment : moment count factors fixed capacity amplitude phases (HomogeneousPhase.unit count) =
      ((falseCylinderEnumeration count fixed).map (weight count factors capacity amplitude phases)).sum := by
    simp only [moment, HomogeneousPhase.unit, FiniteProbRecord.characterSign,
      Bool.false_eq_true, if_false, Int.mul_one]
  rw [← unitMoment]
  unfold covarianceNumerator
  have commuteFirst := Int.mul_comm (moment count factors fixed capacity amplitude phases (HomogeneousPhase.unit count))
    (moment count factors fixed capacity amplitude phases (left.xor right))
  have commuteSecond := Int.mul_comm (moment count factors fixed capacity amplitude phases right)
    (moment count factors fixed capacity amplitude phases left)
  rw [commuteFirst, commuteSecond, Int.mul_sub, show (2 : Int) = 1 + 1 from rfl, Int.add_mul, Int.one_mul]
  omega

private theorem xor_comm (count : Nat) (first second : Fin count -> Bool) :
    xorAssignment count first second = xorAssignment count second first := by
  funext index
  exact Bool.xor_comm _ _

private theorem cylinder_xor_closed (count : Nat) (fixed first second : Fin count -> Bool)
    (firstListed : first ∈ falseCylinderEnumeration count fixed)
    (secondListed : second ∈ falseCylinderEnumeration count fixed) :
    xorAssignment count first second ∈ falseCylinderEnumeration count fixed := by
  apply (falseCylinderEnumeration_member_iff count fixed _).mpr
  intro index selected
  unfold xorAssignment
  rw [(falseCylinderEnumeration_member_iff count fixed first).mp firstListed index selected,
    (falseCylinderEnumeration_member_iff count fixed second).mp secondListed index selected]
  rfl

private theorem sum_translate (count : Nat) (fixed direction : Fin count -> Bool)
    (listed : direction ∈ falseCylinderEnumeration count fixed) (term : (Fin count -> Bool) -> Int) :
    ((falseCylinderEnumeration count fixed).map (fun sample => term (xorAssignment count sample direction))).sum =
      ((falseCylinderEnumeration count fixed).map term).sum := by
  let values := falseCylinderEnumeration count fixed
  let shift := fun sample => xorAssignment count sample direction
  letI : DecidableEq (Fin count -> Bool) := assignmentDecidableEq count (fun _ => Bool) (fun _ => inferInstance)
  have inverse := xorAssignment_involutive count direction
  have closed : forall sample, sample ∈ values -> shift sample ∈ values :=
    fun sample member => cylinder_xor_closed count fixed sample direction member listed
  have injective : forall first, first ∈ values -> forall second, second ∈ values ->
      shift first = shift second -> first = second := by
    intro first _firstListed second _secondListed same
    exact (inverse first).symm.trans ((congrArg shift same).trans (inverse second))
  have members : forall sample, sample ∈ values.map shift ↔ sample ∈ values := by
    intro sample
    constructor
    · intro member
      rcases List.mem_map.mp member with ⟨old, member, same⟩
      exact same ▸ closed old member
    · intro member
      exact List.mem_map.mpr ⟨shift sample, closed sample member, inverse sample⟩
  have permutation := ConstructivePermutation.perm_of_nodup_mem_iff (values.map shift) values
    (ConstructivePermutation.nodup_map_of_injective_on shift values injective (falseCylinderEnumeration_nodup count fixed))
    (falseCylinderEnumeration_nodup count fixed) members
  simpa only [List.map_map, Function.comp_def] using FiniteSupportedSum.sum_eq_of_perm (permutation.map term)

/-- One actual inner two-copy character sum.  The supplied direction is
kept as data; positivity is a separate theorem, not assumed by this definition. -/
def pairedMoment (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) (direction : Fin count -> Bool) : Int :=
  ((falseCylinderEnumeration count fixed).map (fun sample =>
    weight count factors capacity amplitude phases sample *
      weight count factors capacity amplitude phases (xorAssignment count sample direction) *
      FiniteProbRecord.characterSign (character.value sample))).sum

private theorem shifted_row (count factors : Nat) (capacity amplitude : Fin factors -> Int)
    (phases : Fin factors -> HomogeneousPhase count) (left right : HomogeneousPhase count)
    (sample direction : Fin count -> Bool) :
    weight count factors capacity amplitude phases sample *
        weight count factors capacity amplitude phases (xorAssignment count sample direction) *
        (FiniteProbRecord.characterSign (left.value sample) -
          FiniteProbRecord.characterSign (left.value (xorAssignment count sample direction))) *
        (FiniteProbRecord.characterSign (right.value sample) -
          FiniteProbRecord.characterSign (right.value (xorAssignment count sample direction))) =
      (1 - FiniteProbRecord.characterSign (left.value direction)) *
        (1 - FiniteProbRecord.characterSign (right.value direction)) *
        (weight count factors capacity amplitude phases sample *
          weight count factors capacity amplitude phases (xorAssignment count sample direction) *
          FiniteProbRecord.characterSign ((left.xor right).value sample)) := by
  rw [left.xor_additive, right.xor_additive]
  simp only [HomogeneousPhase.xor, FiniteProbRecord.characterSign_xor]
  have factor (sign change : Int) : sign - sign * change = sign * (1 - change) := by
    rw [Int.mul_sub, Int.mul_one]
  rw [factor, factor]
  ac_rfl

/-- Exact covariance polarization followed by a verified XOR change of
variables.  Every direction and sample belongs to the unchanged complete
conditioning cylinder.  The factor two is retained as an integer equality. -/
theorem covarianceNumerator_two_copy (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (left right : HomogeneousPhase count) :
    2 * covarianceNumerator count factors fixed capacity amplitude phases left right =
      ((falseCylinderEnumeration count fixed).map (fun direction =>
        (1 - FiniteProbRecord.characterSign (left.value direction)) *
          (1 - FiniteProbRecord.characterSign (right.value direction)) *
          pairedMoment count factors fixed capacity amplitude phases (left.xor right) direction)).sum := by
  rw [← polarization]
  let term := fun first second => weight count factors capacity amplitude phases first *
    weight count factors capacity amplitude phases second *
      (FiniteProbRecord.characterSign (left.value first) - FiniteProbRecord.characterSign (left.value second)) *
      (FiniteProbRecord.characterSign (right.value first) - FiniteProbRecord.characterSign (right.value second))
  have reindexed : doubleSum (falseCylinderEnumeration count fixed) term =
      doubleSum (falseCylinderEnumeration count fixed) (fun first direction => term first (xorAssignment count first direction)) := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro first listed
    have translated := (sum_translate count fixed first listed (term first)).symm
    simpa only [xor_comm count first] using translated
  change doubleSum (falseCylinderEnumeration count fixed) term = _
  rw [reindexed]
  unfold doubleSum
  rw [FiniteSupportedSum.sum_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro direction _listed
  unfold pairedMoment
  rw [← FiniteSupportedSum.sum_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample _selected
  exact shifted_row count factors capacity amplitude phases left right sample direction

/-- Complete homogeneous-character covariances are nonnegative under
positive-room, nonnegative-amplitude interactions.  The proof sums every
paired direction; it does not infer correlation from positive first moments. -/
theorem covarianceNumerator_nonneg (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (left right : HomogeneousPhase count) (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index) :
    0 <= covarianceNumerator count factors fixed capacity amplitude phases left right := by
  have nonnegative : 0 <= ((falseCylinderEnumeration count fixed).map (fun direction =>
      (1 - FiniteProbRecord.characterSign (left.value direction)) *
        (1 - FiniteProbRecord.characterSign (right.value direction)) *
        pairedMoment count factors fixed capacity amplitude phases (left.xor right) direction)).sum := by
    apply FiniteSupportedSum.sum_nonneg
    intro direction _listed
    have inner := pairedMoment_nonneg count factors fixed capacity amplitude phases
      (left.xor right) direction amplitudes_nonneg room
    have signNonneg (bit : Bool) : 0 <= 1 - FiniteProbRecord.characterSign bit := by
      cases bit <;> decide
    exact Int.mul_nonneg (Int.mul_nonneg (signNonneg _) (signNonneg _)) inner
  rw [← covarianceNumerator_two_copy] at nonnegative
  omega

/-- An explicitly supplied cylinder direction that flips both observables
and has a positive complete paired moment certifies strict covariance.
Every other direction is accounted for by the preceding nonnegativity proof. -/
theorem covarianceNumerator_positive_of_pairedMoment
    (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (left right : HomogeneousPhase count) (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index)
    (direction : Fin count -> Bool) (listed : direction ∈ falseCylinderEnumeration count fixed)
    (left_odd : left.value direction = true) (right_odd : right.value direction = true)
    (inner_positive : 0 < pairedMoment count factors fixed capacity amplitude phases (left.xor right) direction) :
    0 < covarianceNumerator count factors fixed capacity amplitude phases left right := by
  have positive : 0 < ((falseCylinderEnumeration count fixed).map (fun change =>
      (1 - FiniteProbRecord.characterSign (left.value change)) *
        (1 - FiniteProbRecord.characterSign (right.value change)) *
        pairedMoment count factors fixed capacity amplitude phases (left.xor right) change)).sum := by
    refine FiniteSupportedSum.sum_pos_of_mem _ _ ?_ direction listed ?_
    · intro change _listed
      have inner := pairedMoment_nonneg count factors fixed capacity amplitude phases
        (left.xor right) change amplitudes_nonneg room
      have signNonneg (bit : Bool) : 0 <= 1 - FiniteProbRecord.characterSign bit := by
        cases bit <;> decide
      exact Int.mul_nonneg (Int.mul_nonneg (signNonneg _) (signNonneg _)) inner
    · simp only [left_odd, right_odd, FiniteProbRecord.characterSign, if_true]
      change 0 < 4 * pairedMoment count factors fixed capacity amplitude phases (left.xor right) direction
      omega
  rw [← covarianceNumerator_two_copy] at positive
  omega

/-- A fully explicit interaction selection supplies the strict two-copy
witness.  Each selected row is even on the direction, has positive original
amplitude and contributes to the matching character on the entire cylinder.
Thus no positive paired integral is left as an unexplained premise.

An application to active paths must construct this direction and selection
using its legitimate local phases.  The theorem permits arbitrary numbers
of factors, repeated phases and extra unselected interactions, but does not
assert that every graph path automatically supplies the required data. -/
theorem covarianceNumerator_positive_of_selected_phase
    (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (left right : HomogeneousPhase count) (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index)
    (direction : Fin count -> Bool) (listed : direction ∈ falseCylinderEnumeration count fixed)
    (left_odd : left.value direction = true) (right_odd : right.value direction = true)
    (selected : Fin factors -> Bool)
    (selected_even : forall index, selected index = true -> (phases index).value direction = false)
    (selected_positive : forall index, selected index = true -> 0 < amplitude index)
    (matching : forall sample, sample ∈ falseCylinderEnumeration count fixed ->
      (left.xor right).value sample = (selectedPhase count factors selected phases).value sample) :
    0 < covarianceNumerator count factors fixed capacity amplitude phases left right := by
  apply covarianceNumerator_positive_of_pairedMoment count factors fixed capacity amplitude phases
    left right amplitudes_nonneg room direction listed left_odd right_odd
  unfold pairedMoment
  simp only [weight_pair]
  apply moment_positive_of_selected_phase count factors fixed
    (pairedCapacity count factors capacity amplitude phases direction)
    (pairedAmplitude count factors capacity amplitude phases direction) phases (left.xor right) selected
    (pairedCapacity_positive count factors capacity amplitude phases direction amplitudes_nonneg room)
    (pairedAmplitude_nonneg count factors capacity amplitude phases direction amplitudes_nonneg room) ?_ matching
  intro index picked
  unfold pairedAmplitude
  rw [selected_even index picked]
  change 0 < 2 * capacity index * amplitude index
  have capacityPositive : 0 < capacity index := by
    have := amplitudes_nonneg index
    have := room index
    omega
  exact Int.mul_pos (Int.mul_pos (show (0 : Int) < 2 by decide) capacityPositive) (selected_positive index picked)

end FiniteBooleanInteraction
end Probability
end Thesis
