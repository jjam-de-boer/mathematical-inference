import Thesis.Probability.FiniteBooleanCharacter
import Thesis.Probability.FiniteBooleanTranslation

namespace Thesis
namespace Probability
namespace FiniteBooleanInteraction

open FiniteProduct

/-!
# Exact character moments under finite positive interaction products

The action-cut hedge likelihood is an ordinary background product multiplied
by one homogeneous character.  A conditional gap depends on correlations
under that background, not on the sign at one assignment.  This module keeps
the complete false-cylinder sum and every local interaction factor explicit.

Each phase carries its actual zero and XOR-additivity proofs.  Arbitrary
nonlinear local signals therefore cannot silently use the nonnegative
character theorem.  Capacity and amplitude coefficients are auxiliary
integers: the application must connect their product to its actual natural
likelihood and prove the needed coefficient inequalities.

The first moment inequality expands the last factor symbolically.  Both
resulting moments are again homogeneous characters, and nonnegative
coefficients preserve nonnegativity.  No concrete Boolean cube is reduced,
no infinite probability object is introduced, and no representative or
direction is selected from a propositional existence claim.
-/

/-- A homogeneous character phase on one explicit finite Boolean cube.
The proofs concern the supplied function, not a separately chosen linear
representation.  Its sign can be negative at individual assignments. -/
structure HomogeneousPhase (count : Nat) where
  value : (Fin count -> Bool) -> Bool
  at_zero : value (fun _ => false) = false
  xor_additive : forall left right,
    value (xorAssignment count left right) = Bool.xor (value left) (value right)

namespace HomogeneousPhase

/-- The unit character, useful for the ordinary background partition sum. -/
def unit (count : Nat) : HomogeneousPhase count where
  value := fun _ => false
  at_zero := rfl
  xor_additive := fun _ _ => rfl

/-- Product of two character signs, represented by XOR of their actual
phases.  Closure is proved by four Boolean case splits, not Prop excluded middle. -/
def xor {count : Nat} (left right : HomogeneousPhase count) : HomogeneousPhase count where
  value := fun sample => Bool.xor (left.value sample) (right.value sample)
  at_zero := by rw [left.at_zero, right.at_zero]; rfl
  xor_additive := by
    intro first second
    rw [left.xor_additive, right.xor_additive]
    cases left.value first <;> cases left.value second <;>
      cases right.value first <;> cases right.value second <;> rfl

end HomogeneousPhase

/-- Complete local-factor product.  Repeated or trivial phases remain
separate factors, as they do in the underlying row likelihood. -/
def weight (count factors : Nat) (capacity amplitude : Fin factors -> Int)
    (phases : Fin factors -> HomogeneousPhase count) (sample : Fin count -> Bool) : Int :=
  iProduct factors (fun index => capacity index + amplitude index *
    FiniteProbRecord.characterSign ((phases index).value sample))

/-- A full character-weighted background moment on the literal restricted
support.  The conditioning coordinates are fixed to false; nothing else is
masked out, duplicated or assumed uniform after weighting. -/
def moment (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) : Int :=
  ((falseCylinderEnumeration count fixed).map (fun sample =>
    weight count factors capacity amplitude phases sample *
      FiniteProbRecord.characterSign (character.value sample))).sum

/-- Exact one-factor expansion of the whole moment.  The second summand
keeps the last interaction by XORing it into the queried character; it is
not an omitted higher-order correction or a marginal approximation. -/
theorem moment_succ (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin (factors + 1) -> Int)
    (phases : Fin (factors + 1) -> HomogeneousPhase count) (character : HomogeneousPhase count) :
    moment count (factors + 1) fixed capacity amplitude phases character =
      capacity (Fin.last factors) * moment count factors fixed
        (fun index => capacity index.castSucc) (fun index => amplitude index.castSucc)
        (fun index => phases index.castSucc) character +
      amplitude (Fin.last factors) * moment count factors fixed
        (fun index => capacity index.castSucc) (fun index => amplitude index.castSucc)
        (fun index => phases index.castSucc) (character.xor (phases (Fin.last factors))) := by
  unfold moment
  rw [← FiniteSupportedSum.sum_mul_left, ← FiniteSupportedSum.sum_mul_left,
    ← FiniteSupportedSum.sum_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample _listed
  simp only [weight, iProduct, HomogeneousPhase.xor, FiniteProbRecord.characterSign_xor,
    Int.add_mul]
  ac_rfl

/-- All complete homogeneous moments are nonnegative when every local
capacity and interaction amplitude is nonnegative.  The weight itself need
not be normalized, and strict capacity room is not needed for this first
moment inequality.  Negative pointwise character values are still summed. -/
theorem moment_nonneg (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) (capacities_nonneg : forall index, 0 <= capacity index)
    (amplitudes_nonneg : forall index, 0 <= amplitude index) :
    0 <= moment count factors fixed capacity amplitude phases character := by
  induction factors generalizing character with
  | zero =>
      simpa only [moment, weight, iProduct, Int.one_mul] using
        falseCylinder_characterSum_nonneg count fixed character.value character.at_zero character.xor_additive
  | succ factors inductionHypothesis =>
      rw [moment_succ]
      exact Int.add_nonneg
        (Int.mul_nonneg (capacities_nonneg (Fin.last factors))
          (inductionHypothesis (fun index => capacity index.castSucc)
            (fun index => amplitude index.castSucc) (fun index => phases index.castSucc) character
            (fun index => capacities_nonneg index.castSucc) (fun index => amplitudes_nonneg index.castSucc)))
        (Int.mul_nonneg (amplitudes_nonneg (Fin.last factors))
          (inductionHypothesis (fun index => capacity index.castSucc)
            (fun index => amplitude index.castSucc) (fun index => phases index.castSucc)
            (character.xor (phases (Fin.last factors)))
            (fun index => capacities_nonneg index.castSucc) (fun index => amplitudes_nonneg index.castSucc)))

/-! ## Strictness from one explicit complete expansion selection -/

/-- The character contributed by an explicitly supplied interaction mask.
The recursion follows the same terminal-coordinate order as the actual
integer product; each selected phase occurs once and each omitted phase
contributes the unit.  This is data, not a selection from an existence proof. -/
def selectedPhase (count : Nat) : (factors : Nat) -> (Fin factors -> Bool) ->
    (Fin factors -> HomogeneousPhase count) -> HomogeneousPhase count
  | 0, _, _ => HomogeneousPhase.unit count
  | factors + 1, selected, phases =>
      (selectedPhase count factors (fun index => selected index.castSucc)
        (fun index => phases index.castSucc)).xor
          (if selected (Fin.last factors) then phases (Fin.last factors) else HomogeneousPhase.unit count)

/-- The sign of a supplied selected phase is exactly the product of its
selected local signs.  This symbolic identity keeps omitted factors equal
to one, rather than enumerating or masking a complete assignment support. -/
theorem selectedPhase_sign_product (count factors : Nat) (selected : Fin factors -> Bool)
    (phases : Fin factors -> HomogeneousPhase count) (sample : Fin count -> Bool) :
    FiniteProbRecord.characterSign ((selectedPhase count factors selected phases).value sample) =
      iProduct factors (fun index => if selected index then
        FiniteProbRecord.characterSign ((phases index).value sample) else 1) := by
  induction factors with
  | zero => rfl
  | succ factors inductionHypothesis =>
      rw [selectedPhase, iProduct]
      simp only [HomogeneousPhase.xor, FiniteProbRecord.characterSign_xor]
      rw [inductionHypothesis (fun index => selected index.castSucc) (fun index => phases index.castSucc)]
      cases picked : selected (Fin.last factors) with
      | false => simp only [Bool.false_eq_true, if_false, HomogeneousPhase.unit,
          FiniteProbRecord.characterSign, Int.mul_one, Int.one_mul]
      | true => simp only [if_true]; exact Int.mul_comm _ _

/-- One explicit expansion selection whose character matches the queried
one on the *entire* cylinder makes the complete moment positive.  Every
selected amplitude and every omitted capacity is positive, while all other
expansion terms are accounted for by homogeneous-moment nonnegativity.
Agreement at a single sample would not suffice for this theorem. -/
theorem moment_positive_of_selected_phase
    (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) (selected : Fin factors -> Bool)
    (capacities_positive : forall index, 0 < capacity index)
    (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (selected_positive : forall index, selected index = true -> 0 < amplitude index)
    (matching : forall sample, sample ∈ falseCylinderEnumeration count fixed ->
      character.value sample = (selectedPhase count factors selected phases).value sample) :
    0 < moment count factors fixed capacity amplitude phases character := by
  induction factors generalizing character with
  | zero =>
      have signs : forall sample, sample ∈ falseCylinderEnumeration count fixed ->
          FiniteProbRecord.characterSign (character.value sample) = 1 := by
        intro sample listed
        rw [matching sample listed]
        rfl
      let zeroSample : Fin count -> Bool := fun _ => false
      have zeroListed : zeroSample ∈ falseCylinderEnumeration count fixed :=
        (falseCylinderEnumeration_member_iff count fixed zeroSample).mpr (fun _ _ => rfl)
      unfold moment weight
      simp only [iProduct, Int.one_mul]
      apply FiniteSupportedSum.sum_pos_of_mem _ _
        (fun sample listed => by rw [signs sample listed]; decide) zeroSample zeroListed
      rw [signs zeroSample zeroListed]
      decide
  | succ factors inductionHypothesis =>
      have capacityPrefix := fun index : Fin factors => capacities_positive index.castSucc
      have amplitudePrefix := fun index : Fin factors => amplitudes_nonneg index.castSucc
      have selectedPrefix := fun index : Fin factors => selected_positive index.castSucc
      rw [moment_succ]
      cases picked : selected (Fin.last factors) with
      | false =>
          have prefixMatching : forall sample, sample ∈ falseCylinderEnumeration count fixed ->
              character.value sample = (selectedPhase count factors
                (fun index => selected index.castSucc) (fun index => phases index.castSucc)).value sample := by
            intro sample listed
            simpa only [selectedPhase, picked, Bool.false_eq_true, if_false,
              HomogeneousPhase.xor, HomogeneousPhase.unit, Bool.xor_false] using matching sample listed
          have chosen := inductionHypothesis (fun index => capacity index.castSucc)
            (fun index => amplitude index.castSucc) (fun index => phases index.castSucc) character
            (fun index => selected index.castSucc) capacityPrefix amplitudePrefix selectedPrefix prefixMatching
          have firstPositive := Int.mul_pos (capacities_positive (Fin.last factors)) chosen
          have other := Int.mul_nonneg (amplitudes_nonneg (Fin.last factors))
            (moment_nonneg count factors fixed (fun index => capacity index.castSucc)
              (fun index => amplitude index.castSucc) (fun index => phases index.castSucc)
              (character.xor (phases (Fin.last factors)))
              (fun index => Int.le_of_lt (capacityPrefix index)) amplitudePrefix)
          omega
      | true =>
          have prefixMatching : forall sample, sample ∈ falseCylinderEnumeration count fixed ->
              (character.xor (phases (Fin.last factors))).value sample = (selectedPhase count factors
                (fun index => selected index.castSucc) (fun index => phases index.castSucc)).value sample := by
            intro sample listed
            change Bool.xor (character.value sample) ((phases (Fin.last factors)).value sample) = _
            rw [matching sample listed]
            simp only [selectedPhase, picked, if_true, HomogeneousPhase.xor]
            cases (selectedPhase count factors (fun index => selected index.castSucc)
                (fun index => phases index.castSucc)).value sample <;>
              cases (phases (Fin.last factors)).value sample <;> rfl
          have chosen := inductionHypothesis (fun index => capacity index.castSucc)
            (fun index => amplitude index.castSucc) (fun index => phases index.castSucc)
            (character.xor (phases (Fin.last factors))) (fun index => selected index.castSucc)
            capacityPrefix amplitudePrefix selectedPrefix prefixMatching
          have secondPositive := Int.mul_pos (selected_positive (Fin.last factors) picked) chosen
          have other := Int.mul_nonneg (Int.le_of_lt (capacities_positive (Fin.last factors)))
            (moment_nonneg count factors fixed (fun index => capacity index.castSucc)
              (fun index => amplitude index.castSucc) (fun index => phases index.castSucc) character
              (fun index => Int.le_of_lt (capacityPrefix index)) amplitudePrefix)
          omega

/-! ## Two copies retain a nonnegative complete character expansion -/

/-- The constant coefficient when two actual interaction rows are paired
by a supplied XOR direction.  An odd direction removes the interaction and
leaves the exact difference of squares; an even direction keeps both biases. -/
def pairedCapacity (count factors : Nat) (capacity amplitude : Fin factors -> Int)
    (phases : Fin factors -> HomogeneousPhase count) (direction : Fin count -> Bool)
    (index : Fin factors) : Int :=
  if (phases index).value direction then
    capacity index * capacity index - amplitude index * amplitude index
  else capacity index * capacity index + amplitude index * amplitude index

/-- The interaction coefficient of the same paired row.  It is zero on an
odd direction and twice the original capacity-amplitude product otherwise. -/
def pairedAmplitude (count factors : Nat) (capacity amplitude : Fin factors -> Int)
    (phases : Fin factors -> HomogeneousPhase count) (direction : Fin count -> Bool)
    (index : Fin factors) : Int :=
  if (phases index).value direction then 0 else 2 * capacity index * amplitude index

private theorem row_pair (capacity amplitude : Int) (bit change : Bool) :
    (capacity + amplitude * FiniteProbRecord.characterSign bit) *
        (capacity + amplitude * FiniteProbRecord.characterSign (Bool.xor bit change)) =
      (if change then capacity * capacity - amplitude * amplitude
        else capacity * capacity + amplitude * amplitude) +
      (if change then 0 else 2 * capacity * amplitude) * FiniteProbRecord.characterSign bit := by
  have commute : amplitude * capacity = capacity * amplitude := Int.mul_comm _ _
  cases bit <;> cases change <;>
    simp only [Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      FiniteProbRecord.characterSign, Bool.false_eq_true, if_true, if_false,
      Int.mul_one, Int.mul_neg, Int.add_zero,
      Int.add_mul, Int.mul_add, Int.neg_mul,
      commute, show (2 : Int) = 1 + 1 from rfl, Int.one_mul] <;> omega

/-- Pairing two whole weights uses the exact paired row coefficients.
All interactions are retained, including trivial and repeated phases.
This identity is pointwise and does not assume cylinder membership. -/
theorem weight_pair (count factors : Nat) (capacity amplitude : Fin factors -> Int)
    (phases : Fin factors -> HomogeneousPhase count) (direction sample : Fin count -> Bool) :
    weight count factors capacity amplitude phases sample *
        weight count factors capacity amplitude phases (xorAssignment count sample direction) =
      weight count factors (pairedCapacity count factors capacity amplitude phases direction)
        (pairedAmplitude count factors capacity amplitude phases direction) phases sample := by
  unfold weight
  rw [← iProduct_mul]
  apply iProduct_congr factors
  intro index
  rw [(phases index).xor_additive]
  exact row_pair (capacity index) (amplitude index) ((phases index).value sample)
    ((phases index).value direction)

/-- Strict room in each original row makes every paired constant positive.
The odd-direction difference of squares is factored before applying order
reasoning; it is not silently replaced by a positive capacity. -/
theorem pairedCapacity_positive (count factors : Nat) (capacity amplitude : Fin factors -> Int)
    (phases : Fin factors -> HomogeneousPhase count) (direction : Fin count -> Bool)
    (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index) (index : Fin factors) :
    0 < pairedCapacity count factors capacity amplitude phases direction index := by
  have positive : 0 < capacity index := by have := amplitudes_nonneg index; have := room index; omega
  unfold pairedCapacity
  cases changed : (phases index).value direction with
  | false =>
      change 0 < capacity index * capacity index + amplitude index * amplitude index
      have squarePositive := Int.mul_pos positive positive
      have squareNonneg := Int.mul_nonneg (amplitudes_nonneg index) (amplitudes_nonneg index)
      omega
  | true =>
      change 0 < capacity index * capacity index - amplitude index * amplitude index
      have factored : capacity index * capacity index - amplitude index * amplitude index =
          (capacity index - amplitude index) * (capacity index + amplitude index) := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_add]
        have commute := Int.mul_comm (capacity index) (amplitude index)
        omega
      rw [factored]
      exact Int.mul_pos (by have := room index; omega) (by have := amplitudes_nonneg index; omega)

/-- The paired interaction coefficient is nonnegative, also when an odd
direction zeros it.  Strict capacity room is used only to establish the
original capacity's positive sign, not to cancel a row or character. -/
theorem pairedAmplitude_nonneg (count factors : Nat) (capacity amplitude : Fin factors -> Int)
    (phases : Fin factors -> HomogeneousPhase count) (direction : Fin count -> Bool)
    (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index) (index : Fin factors) :
    0 <= pairedAmplitude count factors capacity amplitude phases direction index := by
  have capacityNonneg : 0 <= capacity index := by have := amplitudes_nonneg index; have := room index; omega
  unfold pairedAmplitude
  cases changed : (phases index).value direction with
  | true => change (0 : Int) <= 0; exact Int.le_refl _
  | false =>
      change 0 <= 2 * capacity index * amplitude index
      exact Int.mul_nonneg
        (Int.mul_nonneg (show (0 : Int) <= 2 by decide) capacityNonneg) (amplitudes_nonneg index)

/-- A character moment against the product of two XOR-related *actual*
background weights is nonnegative on the complete false cylinder.  The
pointwise queried character may still change sign; the complete paired
expansion and homogeneous-character sum supply the inequality. -/
theorem pairedMoment_nonneg (count factors : Nat) (fixed : Fin count -> Bool)
    (capacity amplitude : Fin factors -> Int) (phases : Fin factors -> HomogeneousPhase count)
    (character : HomogeneousPhase count) (direction : Fin count -> Bool)
    (amplitudes_nonneg : forall index, 0 <= amplitude index)
    (room : forall index, amplitude index < capacity index) :
    0 <= ((falseCylinderEnumeration count fixed).map (fun sample =>
      weight count factors capacity amplitude phases sample *
        weight count factors capacity amplitude phases (xorAssignment count sample direction) *
        FiniteProbRecord.characterSign (character.value sample))).sum := by
  simp only [weight_pair]
  exact moment_nonneg count factors fixed
    (pairedCapacity count factors capacity amplitude phases direction)
    (pairedAmplitude count factors capacity amplitude phases direction) phases character
    (fun index => Int.le_of_lt (pairedCapacity_positive count factors capacity amplitude phases direction
      amplitudes_nonneg room index))
    (pairedAmplitude_nonneg count factors capacity amplitude phases direction amplitudes_nonneg room)

end FiniteBooleanInteraction
end Probability
end Thesis
