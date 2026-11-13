import Thesis.CausalTransport.HedgeChannelInterventional
import Thesis.CausalTransport.HedgeChannelUnderCoefficients

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Complete action-cut likelihoods as background products

The intervention expansion still lists every outside-small background mask.
For a general conditional-path argument, repeatedly unpacking that list is
unhelpful: the backgrounds jointly form an ordinary product of local row
factors.  This module proves that factorization for the *complete actual*
integrated likelihood, not for a proposed substitute polynomial.

After forcing the stored action seed, the left likelihood is the shared
prior mass times a capacity factor on the small forest and the full
background product off it.  The right-minus-left contribution has exactly
the same outside-small background product, multiplied by the full-small
coefficient and its observed/parent character.  All simultaneous background
interactions occur once in the finite product expansion.

Every row retains its actual intervention coefficient.  A forced conflict
therefore remains zero, and a channel chosen at a forced row also remains
zero.  Removing the canonical support filter is justified only by those
zero coefficients; no row capacity or positive mass is cancelled.

The formulas are symbolic in graph size and channel count.  In particular,
the enormous shared-source enumeration is never evaluated.  They apply to
arbitrary legal typed parent signals, so they can also be used separately at
each frozen shared-input environment.  A nonzero *normalized conditional*
gap along every required active path remains a separate obligation.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Literal local factors, including forced indicators -/

/-- The actual capacity or consistency-indicator coefficient at a row.
It is one at a matching forced row and zero at a conflicting forced row. -/
def capacityRowUnder (w : HedgeWitness G q) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (child : Fin S.count) : Int :=
  (rightTables w child).expansionCoefficientUnder (target child) (sample child) none

/-- The entire outside-small background row: the capacity term plus its
one amplitude-weighted typed parent character.  A forced row has no channel
term, so its factor is still the literal consistency indicator. -/
def backgroundRowUnder (w : HedgeWitness G q) (backgroundSignal : ParentSignal S)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (child : Fin S.count) : Int :=
  capacityRowUnder w target sample child +
    (rightTables w child).expansionCoefficientUnder (target child) (sample child)
      (some (backgroundChannel w child)) *
    FiniteProbRecord.characterSign
      (Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent)))

/-- Product of all ordinary background factors outside the small forest.
Inside-small coordinates contribute the unit, not an extra background row. -/
def outsideBackgroundProductUnder (w : HedgeWitness G q) (backgroundSignal : ParentSignal S)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) : Int :=
  FiniteProduct.iProduct S.count (fun child =>
    if w.small child then 1 else backgroundRowUnder w backgroundSignal target sample child)

/-- Product of the actual capacity coefficients at the small rows.  The
definition does not assume those rows are free or intervention-consistent. -/
def smallCapacityProductUnder (w : HedgeWitness G q) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) : Int :=
  FiniteProduct.iProduct S.count (fun child =>
    if w.small child then capacityRowUnder w target sample child else 1)

/-- Actual full-small amplitude product, before its one complete character.
Forcing any small row zeros this product, including at a consistent sample. -/
def smallAmplitudeProductUnder (w : HedgeWitness G q) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) : Int :=
  FiniteProduct.iProduct S.count (fun child => if w.small child then
    (rightTables w child).expansionCoefficientUnder (target child) (sample child)
      (some (smallChannel w)) else 1)

/-! ## Positivity belongs to the actual background, not the interaction -/

private theorem background_amplitude_eq (w : HedgeWitness G q) (child : Fin S.count) :
    (rightTables w child).amplitude (backgroundChannel w child) =
      HedgeChannelCoefficients.ordinaryAmplitude (channelCount w) S.count := by
  simp only [rightTables, HedgeChannelCoefficients.tables, BooleanChannelTable.ofCapacity,
    HedgeChannelCoefficients.rowExponent, rightAnchors, role_backgroundChannel]
  rfl

/-- Every free background factor is strictly positive, for every typed
signal and observed sample.  The power construction's amplitude is strictly
below its actual capacity; either possible character sign therefore leaves
positive mass.  This does not require the full-small interaction to be positive. -/
theorem backgroundRowUnder_positive_of_free (w : HedgeWitness G q)
    (backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (child : Fin S.count) (free : target child = none) :
    0 < backgroundRowUnder w backgroundSignal target sample child := by
  have room : (rightTables w child).amplitude (backgroundChannel w child) <
      (rightTables w child).capacity := by
    rw [background_amplitude_eq,
      show (rightTables w child).capacity = HedgeChannelCoefficients.capacity (channelCount w) S.count from
        HedgeChannelCoefficients.tables_capacity _ _ _ _ _ child]
    exact HedgeChannelCoefficients.ordinaryAmplitude_lt_capacity (channelCount w) S.count
  have roomInt : ((rightTables w child).amplitude (backgroundChannel w child) : Int) <
      ((rightTables w child).capacity : Int) := by omega
  have amplitudeNonneg := Int.natCast_nonneg ((rightTables w child).amplitude (backgroundChannel w child))
  unfold backgroundRowUnder capacityRowUnder
  rw [free]
  simp only [BooleanChannelTable.expansionCoefficientUnder]
  cases Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent)) <;>
    simp only [FiniteProbRecord.characterSign, Bool.false_eq_true, if_true, if_false,
      Int.mul_neg, Int.mul_one] <;> omega

/-- The outside-small row product has no negative row weights.  A forced
conflict may give zero; treating its consistency indicator as positive would
be incorrect, even though all free background rows have full support. -/
theorem backgroundRowUnder_nonneg (w : HedgeWitness G q)
    (backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (child : Fin S.count) :
    0 <= backgroundRowUnder w backgroundSignal target sample child := by
  cases forced : target child with
  | none => exact Int.le_of_lt (backgroundRowUnder_positive_of_free w backgroundSignal target sample child forced)
  | some fixed =>
      unfold backgroundRowUnder capacityRowUnder
      simp only [forced, BooleanChannelTable.expansionCoefficientUnder, Int.zero_mul, Int.add_zero]
      split <;> decide

private theorem iProduct_nonneg (n : Nat) (factors : Fin n -> Int)
    (nonnegative : forall index, 0 <= factors index) : 0 <= FiniteProduct.iProduct n factors := by
  induction n with
  | zero => change (0 : Int) <= 1; decide
  | succ n inductionHypothesis =>
      exact Int.mul_nonneg (nonnegative (Fin.last n))
        (inductionHypothesis (fun index => factors index.castSucc) (fun index => nonnegative index.castSucc))

/-- The complete outside-small background is nonnegative on every sample,
including conflicting forced samples.  The character perturbation is kept
separate and is not assigned this nonnegativity property. -/
theorem outsideBackgroundProductUnder_nonneg (w : HedgeWitness G q)
    (backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) :
    0 <= outsideBackgroundProductUnder w backgroundSignal target sample := by
  apply iProduct_nonneg
  intro child
  cases inside : w.small child with
  | true => change (0 : Int) <= 1; decide
  | false => exact backgroundRowUnder_nonneg w backgroundSignal target sample child

/-- A conflict at one forced outside-small row zeros the entire actual
background product.  Other rows and all shared-input signal values are kept;
only this row's literal consistency indicator supplies the zero factor. -/
theorem outsideBackgroundProductUnder_zero_of_conflict (w : HedgeWitness G q)
    (backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (child : Fin S.count) (fixed : Bool)
    (outsideSmall : w.small child = false) (forced : target child = some fixed)
    (conflicting : sample child ≠ fixed) :
    outsideBackgroundProductUnder w backgroundSignal target sample = 0 := by
  apply FiniteProduct.iProduct_eq_zero S.count _ child
  have different : fixed ≠ sample child := fun equal => conflicting equal.symm
  simp only [outsideSmall, Bool.false_eq_true, if_false, backgroundRowUnder,
    capacityRowUnder, forced, BooleanChannelTable.expansionCoefficientUnder,
    if_neg different, Int.zero_mul, Int.add_zero]

/-! ## Symbolic expansion of the complete mask list -/

private theorem mask_false_inside (nodes mask : NodeSet S)
    (subset : NodeSet.Subset mask (outside nodes)) (child : Fin S.count)
    (inside : nodes child = true) : mask child = false := by
  cases selected : mask child with
  | false => rfl
  | true =>
      have off := subset child selected
      simp only [outside, NodeSet.diff, NodeSet.full, inside, Bool.not_true,
        Bool.and_false] at off
      cases off

private theorem masked_sign_product (nodes : NodeSet S) (signal : ParentSignal S)
    (sample : S.binary.Assignment) :
    FiniteProduct.iProduct S.count (fun child => if nodes child then
      FiniteProbRecord.characterSign
        (Bool.xor (sample child) (signal child (fun parent _edge => sample parent))) else 1) =
      FiniteProbRecord.characterSign (signalPhase nodes signal sample) := by
  let bits := fun child => Bool.xor (sample child) (signal child (fun parent _edge => sample parent))
  have localSigns : (fun child => if nodes child then FiniteProbRecord.characterSign (bits child) else 1) =
      (fun child => FiniteProbRecord.characterSign (if nodes child then bits child else false)) := by
    funext child
    cases nodes child <;> rfl
  rw [localSigns, FiniteProduct.iProduct_characterSign]
  have phase := hedgeNodeXor_mask_of_subset nodes NodeSet.full (fun _ _ => rfl) bits
  rw [hedgeNodeXor, NodeSet.members_full] at phase
  exact congrArg FiniteProbRecord.characterSign phase

private theorem masks_product_expansion (nodes : NodeSet S) (low high : Fin S.count -> Int) :
    ((masks (outside nodes)).map (fun mask =>
      FiniteProduct.iProduct S.count (fun child => if mask child then high child else low child))).sum =
      FiniteProduct.iProduct S.count (fun child => if nodes child then low child else low child + high child) := by
  unfold masks
  rw [← FiniteProduct.iProduct_finite_sum S.count (fun _ => Bool)
    (maskChoices (outside nodes)) (fun child picked => if picked then high child else low child)]
  apply FiniteProduct.iProduct_congr S.count
  intro child
  cases inside : nodes child <;>
    simp only [maskChoices, outside, NodeSet.diff, NodeSet.full, inside,
      Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_eq_true,
      if_false, if_true, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Int.add_zero]

private theorem coefficient_zero_of_disallowed (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin channels))
    (disallowed : HedgeChannelTable.choiceAllowedUnder target choice = false) :
    HedgeChannelTable.choiceCoefficient tables target sample choice = 0 := by
  by_cases zero : HedgeChannelTable.choiceCoefficient tables target sample choice = 0
  · exact zero
  · have allowed : HedgeChannelTable.choiceAllowedUnder target choice = true := by
      apply List.all_eq_true.mpr
      intro child _listed
      cases forced : target child with
      | none => rfl
      | some fixed =>
          cases picked : choice child with
          | none => rfl
          | some channel =>
              apply False.elim
              apply zero
              apply FiniteProduct.iProduct_eq_zero S.count _ child
              simp only [BooleanChannelTable.expansionCoefficientUnder, forced, picked]
    exact False.elim (Bool.false_ne_true (disallowed.symm.trans allowed))

private def canonicalRow (w : HedgeWitness G q)
    (tables : Fin S.count -> BooleanChannelTable (Fin (channelCount w)))
    (forest : NodeSet S) (channel : Fin (channelCount w))
    (signal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (mask : NodeSet S) (child : Fin S.count) : Int :=
  (tables child).expansionCoefficientUnder (target child) (sample child)
      (fullChoice w forest channel mask child) *
    (if forest child then FiniteProbRecord.characterSign
      (Bool.xor (sample child) (signal child (fun parent _edge => sample parent)))
     else if mask child then FiniteProbRecord.characterSign
      (Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent))) else 1)

private theorem canonicalRow_product (w : HedgeWitness G q)
    (tables : Fin S.count -> BooleanChannelTable (Fin (channelCount w)))
    (forest : NodeSet S) (channel : Fin (channelCount w))
    (signal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (mask : NodeSet S)
    (subset : NodeSet.Subset mask (outside forest)) :
    FiniteProduct.iProduct S.count (canonicalRow w tables forest channel signal backgroundSignal target sample mask) =
      HedgeChannelTable.choiceCoefficient tables target sample (fullChoice w forest channel mask) *
        FiniteProbRecord.characterSign
          (Bool.xor (signalPhase forest signal sample) (signalPhase mask backgroundSignal sample)) := by
  unfold canonicalRow
  rw [FiniteProduct.iProduct_mul]
  apply congrArg (HedgeChannelTable.choiceCoefficient tables target sample (fullChoice w forest channel mask) * ·)
  have localSigns : (fun child => if forest child then FiniteProbRecord.characterSign
        (Bool.xor (sample child) (signal child (fun parent _edge => sample parent)))
      else if mask child then FiniteProbRecord.characterSign
        (Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent))) else 1) =
      (fun child => (if forest child then FiniteProbRecord.characterSign
        (Bool.xor (sample child) (signal child (fun parent _edge => sample parent))) else 1) *
        (if mask child then FiniteProbRecord.characterSign
          (Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent))) else 1)) := by
    funext child
    cases inside : forest child with
    | true => simp only [mask_false_inside forest mask subset child inside,
        if_true, Bool.false_eq_true, if_false, Int.mul_one]
    | false => simp only [Bool.false_eq_true, if_false, Int.one_mul]
  rw [localSigns, FiniteProduct.iProduct_mul, masked_sign_product, masked_sign_product,
    FiniteProbRecord.characterSign_xor]

/-! ## Complete actual baseline and perturbation -/

private theorem capacityCoefficient_equal (w : HedgeWitness G q)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) (child : Fin S.count) :
    (leftTables w child).expansionCoefficientUnder (target child) (sample child) none =
      capacityRowUnder w target sample child := by
  unfold capacityRowUnder
  cases target child with
  | some _fixed => rfl
  | none => exact congrArg (fun value : Nat => (value : Int)) (capacities_equal w child)

private theorem backgroundCoefficient_equal (w : HedgeWitness G q)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) (child : Fin S.count) :
    (leftTables w child).expansionCoefficientUnder (target child) (sample child)
        (some (backgroundChannel w child)) =
      (rightTables w child).expansionCoefficientUnder (target child) (sample child)
        (some (backgroundChannel w child)) := by
  cases target child with
  | some _fixed => rfl
  | none =>
      simp only [BooleanChannelTable.expansionCoefficientUnder, leftTables, rightTables,
        HedgeChannelCoefficients.tables, BooleanChannelTable.ofCapacity,
        HedgeChannelCoefficients.rowExponent, leftAnchors, rightAnchors, role_backgroundChannel]

/-- The complete background-only canonical sum is an ordinary local row
product.  The equality uses every actual mask and retains zero indicators;
it does not assume the sample is consistent with the intervention. -/
theorem commonTermSum_eq_backgroundProduct (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (smallSignal backgroundSignal : ParentSignal S)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    ((commonChoicesUnder w target).map
      (leftTermIntegralUnder w rich smallSignal backgroundSignal target sample)).sum =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        smallCapacityProductUnder w target sample *
        outsideBackgroundProductUnder w backgroundSignal target sample := by
  let term := leftTermIntegralUnder w rich smallSignal backgroundSignal target sample
  have removeFilter := FiniteSupportedSum.sum_eq_filter_of_zero (commonChoices w)
    (HedgeChannelTable.choiceAllowedUnder target) term (by
      intro choice listed rejected
      rcases List.mem_map.mp listed with ⟨mask, _listed, same⟩
      rw [← same]
      unfold term
      rw [left_commonTermIntegral_under, coefficient_zero_of_disallowed _ _ _ _ (same ▸ rejected),
        Int.mul_zero, Int.zero_mul])
  change (((commonChoices w).filter (HedgeChannelTable.choiceAllowedUnder target)).map term).sum = _
  rw [← removeFilter]
  unfold commonChoices
  simp only [List.map_map, Function.comp_def]
  have emptyPhase : signalPhase (NodeSet.empty : NodeSet S) smallSignal sample = false := by
    unfold signalPhase
    rw [← hedgeNodeXor_mask_of_subset NodeSet.empty NodeSet.full (fun _ _ => rfl)]
    unfold hedgeNodeXor
    apply foldl_unchanged
    intro total child
    simp only [NodeSet.empty, Bool.false_eq_true, if_false, Bool.xor_false]
  have terms : ((masks (outside w.small)).map (fun mask =>
      term (backgroundChoice w mask))).sum =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        ((masks (outside w.small)).map (fun mask => FiniteProduct.iProduct S.count
          (canonicalRow w (leftTables w) NodeSet.empty (smallChannel w)
            smallSignal backgroundSignal target sample mask))).sum := by
    rw [← FiniteSupportedSum.sum_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro mask _listed
    rw [canonicalRow_product w _ _ _ _ _ _ _ mask (fun _ _ => rfl), emptyPhase, Bool.false_xor]
    simpa only [fullChoice, NodeSet.empty, Bool.false_eq_true, if_false, Int.mul_assoc] using
      left_commonTermIntegral_under w rich smallSignal backgroundSignal target sample mask
  rw [terms]
  let high := fun child => (rightTables w child).expansionCoefficientUnder
    (target child) (sample child) (some (backgroundChannel w child)) *
      FiniteProbRecord.characterSign
        (Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent)))
  have rows : ((masks (outside w.small)).map (fun mask => FiniteProduct.iProduct S.count
        (canonicalRow w (leftTables w) NodeSet.empty (smallChannel w)
          smallSignal backgroundSignal target sample mask))).sum =
      ((masks (outside w.small)).map (fun mask => FiniteProduct.iProduct S.count
        (fun child => if mask child then high child else capacityRowUnder w target sample child))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro mask _listed
    apply FiniteProduct.iProduct_congr S.count
    intro child
    cases picked : mask child <;>
      simp only [canonicalRow, fullChoice, NodeSet.empty, Bool.false_eq_true,
        if_false, backgroundChoice, picked, if_true, Int.mul_one,
        capacityCoefficient_equal, backgroundCoefficient_equal, high]
  rw [rows, masks_product_expansion]
  unfold smallCapacityProductUnder outsideBackgroundProductUnder
  rw [Int.mul_assoc, ← FiniteProduct.iProduct_mul]
  apply congrArg (((PairRootChannels.prior G.binary (channelCount w)).den : Int) * ·)
  apply FiniteProduct.iProduct_congr S.count
  intro child
  cases inside : w.small child <;>
    simp only [if_true, Bool.false_eq_true, if_false, Int.mul_one,
      Int.one_mul, backgroundRowUnder, high]

/-- Sum every permitted full-small interaction before factorizing it.
The small character and the outside-small background product are the exact
ones appearing in the installed model; unsupported forced choices and
conflicting samples still have their genuine zero coefficients. -/
theorem fullSmallTermSum_eq_backgroundProduct (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    ((rightFullChoicesUnder w target).map
      (rightTermIntegralUnder w smallSignal backgroundSignal target sample)).sum =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        smallAmplitudeProductUnder w target sample *
        FiniteProbRecord.characterSign (signalPhase w.small smallSignal sample) *
        outsideBackgroundProductUnder w backgroundSignal target sample := by
  let term := rightTermIntegralUnder w smallSignal backgroundSignal target sample
  have removeFilter := FiniteSupportedSum.sum_eq_filter_of_zero (rightFullChoices w)
    (HedgeChannelTable.choiceAllowedUnder target) term (by
      intro choice listed rejected
      rcases List.mem_map.mp listed with ⟨mask, listed, same⟩
      rw [← same]
      unfold term
      rw [right_fullTermIntegral_under w _ _ _ sample mask ((masks_member_iff _ _).mp listed),
        coefficient_zero_of_disallowed _ _ _ _ (same ▸ rejected), Int.mul_zero, Int.zero_mul])
  change (((rightFullChoices w).filter (HedgeChannelTable.choiceAllowedUnder target)).map term).sum = _
  rw [← removeFilter]
  unfold rightFullChoices
  simp only [List.map_map, Function.comp_def]
  have terms : ((masks (outside w.small)).map (fun mask =>
      term (fullChoice w w.small (smallChannel w) mask))).sum =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        ((masks (outside w.small)).map (fun mask => FiniteProduct.iProduct S.count
          (canonicalRow w (rightTables w) w.small (smallChannel w)
            smallSignal backgroundSignal target sample mask))).sum := by
    rw [← FiniteSupportedSum.sum_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro mask listed
    have subset := (masks_member_iff _ _).mp listed
    rw [canonicalRow_product w _ _ _ _ _ _ _ mask subset]
    simpa only [Int.mul_assoc] using
      right_fullTermIntegral_under w smallSignal backgroundSignal target sample mask subset
  rw [terms]
  let smallFactor := fun child => if w.small child then
    (rightTables w child).expansionCoefficientUnder (target child) (sample child)
      (some (smallChannel w)) * FiniteProbRecord.characterSign
        (Bool.xor (sample child) (smallSignal child (fun parent _edge => sample parent))) else 1
  let low := fun child => if w.small child then smallFactor child else capacityRowUnder w target sample child
  let high := fun child => (rightTables w child).expansionCoefficientUnder
    (target child) (sample child) (some (backgroundChannel w child)) *
      FiniteProbRecord.characterSign
        (Bool.xor (sample child) (backgroundSignal child (fun parent _edge => sample parent)))
  have rows : ((masks (outside w.small)).map (fun mask => FiniteProduct.iProduct S.count
        (canonicalRow w (rightTables w) w.small (smallChannel w)
          smallSignal backgroundSignal target sample mask))).sum =
      ((masks (outside w.small)).map (fun mask => FiniteProduct.iProduct S.count
        (fun child => if mask child then high child else low child))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro mask listed
    have subset := (masks_member_iff _ _).mp listed
    apply FiniteProduct.iProduct_congr S.count
    intro child
    cases inside : w.small child with
    | true => simp only [canonicalRow, fullChoice, inside, if_true,
        mask_false_inside w.small mask subset child inside, Bool.false_eq_true,
        if_false, low, smallFactor]
    | false => cases picked : mask child <;>
        simp only [canonicalRow, fullChoice, inside, Bool.false_eq_true, if_false,
          backgroundChoice, picked, if_true, Int.mul_one, high, low, capacityRowUnder]
  rw [rows, masks_product_expansion]
  have productSplit : FiniteProduct.iProduct S.count
      (fun child => if w.small child then low child else low child + high child) =
      FiniteProduct.iProduct S.count smallFactor *
        outsideBackgroundProductUnder w backgroundSignal target sample := by
    unfold outsideBackgroundProductUnder
    rw [← FiniteProduct.iProduct_mul]
    apply FiniteProduct.iProduct_congr S.count
    intro child
    cases inside : w.small child <;>
      simp only [if_true, Bool.false_eq_true, if_false, low, smallFactor,
        inside, Int.mul_one, Int.one_mul, backgroundRowUnder, high]
  have smallSplit : FiniteProduct.iProduct S.count smallFactor =
      smallAmplitudeProductUnder w target sample *
        FiniteProbRecord.characterSign (signalPhase w.small smallSignal sample) := by
    unfold smallAmplitudeProductUnder
    rw [← masked_sign_product, ← FiniteProduct.iProduct_mul]
    apply FiniteProduct.iProduct_congr S.count
    intro child
    cases inside : w.small child <;> simp only [smallFactor, inside,
      if_true, Bool.false_eq_true, if_false, Int.mul_one]
  rw [productSplit, smallSplit]
  ac_rfl

/-- The left model's complete actual action-cut numerator is the background
product with capacity factors on the small forest.  Any extra forced rows
are retained.  The action-seed hypothesis is precisely what eliminates the
large channels, not a restriction to a seed-only intervention. -/
theorem left_integratedNumerator_eq_backgroundProduct_of_action
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (sample : S.binary.Assignment) :
    (HedgeChannelTable.integratedNumerator G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) target sample : Int) =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        smallCapacityProductUnder w target sample *
        outsideBackgroundProductUnder w backgroundSignal target sample := by
  rw [HedgeChannelTable.integratedNumerator_expansion,
    left_expandedIntegral_common_under w rich smallSignal backgroundSignal target fixed forced sample,
    commonTermSum_eq_backgroundProduct]

/-- Exact complete likelihood difference after the action cut, with one
small-forest character against the genuine outside-small background product.
This is an equality of the two actual nonnegative natural numerators embedded
in integers.  It neither claims a pointwise positive difference nor infers a
conditional gap from joint separation alone. -/
theorem integratedNumerators_difference_eq_backgroundProduct_of_action
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (sample : S.binary.Assignment) :
    (HedgeChannelTable.integratedNumerator G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) target sample : Int) =
      (HedgeChannelTable.integratedNumerator G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target sample : Int) +
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        smallAmplitudeProductUnder w target sample *
        FiniteProbRecord.characterSign (signalPhase w.small smallSignal sample) *
        outsideBackgroundProductUnder w backgroundSignal target sample := by
  rw [integratedNumerators_difference_of_action w rich smallSignal backgroundSignal target fixed forced sample,
    fullSmallTermSum_eq_backgroundProduct]

end HedgeChannelInstallation
end Causality
end Thesis
