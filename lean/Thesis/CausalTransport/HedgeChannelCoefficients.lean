import Thesis.CausalTransport.HedgeChannelMonomial
import Thesis.Probability.FinitePowerProduct

namespace Thesis
namespace Causality
namespace HedgeChannelCoefficients

open Probability

/-!
# Explicit positive integer coefficients for nested channel families

Matching full-channel contributions must not rely on an unspecified small
real perturbation.  We use the integer scale `channels + 2` and powers of
that scale throughout.  At degree bound `n`, the ordinary amplitude is
`K^n`, the common row capacity is `K^(n+1)`, and a designated anchor can
carry the smaller amplitude `K^(n-deficit)`.  No division or rounding occurs.

Each row lists only the channels whose designated supports contain it.
There are at most `channels` such terms and every amplitude is at most the
ordinary amplitude.  The extra room in the scale therefore proves a strictly
positive baseline automatically, for every signal configuration.  Different
anchor and deficit families retain the same literal row capacities.

For a nested forest with `s+1` small vertices and `k` outer vertices, the
small anchor uses deficit `k`.  A large expansion channel whose mask chooses
`e` outer backgrounds uses deficit `e`.  The exact coefficient identity below
matches its full large contribution with the small contribution times that
outer expansion coefficient, provided `e <= k <= n`.

The positive tables are genuine inputs to the actual channel SCM builder.
`HedgeChannelInstallation` instantiates their masks and signals for an
arbitrary hedge.  Summing its surviving terms and proving the original-query
gap are still separate tasks.
This module does not assume observational equivalence or inhabit completeness.
-/

variable {S : ObservedSignature.{0}}

/-- A uniform integer scale with room for every listed channel term. -/
def scale (channels : Nat) : Nat := channels + 2

theorem scale_positive (channels : Nat) : 0 < scale channels := by unfold scale; omega

/-- Amplitude of each ordinary channel row and common background bias. -/
def ordinaryAmplitude (channels bound : Nat) : Nat := scale channels ^ bound

/-- Literal half-mass of every row, independent of its signals and anchors. -/
def capacity (channels bound : Nat) : Nat := scale channels ^ (bound + 1)

/-- One anchored amplitude with an explicitly reduced natural exponent.
The coefficient-matching theorem supplies the bounds preventing a truncated
exponent from changing the intended identity. -/
def anchorAmplitude (channels bound deficit : Nat) : Nat := scale channels ^ (bound - deficit)

theorem ordinaryAmplitude_positive (channels bound : Nat) : 0 < ordinaryAmplitude channels bound :=
  Nat.pow_pos (scale_positive channels)

theorem anchorAmplitude_positive (channels bound deficit : Nat) : 0 < anchorAmplitude channels bound deficit :=
  Nat.pow_pos (scale_positive channels)

theorem anchorAmplitude_le_ordinary (channels bound deficit : Nat) :
    anchorAmplitude channels bound deficit <= ordinaryAmplitude channels bound :=
  Nat.pow_le_pow_right (scale_positive channels) (Nat.sub_le bound deficit)

/-- Every ordinary bias is strictly below the common capacity, including
degree zero.  This leaves a genuinely positive two-sided background row. -/
theorem ordinaryAmplitude_lt_capacity (channels bound : Nat) :
    ordinaryAmplitude channels bound < capacity channels bound := by
  change scale channels ^ bound < scale channels ^ (bound + 1)
  rw [Nat.pow_succ]
  simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left
    (show 1 < scale channels by unfold scale; omega) (Nat.pow_pos (scale_positive channels))

/-- Local amplitude exponent; a channel may omit an anchor altogether.
Such unanchored channels supply ordinary private background biases. -/
def rowExponent (bound : Nat) (anchors : Fin channels -> Option (Fin S.count))
    (deficits : Fin channels -> Nat) (child : Fin S.count) (channel : Fin channels) : Nat :=
  match anchors channel with
  | none => bound
  | some anchor => if child = anchor then bound - deficits channel else bound

theorem rowExponent_le (bound : Nat) (anchors : Fin channels -> Option (Fin S.count))
    (deficits : Fin channels -> Nat) (child : Fin S.count) (channel : Fin channels) :
    rowExponent bound anchors deficits child channel <= bound := by
  cases chosen : anchors channel with
  | none => simp only [rowExponent, chosen]; exact Nat.le_refl bound
  | some anchor =>
      simp only [rowExponent, chosen]
      split
      · exact Nat.sub_le _ _
      · exact Nat.le_refl _

private theorem sum_bound (values : List α) (amplitude : α -> Nat) (bound : Nat)
    (bounded : forall value, amplitude value <= bound) :
    (values.map amplitude).sum <= values.length * bound := by
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul]; exact Nat.le_refl 0
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have boundSum := Nat.add_le_add (bounded value) inductionHypothesis
      rw [Nat.add_comm bound (rest.length * bound)] at boundSum
      exact boundSum

/-- Actual local channel list; unsupported channels are never selectable
at this row in the full likelihood enumeration. -/
def localChannels (nodes : Fin channels -> NodeSet S) (child : Fin S.count) : List (Fin channels) :=
  (List.finRange channels).filter (fun channel => nodes channel child)

/-- The complete amplitude sum fits strictly inside the chosen capacity.
The proof is symbolic in channel count and supports; no exponentially large
mask enumeration or concrete row is evaluated. -/
theorem row_room (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat) (child : Fin S.count) :
    ((localChannels nodes child).map fun channel => scale channels ^ rowExponent bound anchors deficits child channel).sum <
      capacity channels bound := by
  have massBound := sum_bound (localChannels nodes child)
    (fun channel => scale channels ^ rowExponent bound anchors deficits child channel)
    (ordinaryAmplitude channels bound)
    (fun channel => Nat.pow_le_pow_right (scale_positive channels) (rowExponent_le bound anchors deficits child channel))
  have lengthBound : (localChannels nodes child).length <= channels := by
    exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_finRange (n := channels)))
  have coefficientBound : channels * ordinaryAmplitude channels bound < scale channels * ordinaryAmplitude channels bound :=
    Nat.mul_lt_mul_of_pos_right (by unfold scale; omega) (ordinaryAmplitude_positive channels bound)
  refine Nat.lt_of_le_of_lt (Nat.le_trans massBound (Nat.mul_le_mul_right _ lengthBound)) ?_
  simpa only [capacity, ordinaryAmplitude, Nat.pow_succ, Nat.mul_comm] using coefficientBound

/-- Positive rows at one common literal capacity, with no user-supplied
smallness condition.  Supports, anchors and deficits remain explicit finite
data, so no global latent representative or real perturbation is chosen. -/
def tables (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (child : Fin S.count) : BooleanChannelTable (Fin channels) :=
  BooleanChannelTable.ofCapacity (localChannels nodes child)
    (fun channel => scale channels ^ rowExponent bound anchors deficits child channel)
    (capacity channels bound) (row_room channels bound nodes anchors deficits child)

theorem tables_capacity (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat) (child : Fin S.count) :
    (tables channels bound nodes anchors deficits child).capacity = capacity channels bound :=
  BooleanChannelTable.ofCapacity_capacity _ _ _ _

/-- Only supported channels appear in the real local list.  This discharges
the support premise of the monomial survivor and action-cut theorems. -/
theorem tables_channel_allowed (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (child : Fin S.count) (channel : Fin channels)
    (member : channel ∈ (tables channels bound nodes anchors deficits child).channels) : nodes channel child = true :=
  (List.mem_filter.mp member).2

/-- At every configuration both Boolean values have actual positive mass.
This is inherited from the proved positive baseline, not assumed for an
approximate polynomial or for only one queried evidence event. -/
theorem tables_positive (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (child : Fin S.count) (signals : Fin channels -> Bool) (value : Bool) :
    ((tables channels bound nodes anchors deficits child).record signals).EventPositive (FiniteProbRecord.singletonEvent value) :=
  (tables channels bound nodes anchors deficits child).record_positive signals value

/-- Actual graph-compatible SCM supplied by the explicit power tables.
Parent signals read only declared parents, and incidence signals read only
the original pair roots incident to each child. -/
def model (G : ObservedGraph S) (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool) : ExactModel S.binary :=
  HedgeChannelTable.model G channels (tables channels bound nodes anchors deficits)
    (HedgeChannelTable.incidenceSignals G channels nodes parentSignal)

theorem model_compatible (G : ObservedGraph S) (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool) :
    Compatible (model G channels bound nodes anchors deficits parentSignal) G.binary :=
  HedgeChannelTable.model_compatible G channels _ _

/-- Full observed positivity is now derived for the actual coefficient
construction, without a user-supplied smallness or support premise. -/
theorem model_positive (G : ObservedGraph S) (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (parentSignal : (child : Fin S.count) -> S.binary.ParentValues child -> Fin channels -> Bool) :
    ObservationallyPositive (model G channels bound nodes anchors deficits parentSignal) :=
  HedgeChannelTable.model_positive G channels _ _

/-- Changing supports, anchors or deficits cannot change row capacities.
The two model families can therefore use the actual equality and event-gap
criteria without an extra normalization-matching condition. -/
theorem tables_capacities_equal (channels bound : Nat) (leftNodes rightNodes : Fin channels -> NodeSet S)
    (leftAnchors rightAnchors : Fin channels -> Option (Fin S.count)) (leftDeficits rightDeficits : Fin channels -> Nat)
    (child : Fin S.count) :
    (tables channels bound leftNodes leftAnchors leftDeficits child).capacity =
      (tables channels bound rightNodes rightAnchors rightDeficits child).capacity :=
  (tables_capacity channels bound leftNodes leftAnchors leftDeficits child).trans
    (tables_capacity channels bound rightNodes rightAnchors rightDeficits child).symm

/-- Full coefficient of a channel with one anchor and `others` ordinary
rows.  The anchor is still actual finite data in the product theorem below. -/
def fullCoefficient (channels bound others deficit : Nat) : Nat :=
  anchorAmplitude channels bound deficit * ordinaryAmplitude channels bound ^ others

/-- The fully selected small-channel coefficient is genuinely nonzero.
The later original-outcome marginal must still prove that its character gap
is not erased by projection or conditioning. -/
theorem fullCoefficient_positive (channels bound others deficit : Nat) :
    0 < fullCoefficient channels bound others deficit :=
  Nat.mul_pos (anchorAmplitude_positive channels bound deficit)
    (Nat.pow_pos (ordinaryAmplitude_positive channels bound))

theorem fullCoefficient_product (channels bound others deficit : Nat) (anchor : Fin (others + 1)) :
    FiniteProduct.natProduct (others + 1) (fun index =>
      if index = anchor then anchorAmplitude channels bound deficit else ordinaryAmplitude channels bound) =
      fullCoefficient channels bound others deficit :=
  FiniteProduct.natProduct_one_exception others _ _ anchor

/-- Coefficient of an outer-background mask: each selected row contributes
its ordinary amplitude and each unselected row its background capacity. -/
def outerCoefficient (channels bound outer selected : Nat) : Nat :=
  ordinaryAmplitude channels bound ^ selected * capacity channels bound ^ (outer - selected)

/-- Exact constructive coefficient match for every admissible outer mask.
There are `smallOthers+1` small rows and `outer` additional large rows.
The identity is literal natural multiplication, not a normalized or limiting
argument.  It includes the empty outer forest and empty or full masks. -/
theorem fullCoefficient_match (channels bound smallOthers outer selected : Nat)
    (outerBound : outer <= bound) (selectedBound : selected <= outer) :
    fullCoefficient channels bound (smallOthers + outer) selected =
      fullCoefficient channels bound smallOthers outer * outerCoefficient channels bound outer selected := by
  have subtraction : bound - selected = (bound - outer) + (outer - selected) := by omega
  have splitOuter : outer = selected + (outer - selected) := by omega
  have exponent : (bound - selected) + bound * (smallOthers + outer) =
      ((bound - outer) + bound * smallOthers) + (bound * selected + (bound + 1) * (outer - selected)) := by
    rw [subtraction, Nat.mul_add, show bound * outer = bound * selected + bound * (outer - selected) by
      exact (congrArg (bound * ·) splitOuter).trans (Nat.mul_add _ _ _), Nat.add_mul, Nat.one_mul]
    ac_rfl
  unfold fullCoefficient outerCoefficient anchorAmplitude ordinaryAmplitude capacity
  simp only [← Nat.pow_mul, ← Nat.pow_add]
  exact congrArg (scale channels ^ ·) exponent

/-- Coefficient of one actual finite outer mask, with every selected or
unselected row represented in the original finite product order. -/
def maskCoefficient (channels bound outer : Nat) (mask : Fin outer -> Bool) : Nat :=
  FiniteProduct.natProduct outer (fun index =>
    if mask index then ordinaryAmplitude channels bound else capacity channels bound)

theorem maskCoefficient_eq_outerCoefficient (channels bound outer : Nat) (mask : Fin outer -> Bool) :
    maskCoefficient channels bound outer mask =
      outerCoefficient channels bound outer ((List.finRange outer).countP mask) :=
  FiniteProduct.natProduct_binary_mask outer _ _ mask

/-- Literal coefficient matching at every actual binary mask.  Its size
bound comes from the finite-index count rather than being supplied as an
extra mask-readiness premise. -/
theorem fullCoefficient_match_mask (channels bound smallOthers outer : Nat)
    (outerBound : outer <= bound) (mask : Fin outer -> Bool) :
    fullCoefficient channels bound (smallOthers + outer) ((List.finRange outer).countP mask) =
      fullCoefficient channels bound smallOthers outer * maskCoefficient channels bound outer mask := by
  rw [maskCoefficient_eq_outerCoefficient]
  apply fullCoefficient_match channels bound smallOthers outer _ outerBound
  simpa only [List.length_finRange] using List.countP_le_length (p := mask) (l := List.finRange outer)

/-- Character of the selected outer background rows; unselected rows
contribute the multiplicative unit rather than an omitted coordinate. -/
def maskCharacter (outer : Nat) (mask bits : Fin outer -> Bool) : Int :=
  FiniteProduct.iProduct outer (fun index => if mask index then FiniteProbRecord.characterSign (bits index) else 1)

/-- One weighted mask term is exactly the corresponding full outer-row
product.  Natural coefficients are embedded into integers only to multiply
their Boolean signs; no signed probability record is introduced. -/
theorem maskTerm_product (channels bound outer : Nat) (mask bits : Fin outer -> Bool) :
    (maskCoefficient channels bound outer mask : Int) * maskCharacter outer mask bits =
      FiniteProduct.iProduct outer (fun index => if mask index then
        (ordinaryAmplitude channels bound : Int) * FiniteProbRecord.characterSign (bits index)
        else (capacity channels bound : Int)) := by
  have natural := FiniteProduct.iProduct_nat outer
    (fun index => if mask index then ordinaryAmplitude channels bound else capacity channels bound)
  have separated := FiniteProduct.iProduct_mul outer
    (fun index => ((if mask index then ordinaryAmplitude channels bound else capacity channels bound : Nat) : Int))
    (fun index => if mask index then FiniteProbRecord.characterSign (bits index) else 1)
  refine (congrArg (· * maskCharacter outer mask bits) natural.symm).trans (separated.symm.trans ?_)
  apply FiniteProduct.iProduct_congr
  intro index
  cases mask index <;> simp only [Bool.false_eq_true, if_false, if_true, Int.mul_one]

private theorem sum_mul_left (values : List α) (factor : Int) (term : α -> Int) :
    (values.map fun value => factor * term value).sum = factor * (values.map term).sum := by
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, Int.mul_zero]
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis, Int.mul_add]

/-- Complete sum of the large family's outer-mask coefficients and signs.
Every finite mask occurs once in the ordinary dependent-product enumeration. -/
def largeMaskSum (channels bound smallOthers outer : Nat) (bits : Fin outer -> Bool) : Int :=
  ((FiniteProduct.enumeration outer (fun _ => Bool) (fun _ => [false, true])).map fun mask =>
    (fullCoefficient channels bound (smallOthers + outer) ((List.finRange outer).countP mask) : Int) *
      maskCharacter outer mask bits).sum

/-- The sum of all large-channel mask contributions is exactly the small
full coefficient times the complete outer-background product.  This is the
finite coefficient matching required after channel cancellation: all masks
and their signed interactions are retained, with no limiting argument. -/
theorem largeMaskSum_eq_background_product (channels bound smallOthers outer : Nat)
    (outerBound : outer <= bound) (bits : Fin outer -> Bool) :
    largeMaskSum channels bound smallOthers outer bits =
      (fullCoefficient channels bound smallOthers outer : Int) * FiniteProduct.iProduct outer
        (fun index => (capacity channels bound : Int) +
          (ordinaryAmplitude channels bound : Int) * FiniteProbRecord.characterSign (bits index)) := by
  let term := fun (index : Fin outer) (bit : Bool) => if bit then
    (ordinaryAmplitude channels bound : Int) * FiniteProbRecord.characterSign (bits index)
    else (capacity channels bound : Int)
  have maskTerms : forall mask,
      (fullCoefficient channels bound (smallOthers + outer) ((List.finRange outer).countP mask) : Int) *
        maskCharacter outer mask bits = (fullCoefficient channels bound smallOthers outer : Int) *
          FiniteProduct.iProduct outer (fun index => term index (mask index)) := by
    intro mask
    rw [fullCoefficient_match_mask channels bound smallOthers outer outerBound mask, Int.natCast_mul, Int.mul_assoc]
    exact congrArg ((fullCoefficient channels bound smallOthers outer : Int) * ·) (maskTerm_product channels bound outer mask bits)
  have listed : largeMaskSum channels bound smallOthers outer bits =
      ((FiniteProduct.enumeration outer (fun _ => Bool) (fun _ => [false, true])).map fun mask =>
        (fullCoefficient channels bound smallOthers outer : Int) *
          FiniteProduct.iProduct outer (fun index => term index (mask index))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro mask _member
    exact maskTerms mask
  have expanded := FiniteProduct.iProduct_finite_sum outer (fun _ => Bool) (fun _ => [false, true]) term
  have localSums := FiniteProduct.iProduct_congr outer
    (fun index => (([false, true] : List Bool).map (term index)).sum)
    (fun index => (capacity channels bound : Int) +
      (ordinaryAmplitude channels bound : Int) * FiniteProbRecord.characterSign (bits index)) (fun index => by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, term,
          Bool.false_eq_true, if_false, if_true, Int.add_zero])
  exact listed.trans ((sum_mul_left _ _ _).trans
    (congrArg ((fullCoefficient channels bound smallOthers outer : Int) * ·) (expanded.symm.trans localSums)))

/-- Natural numerator of an ordinary biased background row character.
Both signs give positive mass because the chosen capacity strictly exceeds
the ordinary amplitude. -/
def backgroundNumerator (channels bound : Nat) (bit : Bool) : Nat :=
  if bit then capacity channels bound - ordinaryAmplitude channels bound
  else capacity channels bound + ordinaryAmplitude channels bound

theorem backgroundNumerator_positive (channels bound : Nat) (bit : Bool) :
    0 < backgroundNumerator channels bound bit := by
  cases bit with
  | false => exact Nat.lt_of_lt_of_le (Nat.pow_pos (scale_positive channels)) (Nat.le_add_right _ _)
  | true => exact Nat.sub_pos_iff_lt.mpr (ordinaryAmplitude_lt_capacity channels bound)

/-- Its integer character presentation is exactly the positive natural
numerator, not a signed probability cell or truncated negative value. -/
theorem backgroundNumerator_cast (channels bound : Nat) (bit : Bool) :
    (backgroundNumerator channels bound bit : Int) =
      (capacity channels bound : Int) + (ordinaryAmplitude channels bound : Int) * FiniteProbRecord.characterSign bit := by
  cases bit with
  | false => simp only [backgroundNumerator, FiniteProbRecord.characterSign, Bool.false_eq_true,
      if_false, Int.natCast_add, Int.mul_one]
  | true =>
      simp only [backgroundNumerator, FiniteProbRecord.characterSign, if_true]
      rw [Int.ofNat_sub (Nat.le_of_lt (ordinaryAmplitude_lt_capacity channels bound))]
      omega

end HedgeChannelCoefficients
end Causality
end Thesis
