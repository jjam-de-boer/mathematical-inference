import Thesis.Probability.Construction
import Thesis.Probability.FiniteRecordSlicing

namespace Thesis
namespace Probability

/-!
# Full coordinate conditionals determine a positive finite product law

A joint signal gap need not survive conditioning at a preselected coordinate:
the difference might be carried by the conditioning marginal instead.  This
module isolates the general finite argument needed to select a coordinate
whose conditional really differs.  It concerns arbitrary dependent finite
coordinate alphabets, rather than a fixed number of Boolean hedge roots.

The proof has two independent parts.  Equal full coordinate conditionals make
the ratio of the two joint cell masses constant along a one-coordinate change.
Replacing coordinates in their explicit finite order connects every pair of
assignments.  Finally, summing the complete cells uses the actual two record
normalizations to fix that common scale.  No equal-denominator assumption,
stationary-distribution theorem, or chosen path through assignments is used.

Full support is important: only genuinely positive context and cell masses
are cancelled.  The finite disagreement selector below returns explicit
coordinate and reference data, not data extracted by choice from a proposition.
This probability layer does not itself identify those coordinates with a
causal graph's admissible collider pivots or compose an active-path model.
-/

namespace FiniteProductConditionals

universe u

variable {n : Nat} {Value : Fin n -> Type u}
variable [coordinateEq : (i : Fin n) -> DecidableEq (Value i)]

private instance valueDecidableEq (i : Fin n) : DecidableEq (Value i) := coordinateEq i

private instance assignmentDecidableEq : DecidableEq (FiniteProduct.Assignment n Value) :=
  FiniteProduct.assignmentDecidableEq n Value coordinateEq

/-- Agree with a reference on every coordinate except the selected pivot.
The remaining coordinate value is genuinely free in this context cylinder. -/
def context (pivot : Fin n) (reference : FiniteProduct.Assignment n Value) :
    Event (FiniteProduct.Assignment n Value) :=
  fun sample => finAll n (fun node => if node = pivot then true else decide (sample node = reference node))

/-- The selected coordinate's reference-value event. -/
def coordinateEvent (pivot : Fin n) (reference : FiniteProduct.Assignment n Value) :
    Event (FiniteProduct.Assignment n Value) :=
  fun sample => decide (sample pivot = reference pivot)

/-- Positive mass of every full assignment cell, not merely of each separate
coordinate marginal.  Repeated labels in the actual atom list are allowed. -/
def FullSupport (record : FiniteProbRecord (FiniteProduct.Assignment n Value)) : Prop :=
  forall reference, record.EventPositive (FiniteProbRecord.singletonEvent reference)

private def cellMass (record : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (reference : FiniteProduct.Assignment n Value) : Nat :=
  FiniteProbRecord.eventMass record.atoms (FiniteProbRecord.singletonEvent reference)

private theorem context_coordinate_eq_cell (pivot : Fin n)
    (reference sample : FiniteProduct.Assignment n Value) :
    (context pivot reference sample && coordinateEvent pivot reference sample) =
      FiniteProbRecord.singletonEvent reference sample := by
  apply Bool.eq_iff_iff.mpr
  simp only [context, coordinateEvent, Bool.and_eq_true_iff, finAll_eq_true_iff,
    decide_eq_true_eq, FiniteProbRecord.singletonEvent]
  constructor
  · intro parts
    funext node
    by_cases same : node = pivot
    · subst node; exact parts.2
    · have selected := parts.1 node
      simpa only [same, if_false, decide_eq_true_eq] using selected
  · intro same
    constructor
    · intro node
      by_cases selected : node = pivot
      · simp only [selected, if_true]
      · simp only [selected, if_false]
        exact decide_eq_true (congrFun same node)
    · exact congrFun same pivot

/-- Every full context cylinder is supported because it contains its
reference cell.  The support witness is derived from the actual record. -/
theorem context_positive (record : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (supported : FullSupport record) (pivot : Fin n) (reference : FiniteProduct.Assignment n Value) :
    record.EventPositive (context pivot reference) := by
  apply Nat.lt_of_lt_of_le (supported reference)
  apply FiniteProbRecord.eventMass_mono record.atoms _ _
  intro sample selected
  have same : sample = reference := of_decide_eq_true selected
  subst sample
  apply (finAll_eq_true_iff _).mpr
  intro node
  by_cases atPivot : node = pivot
  · simp only [atPivot, if_true]
  · simp only [atPivot, if_false, decide_true]

/-- One full-coordinate conditional, normalized by its actual context mass.
It is the reference-value probability in the explicitly conditioned record. -/
def conditionalAt (record : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (supported : FullSupport record) (pivot : Fin n) (reference : FiniteProduct.Assignment n Value) : QProb :=
  (record.conditionOn (context pivot reference) (context_positive record supported pivot reference)).probVal
    (coordinateEvent pivot reference)

private theorem conditionalAt_num (record : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (supported : FullSupport record) (pivot : Fin n) (reference : FiniteProduct.Assignment n Value) :
    (conditionalAt record supported pivot reference).num = cellMass record reference := by
  change FiniteProbRecord.eventMass (record.atoms.filter (fun atom => context pivot reference atom.1))
    (coordinateEvent pivot reference) = _
  rw [FiniteProbRecord.eventMass_filter_event]
  exact FiniteProbRecord.eventMass_congr record.atoms _ _ (context_coordinate_eq_cell pivot reference)

private theorem conditionalAt_den (record : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (supported : FullSupport record) (pivot : Fin n) (reference : FiniteProduct.Assignment n Value) :
    (conditionalAt record supported pivot reference).den =
      FiniteProbRecord.eventMass record.atoms (context pivot reference) := rfl

/-- A reference change only at the omitted pivot leaves the complete context
event unchanged.  This is a pointwise event identity, not a marginal claim. -/
theorem context_eq_of_away (pivot : Fin n) (first second : FiniteProduct.Assignment n Value)
    (away : forall node, node ≠ pivot -> first node = second node) :
    context pivot first = context pivot second := by
  funext sample
  apply finAll_congr
  intro node
  by_cases same : node = pivot
  · simp only [same, if_true]
  · simp only [same, if_false]
    rw [away node same]

/-! ## Local conditional equality determines neighbouring cell ratios -/

/-- A ratio of joint cell masses is only a proof device; it need not be a
probability in the unit interval.  Right full support supplies its denominator. -/
private def cellRatio (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (rightSupported : FullSupport right) (reference : FiniteProduct.Assignment n Value) : QProb :=
  ⟨cellMass left reference, cellMass right reference, rightSupported reference⟩

private theorem cellRatio_equiv_of_away
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (conditionals : forall pivot reference, QProb.Equiv
      (conditionalAt left leftSupported pivot reference) (conditionalAt right rightSupported pivot reference))
    (pivot : Fin n) (first second : FiniteProduct.Assignment n Value)
    (away : forall node, node ≠ pivot -> first node = second node) :
    QProb.Equiv (cellRatio left right rightSupported first) (cellRatio left right rightSupported second) := by
  have firstEqual := conditionals pivot first
  have secondEqual := conditionals pivot second
  simp only [QProb.Equiv, conditionalAt_num, conditionalAt_den] at firstEqual secondEqual
  rw [← context_eq_of_away pivot first second away] at secondEqual
  change cellMass left first * cellMass right second = cellMass left second * cellMass right first
  apply Nat.eq_of_mul_eq_mul_right (context_positive right rightSupported pivot first)
  calc
    _ = (cellMass left first * FiniteProbRecord.eventMass right.atoms (context pivot first)) * cellMass right second := by ac_rfl
    _ = (cellMass right first * FiniteProbRecord.eventMass left.atoms (context pivot first)) * cellMass right second := by rw [firstEqual]
    _ = (cellMass right second * FiniteProbRecord.eventMass left.atoms (context pivot first)) * cellMass right first := by ac_rfl
    _ = (cellMass left second * FiniteProbRecord.eventMass right.atoms (context pivot first)) * cellMass right first := by rw [← secondEqual]
    _ = _ := by ac_rfl

/-! ## Explicit finite-coordinate connectivity -/

private def prefixAssignment (target initial : FiniteProduct.Assignment n Value) (length : Nat) :
    FiniteProduct.Assignment n Value :=
  fun node => if node.val < length then target node else initial node

omit coordinateEq in
private theorem prefix_zero (target initial : FiniteProduct.Assignment n Value) : prefixAssignment target initial 0 = initial := by
  funext node
  exact if_neg (Nat.not_lt_zero node.val)

omit coordinateEq in
private theorem prefix_full (target initial : FiniteProduct.Assignment n Value) : prefixAssignment target initial n = target := by
  funext node
  exact if_pos node.isLt

omit coordinateEq in
private theorem prefix_away (target initial : FiniteProduct.Assignment n Value)
    (length : Nat) (bound : length < n) (node : Fin n) (away : node ≠ ⟨length, bound⟩) :
    prefixAssignment target initial length node = prefixAssignment target initial (length + 1) node := by
  have different : node.val ≠ length := by
    intro same
    exact away (Fin.ext same)
  -- Prove the two directions directly.  Asking arithmetic automation to
  -- negate this whole iff can synthesize classical decisions for its parts.
  have sameTest : (node.val < length) ↔ (node.val < length + 1) :=
    ⟨Nat.lt_succ_of_lt, fun before => (Nat.lt_succ_iff_lt_or_eq.mp before).resolve_right different⟩
  simp only [prefixAssignment, sameTest]

private theorem cellRatio_equiv_prefix
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (conditionals : forall pivot reference, QProb.Equiv
      (conditionalAt left leftSupported pivot reference) (conditionalAt right rightSupported pivot reference))
    (initial target : FiniteProduct.Assignment n Value) (length : Nat) (bound : length ≤ n) :
    QProb.Equiv (cellRatio left right rightSupported initial)
      (cellRatio left right rightSupported (prefixAssignment target initial length)) := by
  induction length with
  | zero => rw [prefix_zero]; exact QProb.equiv_refl _
  | succ length inductionHypothesis =>
      have before : length ≤ n := Nat.le_trans (Nat.le_succ length) bound
      have inside : length < n := Nat.lt_of_succ_le bound
      exact QProb.equiv_trans (inductionHypothesis before)
        (cellRatio_equiv_of_away left right leftSupported rightSupported conditionals ⟨length, inside⟩
          (prefixAssignment target initial length) (prefixAssignment target initial (length + 1))
          (prefix_away target initial length inside))

/-- Equality of all full-coordinate conditionals gives one common joint-cell
scale.  The finite prefix sequence is supplied explicitly, including at zero
coordinates; no connectedness witness is selected from a proposition. -/
private theorem cellRatio_equiv
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (conditionals : forall pivot reference, QProb.Equiv
      (conditionalAt left leftSupported pivot reference) (conditionalAt right rightSupported pivot reference))
    (first second : FiniteProduct.Assignment n Value) :
    QProb.Equiv (cellRatio left right rightSupported first) (cellRatio left right rightSupported second) := by
  have connected := cellRatio_equiv_prefix left right leftSupported rightSupported conditionals first second n (Nat.le_refl n)
  rw [prefix_full] at connected
  exact connected

/-! ## Genuine finite normalization closes the joint comparison -/

private theorem sum_scaled (values : List (FiniteProduct.Assignment n Value))
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (first second : Nat) (scaled : forall reference,
      cellMass left reference * first = cellMass right reference * second) :
    (values.map (cellMass left)).sum * first = (values.map (cellMass right)).sum * second := by
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.zero_mul]
  | cons reference rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, Nat.add_mul]
      rw [scaled reference, inductionHypothesis]

/-- Equality of all full-coordinate conditionals determines every singleton
probability.  Each reference cell is its own explicit normalization anchor;
no reference assignment is chosen from a nonemptiness proposition. -/
theorem singleton_probVal_equiv_of_fullConditionals
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (values : List (FiniteProduct.Assignment n Value)) (nodup : values.Nodup)
    (complete : forall reference, reference ∈ values)
    (conditionals : forall pivot reference, QProb.Equiv
      (conditionalAt left leftSupported pivot reference) (conditionalAt right rightSupported pivot reference))
    (reference : FiniteProduct.Assignment n Value) :
    QProb.Equiv (left.probVal (FiniteProbRecord.singletonEvent reference))
      (right.probVal (FiniteProbRecord.singletonEvent reference)) := by
  have scaled (sample : FiniteProduct.Assignment n Value) :
      cellMass left sample * cellMass right reference = cellMass right sample * cellMass left reference := by
    have compared := cellRatio_equiv left right leftSupported rightSupported conditionals sample reference
    exact compared.trans (Nat.mul_comm _ _)
  have total := sum_scaled values left right (cellMass right reference) (cellMass left reference) scaled
  have leftTotal : (values.map (cellMass left)).sum = left.den := left.sum_singletonMass_eq_den values nodup complete
  have rightTotal : (values.map (cellMass right)).sum = right.den := right.sum_singletonMass_eq_den values nodup complete
  rw [leftTotal, rightTotal] at total
  change cellMass left reference * right.den = cellMass right reference * left.den
  calc
    _ = right.den * cellMass left reference := Nat.mul_comm _ _
    _ = left.den * cellMass right reference := total.symm
    _ = _ := Nat.mul_comm _ _

/-- Positive finite dependent-product laws agreeing in every full coordinate
conditional agree on every Boolean event.  The proof also covers zero
coordinates, where normalization alone fixes the sole assignment's law. -/
theorem probVal_equiv_of_fullConditionals
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (values : List (FiniteProduct.Assignment n Value)) (nodup : values.Nodup)
    (complete : forall reference, reference ∈ values)
    (conditionals : forall pivot reference, QProb.Equiv
      (conditionalAt left leftSupported pivot reference) (conditionalAt right rightSupported pivot reference))
    (event : Event (FiniteProduct.Assignment n Value)) :
    QProb.Equiv (left.probVal event) (right.probVal event) :=
  left.probVal_extensional_of_singletons right values nodup complete
    (singleton_probVal_equiv_of_fullConditionals left right leftSupported rightSupported values nodup complete conditionals)
    event

/-! ## Explicit finite search for a genuinely separated coordinate conditional -/

/-- A selected coordinate, its actual reference assignment, and a supported
conditional value gap.  This is data consumed by a model construction, not a
propositional statement that some unspecified coordinate might work. -/
structure Disagreement (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right) where
  pivot : Fin n
  reference : FiniteProduct.Assignment n Value
  separated : Not (QProb.Equiv (conditionalAt left leftSupported pivot reference)
    (conditionalAt right rightSupported pivot reference))

private def disagreementAt? (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (pivot : Fin n) (reference : FiniteProduct.Assignment n Value) :
    Option (Disagreement left right leftSupported rightSupported) :=
  if same : QProb.Equiv (conditionalAt left leftSupported pivot reference)
      (conditionalAt right rightSupported pivot reference) then none
  else some ⟨pivot, reference, same⟩

/-- Scan the displayed finite coordinate order and the supplied reference
order.  No completeness or duplicate-freeness is needed merely to run the
search; those properties enter only its completeness theorem below. -/
def disagreement? (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (values : List (FiniteProduct.Assignment n Value)) :
    Option (Disagreement left right leftSupported rightSupported) :=
  (List.finRange n).findSome? (fun pivot =>
    values.findSome? (disagreementAt? left right leftSupported rightSupported pivot))

/-- Exhaustion of the exact finite search is equivalent to equality of all
coordinate conditionals.  Only completeness of the reference list is needed;
there is no excluded-middle test of extensional equality of whole laws. -/
theorem disagreement?_eq_none_iff (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (values : List (FiniteProduct.Assignment n Value)) (complete : forall reference, reference ∈ values) :
    disagreement? left right leftSupported rightSupported values = none ↔
      forall pivot reference, QProb.Equiv (conditionalAt left leftSupported pivot reference)
        (conditionalAt right rightSupported pivot reference) := by
  constructor
  · intro exhausted pivot reference
    have noneAtPivot := (List.findSome?_eq_none_iff.mp exhausted) pivot (List.mem_finRange pivot)
    have noneAtReference := (List.findSome?_eq_none_iff.mp noneAtPivot) reference (complete reference)
    unfold disagreementAt? at noneAtReference
    split at noneAtReference
    · assumption
    · cases noneAtReference
  · intro same
    apply List.findSome?_eq_none_iff.mpr
    intro pivot _
    apply List.findSome?_eq_none_iff.mpr
    intro reference _
    unfold disagreementAt?
    rw [dif_pos (same pivot reference)]

/-- Return an actual separated full-coordinate conditional from any joint
event gap.  A failed search contradicts the already proved normalization
theorem; matching the computed option produces the data constructively.
The event may mix every coordinate and need not be a singleton or parity. -/
def disagreementOfEventGap (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (leftSupported : FullSupport left) (rightSupported : FullSupport right)
    (values : List (FiniteProduct.Assignment n Value)) (nodup : values.Nodup)
    (complete : forall reference, reference ∈ values)
    (event : Event (FiniteProduct.Assignment n Value))
    (gap : Not (QProb.Equiv (left.probVal event) (right.probVal event))) :
    Disagreement left right leftSupported rightSupported :=
  match found : disagreement? left right leftSupported rightSupported values with
  | some witness => witness
  | none => False.elim (gap (probVal_equiv_of_fullConditionals left right leftSupported rightSupported
      values nodup complete ((disagreement?_eq_none_iff left right leftSupported rightSupported values complete).mp found) event))

end FiniteProductConditionals
end Probability
end Thesis
