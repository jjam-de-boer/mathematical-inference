import Thesis.CausalTransport.HedgeChannelConditionalGap
import Thesis.Causality.ConditionalIdentificationKernel

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelLatentBoundary

open Probability HedgeChannelInstallation

/-!
# A shared-latent entry which directed-parent signals must not replace

The original graph is `A -> R`, `A <-> R`, `U <-> R`, with no observed
arrow from `U` to `R`.  The query is `P(U | do(A), R)` on three-valued
observed domains.  The displayed hedge has large forest `A,R` and small
forest `R`; its conditioned root has a queried shared-latent neighbour.

The one-way `HedgeChannelLatentBoundaryCounterexample` companion applies
the existing shared-latent constructor to this graph and supplies a genuine
positive pair for the query.  That construction uses the already declared
`U <-> R` source, not an observed parental input.  Keeping that heavier
countermodel assembly separate lets the tiny finite projection below be
checked without importing its carrier and soundness developments.

This fixture also proves the limit of the more restrictive independent-
channel installation.  Its small parent signal can read `A`, but not `U`.
The ordinary background at `U` is a singleton channel, not a channel shared
with `R`.  The complete normalized change is zero at every Boolean reference
for every admissible small/background parent function.  The actual installed
conditionals therefore agree throughout, although the separate shared-latent
pair refutes identifiability.  This is a semantic obstruction to that signal
family, not a failed bounded search or evidence against general completeness.
-/

/-! ## Original signature, projected graph and displayed hedge -/

def signature : ObservedSignature where
  count := 3
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 1 ∧ child.val = 2)
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    omega

def outcomeNode : Fin signature.count := ⟨0, by decide⟩
def actionNode : Fin signature.count := ⟨1, by decide⟩
def rootNode : Fin signature.count := ⟨2, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right ∧ (left = rootNode ∨ right = rootNode))
  bidirected_symmetric := by
    intro left right selected
    have parts := of_decide_eq_true selected
    exact decide_eq_true ⟨Ne.symm parts.1, parts.2.elim Or.inr Or.inl⟩
  bidirected_irreflexive := by intro node; simp

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton rootNode
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def large : NodeSet signature := NodeSet.union (NodeSet.singleton actionNode) (NodeSet.singleton rootNode)
def small : NodeSet signature := NodeSet.singleton rootNode
def child : ForestChild signature := fun node => if node = actionNode then some rootNode else none
def selection : HedgeSelection signature := ⟨large, small, child⟩

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

theorem roots_are_condition : witness.roots = query.condition :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

/-- The actual queried neighbour is not a declared directed parent.  A
parent-signal proof must therefore not read its observed value at `R`. -/
theorem no_observed_readout_edge : signature.directed outcomeNode rootNode = false := rfl

/-- The shared-latent back-door entry prevents the sole remaining
conditioner from being exchanged.  Only this small graph test is reduced. -/
theorem no_exchange : conditionalExchangeStep? graph query = none := by decide +kernel

/-! ## Complete projected sums of the independent-channel family -/

/-- Retain every Boolean reference value explicitly, including the action.
The finite projection calculation below does not test only one convenient
source cell or change the original intervention to a fixed seed value. -/
def reference (outcome action root : Bool) : signature.binary.Assignment :=
  fun node => if node.val = 0 then outcome else if node.val = 1 then action else root

private def target (assignment : signature.binary.Assignment) :=
  query.binary.operationKernel.intervention assignment

private def outcomeMask : NodeSet signature := NodeSet.singleton outcomeNode

private instance : DecidableEq (Fin signature.count -> Option (Fin (channelCount witness))) :=
  FiniteProduct.assignmentDecidableEq signature.count (fun _ => Option (Fin (channelCount witness)))
    (fun _ => inferInstance)

private theorem common_choices (outcome action root : Bool) :
    commonChoicesUnder witness (target (reference outcome action root)) =
      [backgroundChoice witness NodeSet.empty, backgroundChoice witness outcomeMask] := by
  cases outcome <;> cases action <;> cases root <;> decide +kernel

private theorem small_choices (outcome action root : Bool) :
    rightFullChoicesUnder witness (target (reference outcome action root)) =
      [fullChoice witness witness.small (smallChannel witness) NodeSet.empty,
        fullChoice witness witness.small (smallChannel witness) outcomeMask] := by
  cases outcome <;> cases action <;> cases root <;> decide +kernel

private theorem target_at_seed (outcome action root : Bool) :
    target (reference outcome action root) witness.actionSeed = some action := rfl

/-- Leave the literal shared-prior mass outside the tiny observed sum.
Only genuine row coefficients and character phases are computed below;
the potentially much larger response-function support is never evaluated. -/
private def commonTerm (backgroundSignal : ParentSignal signature)
    (assignment sample : signature.binary.Assignment) (mask : NodeSet signature) : Int :=
  HedgeChannelTable.choiceCoefficient (leftTables witness) (target assignment) sample (backgroundChoice witness mask) *
    FiniteProbRecord.characterSign (signalPhase mask backgroundSignal sample)

private def smallTerm (smallSignal backgroundSignal : ParentSignal signature)
    (assignment sample : signature.binary.Assignment) (mask : NodeSet signature) : Int :=
  HedgeChannelTable.choiceCoefficient (rightTables witness) (target assignment) sample
    (fullChoice witness witness.small (smallChannel witness) mask) *
    FiniteProbRecord.characterSign (Bool.xor (signalPhase witness.small smallSignal sample)
      (signalPhase mask backgroundSignal sample))

private def commonProjection (backgroundSignal : ParentSignal signature)
    (assignment : signature.binary.Assignment) (event : Event signature.binary.Assignment) : Int :=
  ((signature.binary.assignmentEnumeration.filter event).map
    (fun sample => commonTerm backgroundSignal assignment sample NodeSet.empty +
      commonTerm backgroundSignal assignment sample outcomeMask)).sum

private def changeProjection (smallSignal backgroundSignal : ParentSignal signature)
    (assignment : signature.binary.Assignment) (event : Event signature.binary.Assignment) : Int :=
  ((signature.binary.assignmentEnumeration.filter event).map
    (fun sample => smallTerm smallSignal backgroundSignal assignment sample NodeSet.empty +
      smallTerm smallSignal backgroundSignal assignment sample outcomeMask)).sum

private theorem castMapSum {α : Type} (values : List α) (term : α -> Nat) :
    (((values.map term).sum : Nat) : Int) = (values.map (fun value => (term value : Int))).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add, inductionHypothesis]

/-- Recover the actual left numerator from its entire surviving background
support.  The equality holds for arbitrary typed small/background signals;
it is not an independent likelihood polynomial supplied by the fixture. -/
private theorem commonProjection_eq (smallSignal backgroundSignal : ParentSignal signature)
    (outcome action root : Bool) (event : Event signature.binary.Assignment) :
    (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
      (leftSignals witness rich smallSignal backgroundSignal) (target (reference outcome action root)) event : Int) =
      ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
        commonProjection backgroundSignal (reference outcome action root) event := by
  unfold HedgeChannelTable.eventNumerator commonProjection
  rw [castMapSum]
  have rows :
      ((signature.binary.assignmentEnumeration.filter event).map (fun sample =>
        (HedgeChannelTable.integratedNumerator graph (channelCount witness) (leftTables witness)
          (leftSignals witness rich smallSignal backgroundSignal) (target (reference outcome action root)) sample : Int))) =
      ((signature.binary.assignmentEnumeration.filter event).map (fun sample =>
        ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
          (commonTerm backgroundSignal (reference outcome action root) sample NodeSet.empty +
            commonTerm backgroundSignal (reference outcome action root) sample outcomeMask))) := by
    apply List.map_congr_left
    intro sample _selected
    have evaluated := (HedgeChannelTable.integratedNumerator_expansion graph (channelCount witness)
      (leftTables witness) (leftSignals witness rich smallSignal backgroundSignal)
      (target (reference outcome action root)) sample).trans
        (left_expandedIntegral_common_under witness rich smallSignal backgroundSignal _ action
          (target_at_seed outcome action root) sample)
    rw [common_choices outcome action root] at evaluated
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero] at evaluated
    rw [left_commonTermIntegral_under witness rich smallSignal backgroundSignal _ sample NodeSet.empty,
      left_commonTermIntegral_under witness rich smallSignal backgroundSignal _ sample outcomeMask] at evaluated
    exact evaluated.trans (by
      change _ = _ * (commonTerm backgroundSignal _ sample NodeSet.empty +
        commonTerm backgroundSignal _ sample outcomeMask)
      simp only [commonTerm, Int.mul_add, Int.mul_assoc])
  exact (congrArg List.sum rows).trans (FiniteSupportedSum.sum_mul_left _ _ _)

/-- The entire right-minus-left contribution has the same literal shared
mass.  Both permitted full-small/background terms, including conflicting
zero cells, remain in the exact projection. -/
private theorem changeProjection_eq (smallSignal backgroundSignal : ParentSignal signature)
    (outcome action root : Bool) (event : Event signature.binary.Assignment) :
    projectedEventChange witness smallSignal backgroundSignal (target (reference outcome action root)) event =
      ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
        changeProjection smallSignal backgroundSignal (reference outcome action root) event := by
  have outcomeOutside : NodeSet.Subset outcomeMask (outside witness.small) := by
    intro node selected
    have same := (NodeSet.singleton_eq_true_iff outcomeNode node).mp selected
    subst node
    decide +kernel
  unfold projectedEventChange changeProjection
  rw [small_choices outcome action root]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
  have rows :
      ((signature.binary.assignmentEnumeration.filter event).map (fun sample =>
        rightTermIntegralUnder witness smallSignal backgroundSignal (target (reference outcome action root)) sample
            (fullChoice witness witness.small (smallChannel witness) NodeSet.empty) +
          rightTermIntegralUnder witness smallSignal backgroundSignal (target (reference outcome action root)) sample
            (fullChoice witness witness.small (smallChannel witness) outcomeMask))) =
      ((signature.binary.assignmentEnumeration.filter event).map (fun sample =>
        ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
          (smallTerm smallSignal backgroundSignal (reference outcome action root) sample NodeSet.empty +
            smallTerm smallSignal backgroundSignal (reference outcome action root) sample outcomeMask))) := by
    apply List.map_congr_left
    intro sample _selected
    rw [right_fullTermIntegral_under witness smallSignal backgroundSignal _ sample NodeSet.empty
        (by intro node selected; cases selected),
      right_fullTermIntegral_under witness smallSignal backgroundSignal _ sample outcomeMask outcomeOutside]
    change _ = _ * (smallTerm smallSignal backgroundSignal _ sample NodeSet.empty +
      smallTerm smallSignal backgroundSignal _ sample outcomeMask)
    simp only [smallTerm, Int.mul_add, Int.mul_assoc]
  exact (congrArg List.sum rows).trans (FiniteSupportedSum.sum_mul_left _ _ _)

/-! ## What the typed parent functions can actually inspect -/

private def rootParents (action : Bool) : signature.binary.ParentValues rootNode := fun _ _ => action

private def emptyParents : signature.binary.ParentValues outcomeNode := fun parent edge => False.elim (by
  have selected := of_decide_eq_true edge
  change parent.val = 1 ∧ (0 : Nat) = 2 at selected
  omega)

/-- Every declared parent of `R` is the action node.  At a fixed hard cut
its complete typed parent vector therefore contains only the fixed action
bit, irrespective of the queried or conditioned sample values. -/
private theorem rootParents_unique (parents : signature.binary.ParentValues rootNode) :
    parents = rootParents (parents actionNode (by decide)) := by
  funext parent edge
  have selected := of_decide_eq_true edge
  change parent.val = 1 ∧ (2 : Nat) = 2 at selected
  have same : parent = actionNode := Fin.ext selected.1
  subst parent
  rfl

/-- `U` has no declared parents.  Its arbitrary background signal is a
single Boolean constant, not a function of the latent neighbour's observed
value.  Empty-input extensionality supplies the literal vector equality. -/
private theorem emptyParents_unique (parents : signature.binary.ParentValues outcomeNode) :
    parents = emptyParents := by
  funext parent edge
  have selected := of_decide_eq_true edge
  change parent.val = 1 ∧ (0 : Nat) = 2 at selected
  omega

private theorem empty_phase (signal : ParentSignal signature) (sample : signature.binary.Assignment) :
    signalPhase (S := signature) NodeSet.empty signal sample = false := rfl

private theorem small_phase (signal : ParentSignal signature) (sample : signature.binary.Assignment) :
    signalPhase witness.small signal sample =
      Bool.xor (sample rootNode) (signal rootNode (rootParents (sample actionNode))) := by
  change Bool.xor false (Bool.xor (sample rootNode) (signal rootNode (fun parent _edge => sample parent))) = _
  rw [Bool.false_xor]
  exact congrArg (Bool.xor (sample rootNode))
    (congrArg (signal rootNode) (rootParents_unique (fun parent _edge => sample parent)))

private theorem outcome_phase (signal : ParentSignal signature) (sample : signature.binary.Assignment) :
    signalPhase outcomeMask signal sample = Bool.xor (sample outcomeNode) (signal outcomeNode emptyParents) := by
  change Bool.xor false (Bool.xor (sample outcomeNode) (signal outcomeNode (fun parent _edge => sample parent))) = _
  rw [Bool.false_xor]
  exact congrArg (Bool.xor (sample outcomeNode))
    (congrArg (signal outcomeNode) (emptyParents_unique (fun parent _edge => sample parent)))

/-- Only the eight ordinary observed Boolean assignments are reduced.
The original-alphabet and augmented latent assignment lists are not used. -/
private theorem numerator_samples (outcome action root : Bool) :
    signature.binary.assignmentEnumeration.filter
        (query.binary.operationKernel.numeratorEvent (reference outcome action root)) =
      [reference outcome false root, reference outcome true root] := by
  cases outcome <;> cases action <;> cases root <;> decide +kernel

private theorem condition_samples (outcome action root : Bool) :
    signature.binary.assignmentEnumeration.filter
        (query.binary.operationKernel.conditionEvent (reference outcome action root)) =
      [reference false false root, reference true false root,
        reference false true root, reference true true root] := by
  cases outcome <;> cases action <;> cases root <;> decide +kernel

private theorem reference_outcome (outcome action root : Bool) :
    reference outcome action root outcomeNode = outcome := rfl

private theorem reference_action (outcome action root : Bool) :
    reference outcome action root actionNode = action := rfl

private theorem reference_root (outcome action root : Bool) :
    reference outcome action root rootNode = root := rfl

/-- The four literal row scalars are computed once, independently of the
parent functions and shared prior.  At a conflicting action value every
one is zero.  Factoring this small lookup out of the Boolean case analysis
keeps the checker from repeatedly reducing the full installed table data. -/
private theorem coefficient_values (outcome action root sampleOutcome sampleAction sampleRoot : Bool) :
    HedgeChannelTable.choiceCoefficient (leftTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot) (backgroundChoice witness NodeSet.empty) =
      (if sampleAction = action then 16777216 else 0) ∧
    HedgeChannelTable.choiceCoefficient (leftTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot) (backgroundChoice witness outcomeMask) =
      (if sampleAction = action then 2097152 else 0) ∧
    HedgeChannelTable.choiceCoefficient (rightTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot)
        (fullChoice witness witness.small (smallChannel witness) NodeSet.empty) =
      (if sampleAction = action then 262144 else 0) ∧
    HedgeChannelTable.choiceCoefficient (rightTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot)
        (fullChoice witness witness.small (smallChannel witness) outcomeMask) =
      (if sampleAction = action then 32768 else 0) := by
  cases action <;> cases sampleAction <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem left_empty_coefficient (outcome action root sampleOutcome sampleAction sampleRoot : Bool) :
    HedgeChannelTable.choiceCoefficient (leftTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot) (backgroundChoice witness NodeSet.empty) =
      (if sampleAction = action then 16777216 else 0) :=
  (coefficient_values outcome action root sampleOutcome sampleAction sampleRoot).1

private theorem left_background_coefficient (outcome action root sampleOutcome sampleAction sampleRoot : Bool) :
    HedgeChannelTable.choiceCoefficient (leftTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot) (backgroundChoice witness outcomeMask) =
      (if sampleAction = action then 2097152 else 0) :=
  (coefficient_values outcome action root sampleOutcome sampleAction sampleRoot).2.1

private theorem right_empty_coefficient (outcome action root sampleOutcome sampleAction sampleRoot : Bool) :
    HedgeChannelTable.choiceCoefficient (rightTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot)
        (fullChoice witness witness.small (smallChannel witness) NodeSet.empty) =
      (if sampleAction = action then 262144 else 0) :=
  (coefficient_values outcome action root sampleOutcome sampleAction sampleRoot).2.2.1

private theorem right_background_coefficient (outcome action root sampleOutcome sampleAction sampleRoot : Bool) :
    HedgeChannelTable.choiceCoefficient (rightTables witness) (target (reference outcome action root))
        (reference sampleOutcome sampleAction sampleRoot)
        (fullChoice witness witness.small (smallChannel witness) outcomeMask) =
      (if sampleAction = action then 32768 else 0) :=
  (coefficient_values outcome action root sampleOutcome sampleAction sampleRoot).2.2.2

/-! ## Actual fixed-reference masses before an independent environment sum -/

/-- The small signal's actual declared-parent read at the all-false source
reference.  Naming the read exposes no undeclared observed input at `R`. -/
def rootSignalAtFalse (signal : ParentSignal signature) : Bool :=
  signal rootNode (fun parent _edge => reference false false false parent)

/-- The background signal's actual empty-parent read at that same source
reference.  A shared-input construction will supply this frozen value. -/
def outcomeSignalAtFalse (signal : ParentSignal signature) : Bool :=
  signal outcomeNode (fun parent _edge => reference false false false parent)

private theorem rootSignalAtFalse_eq (signal : ParentSignal signature) :
    rootSignalAtFalse signal = signal rootNode (rootParents false) := by
  unfold rootSignalAtFalse
  exact congrArg (signal rootNode) (rootParents_unique (fun parent _edge => reference false false false parent))

private theorem outcomeSignalAtFalse_eq (signal : ParentSignal signature) :
    outcomeSignalAtFalse signal = signal outcomeNode emptyParents := by
  unfold outcomeSignalAtFalse
  exact congrArg (signal outcomeNode) (emptyParents_unique (fun parent _edge => reference false false false parent))

/-- The complete left joint cylinder, with its literal main-prior mass
kept symbolic.  This formula can be integrated over an independent latent
environment without reducing the augmented response-function support. -/
theorem left_joint_numerator_at_false (smallSignal backgroundSignal : ParentSignal signature) :
    (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
      (leftSignals witness rich smallSignal backgroundSignal) (target (reference false false false))
      (query.binary.operationKernel.numeratorEvent (reference false false false)) : Int) =
      ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
        (16777216 + 2097152 * FiniteProbRecord.characterSign (outcomeSignalAtFalse backgroundSignal)) := by
  rw [commonProjection_eq, outcomeSignalAtFalse_eq]
  apply congrArg (fun value : Int => ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) * value)
  simp only [commonProjection, numerator_samples, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    commonTerm, empty_phase, outcome_phase, reference_outcome, left_empty_coefficient, left_background_coefficient]
  cases backgroundSignal outcomeNode emptyParents <;> rfl

/-- The actual left evidence mass has no dependence on either local signal.
Both outcome values and every conflicting action cell are included. -/
theorem left_condition_numerator_at_false (smallSignal backgroundSignal : ParentSignal signature) :
    (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
      (leftSignals witness rich smallSignal backgroundSignal) (target (reference false false false))
      (query.binary.operationKernel.conditionEvent (reference false false false)) : Int) =
      ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) * 33554432 := by
  rw [commonProjection_eq]
  apply congrArg (fun value : Int => ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) * value)
  simp only [commonProjection, condition_samples, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    commonTerm, empty_phase, outcome_phase, reference_outcome, left_empty_coefficient, left_background_coefficient]
  cases backgroundSignal outcomeNode emptyParents <;> rfl

/-- The complete right-minus-left joint change before environment
integration.  Both full-small terms are present, including the interaction
between the small signal and the outcome background signal. -/
theorem joint_change_at_false (smallSignal backgroundSignal : ParentSignal signature) :
    projectedEventChange witness smallSignal backgroundSignal (target (reference false false false))
      (query.binary.operationKernel.numeratorEvent (reference false false false)) =
      ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
        (FiniteProbRecord.characterSign (rootSignalAtFalse smallSignal) *
          (262144 + 32768 * FiniteProbRecord.characterSign (outcomeSignalAtFalse backgroundSignal))) := by
  rw [changeProjection_eq, rootSignalAtFalse_eq, outcomeSignalAtFalse_eq]
  apply congrArg (fun value : Int => ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) * value)
  simp only [changeProjection, numerator_samples, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    smallTerm, empty_phase, small_phase, outcome_phase, reference_outcome, reference_action, reference_root,
    right_empty_coefficient, right_background_coefficient]
  simp only [Bool.true_eq_false, if_false, if_true, Int.zero_mul, Int.add_zero]
  cases smallSignal rootNode (rootParents false) <;> cases backgroundSignal outcomeNode emptyParents <;> rfl

/-- The complete evidence change still depends on the small signal.  A
shared-input proof must integrate this change as well as the joint change;
conditional separation is not inferred from the latter alone. -/
theorem condition_change_at_false (smallSignal backgroundSignal : ParentSignal signature) :
    projectedEventChange witness smallSignal backgroundSignal (target (reference false false false))
      (query.binary.operationKernel.conditionEvent (reference false false false)) =
      ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) *
        (524288 * FiniteProbRecord.characterSign (rootSignalAtFalse smallSignal)) := by
  rw [changeProjection_eq, rootSignalAtFalse_eq]
  apply congrArg (fun value : Int => ((PairRootChannels.prior graph.binary (channelCount witness)).den : Int) * value)
  simp only [changeProjection, condition_samples, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    smallTerm, empty_phase, small_phase, outcome_phase, reference_outcome, reference_action, reference_root,
    right_empty_coefficient, right_background_coefficient]
  simp only [Bool.true_eq_false, if_false, if_true, Int.zero_mul, Int.add_zero]
  cases smallSignal rootNode (rootParents false) <;> cases backgroundSignal outcomeNode emptyParents <;> rfl

/-- Complete finite normalized cross-products agree for every admissible
typed parent signal and every Boolean reference, not only constant signals
or the all-false source cell.  The parent-vector identities reduce the
arbitrary functions to their actual finite local reads; no undeclared
`U -> R` edge is added to make the small signal depend on the outcome. -/
private theorem projected_cross_equal (smallSignal backgroundSignal : ParentSignal signature)
    (outcome action root : Bool) :
    changeProjection smallSignal backgroundSignal (reference outcome action root)
        (query.binary.operationKernel.numeratorEvent (reference outcome action root)) *
      commonProjection backgroundSignal (reference outcome action root)
        (query.binary.operationKernel.conditionEvent (reference outcome action root)) =
    commonProjection backgroundSignal (reference outcome action root)
        (query.binary.operationKernel.numeratorEvent (reference outcome action root)) *
      changeProjection smallSignal backgroundSignal (reference outcome action root)
        (query.binary.operationKernel.conditionEvent (reference outcome action root)) := by
  simp only [changeProjection, commonProjection, numerator_samples, condition_samples,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [smallTerm, commonTerm, empty_phase, small_phase, outcome_phase,
    reference_outcome, reference_action, reference_root, left_empty_coefficient, left_background_coefficient,
    right_empty_coefficient, right_background_coefficient]
  generalize smallSignal rootNode (rootParents false) = smallFalse
  generalize smallSignal rootNode (rootParents true) = smallTrue
  generalize backgroundSignal outcomeNode emptyParents = background
  cases outcome <;> cases action <;> cases root <;>
    cases smallFalse <;> cases smallTrue <;> cases background <;> decide +kernel

private theorem reference_complete (assignment : signature.binary.Assignment) :
    reference (assignment outcomeNode) (assignment actionNode) (assignment rootNode) = assignment := by
  funext node
  have cases : node = outcomeNode ∨ node = actionNode ∨ node = rootNode := by
    have bound := node.isLt
    change node.val < 3 at bound
    have values : node.val = 0 ∨ node.val = 1 ∨ node.val = 2 := by omega
    exact values.elim (fun same => Or.inl (Fin.ext same))
      (fun remaining => Or.inr (remaining.elim (fun same => Or.inl (Fin.ext same))
        (fun same => Or.inr (Fin.ext same))))
  rcases cases with outcome | action | root
  · subst node; rfl
  · subst node; rfl
  · subst node; rfl

/-- No choice of the current installation's typed small/background parent
signals separates any conditional cell on this genuine irreducible fixture.
The actual full projected changes and actual left masses are retained;
their common prior mass is factored symbolically and cancels algebraically.

This is a universal statement about this installed family on this graph,
not an exhausted bounded signal search.  The companion's shared-latent
counterexample proves that it is a construction-family limit, not
identifiability of the query or impossibility of general completeness. -/
theorem normalized_change_zero (smallSignal backgroundSignal : ParentSignal signature)
    (assignment : signature.binary.Assignment) :
    normalizedCellChange witness rich smallSignal backgroundSignal assignment = 0 := by
  rw [← reference_complete assignment]
  let outcome := assignment outcomeNode
  let action := assignment actionNode
  let root := assignment rootNode
  change projectedEventChange witness smallSignal backgroundSignal (target (reference outcome action root))
        (query.binary.operationKernel.numeratorEvent (reference outcome action root)) *
      (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
        (leftSignals witness rich smallSignal backgroundSignal) (target (reference outcome action root))
        (query.binary.operationKernel.conditionEvent (reference outcome action root)) : Int) -
    (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
        (leftSignals witness rich smallSignal backgroundSignal) (target (reference outcome action root))
        (query.binary.operationKernel.numeratorEvent (reference outcome action root)) : Int) *
      projectedEventChange witness smallSignal backgroundSignal (target (reference outcome action root))
        (query.binary.operationKernel.conditionEvent (reference outcome action root)) = 0
  rw [changeProjection_eq, changeProjection_eq, commonProjection_eq, commonProjection_eq]
  apply Int.sub_eq_zero.mpr
  let mass : Int := (PairRootChannels.prior graph.binary (channelCount witness)).den
  calc
    _ = (mass * mass) *
        (changeProjection smallSignal backgroundSignal (reference outcome action root)
            (query.binary.operationKernel.numeratorEvent (reference outcome action root)) *
          commonProjection backgroundSignal (reference outcome action root)
            (query.binary.operationKernel.conditionEvent (reference outcome action root))) := by ac_rfl
    _ = (mass * mass) *
        (commonProjection backgroundSignal (reference outcome action root)
            (query.binary.operationKernel.numeratorEvent (reference outcome action root)) *
          changeProjection smallSignal backgroundSignal (reference outcome action root)
            (query.binary.operationKernel.conditionEvent (reference outcome action root))) := by
      rw [projected_cross_equal]
    _ = _ := by ac_rfl

/-- The installed pair agrees on the actual entire conditional kernel for
all typed parent signals.  This uses the full likelihood-to-kernel bridge,
not only a proposed vanishing polynomial.  The companion's independently
constructed shared-latent pair refutes identifiability in the same graph. -/
theorem independent_channel_conditionals_equivalent
    (smallSignal backgroundSignal : ParentSignal signature) :
    query.binary.ValueEquivalent (leftModel witness rich smallSignal backgroundSignal)
      (rightModel witness smallSignal backgroundSignal) :=
  (binary_conditionals_equivalent_iff_normalizedCellChanges_zero witness rich smallSignal backgroundSignal).mpr
    (normalized_change_zero smallSignal backgroundSignal)

end HedgeChannelLatentBoundary
end Examples
end Causality
end Thesis
