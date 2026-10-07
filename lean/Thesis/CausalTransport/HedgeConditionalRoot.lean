import Thesis.CausalTransport.HedgePositive
import Thesis.Causality.CoordinateAssignment

namespace Thesis
namespace Causality

open Probability

/-!
# A genuinely separated root conditional for an arbitrary hedge

The positive carrier pair separates the joint common-root parity for every
hedge.  That fact does not separate the conditional at a predetermined root:
the change could instead be carried by its conditioning marginal.  Here the
full-coordinate uniqueness theorem selects an actual root and an actual
assignment of the other roots at which the conditional differs.

The selection is made in the compact dependent product of the root alphabets.
Both full-support witnesses are derived from the same positive SCMs at the
original intervention, and the parity event is transported through literal
restriction and extension.  The returned witness is then stated in terms of
the models' real observed interventional records and finally their real latent
priors.  No root, cell, support witness, or alternative label is chosen from
a proposition.  The original action values stay fixed throughout the search.

This is a general multi-root signal-selection step, not the universal
conditional countermodel theorem.  A later collider or active-path construction
must still place this signal in the original outcome/conditioning geometry
and preserve the full observed law of the installed pair.  In particular,
the selected root need not be an admissible incoming-parent collider pivot.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- Every common root avoids the original action.  This is derived from the
small forest, not assumed by the conditional selector. -/
theorem HedgeWitness.action_roots_disjoint (w : HedgeWitness G q) : NodeSet.Disjoint q.action w.roots := by
  apply NodeSet.Disjoint.symm
  intro node root
  exact w.small_avoids_intervention node ((w.small_forest.roots_exact node).mp root).1

namespace HedgeConditionalRoot

/-- The compact law is the actual SCM's observed interventional law with only
the common-root coordinates retained.  Its atoms and weights are not replaced
by a separately supplied positive table. -/
def coordinateLaw (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (model : ExactModel S) :
    FiniteProbRecord w.roots.CoordinateAssignment :=
  model.interventionalCoordinateLaw (hedgeDoSecond rich q.action) w.roots

theorem coordinateLaw_fullSupport (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (model : ExactModel S) (positive : ObservationallyPositive model) :
    FiniteProductConditionals.FullSupport (coordinateLaw w rich model) :=
  model.interventionalCoordinateLaw_fullSupport positive q.action w.roots w.action_roots_disjoint rich.second

/-- Parity on compact values, with a supplied background outside the roots.
The background is immaterial because root parity is a local event. -/
def parityEvent (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) : Event w.roots.CoordinateAssignment :=
  fun values => hedgeRootParityEvent rich w.roots (w.roots.extendCoordinates values rich.first)

private theorem parity_select (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (sample : S.Assignment) :
    parityEvent w rich (w.roots.selectCoordinates sample) = hedgeRootParityEvent rich w.roots sample :=
  hedgeRootParityEvent_local rich w.roots _ _
    (w.roots.extendCoordinates_select_of_true sample rich.first)

private theorem parity_probVal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (model : ExactModel S) :
    QProb.Equiv ((coordinateLaw w rich model).probVal (parityEvent w rich))
      (model.interventionalValue (hedgeDoSecond rich q.action) (hedgeRootParityEvent rich w.roots)) :=
  QProb.equiv_trans ((model.interventionalDist (hedgeDoSecond rich q.action)).map_probVal
    w.roots.selectCoordinates (parityEvent w rich))
    ((model.interventionalDist (hedgeDoSecond rich q.action)).probVal_congr _ _ (parity_select w rich))

/-- The observed evidence fixes every common root except the selected one.
It is a full-label cylinder, rather than just a test of their parity bits. -/
def context (w : HedgeWitness G q) (root : Fin S.count) (reference : S.Assignment) : Event S.Assignment :=
  Kernel.agreesOn (NodeSet.diff w.roots (NodeSet.singleton root)) reference

/-- Actual constructive signal data for the fixed positive carrier pair.
The evidence masses can differ: each probability uses its own model's real
conditioning denominator.  In a nonbinary alphabet the selected label need
not be the old distinguished `second` label. -/
structure Witness (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) where
  root : Fin S.count
  root_selected : w.roots root = true
  reference : S.Assignment
  action_values : forall node, q.action node = true -> reference node = rich.second node
  left_supported : ((w.largeCarrierDefectParityModel rich).interventionalDist (hedgeDoSecond rich q.action)).EventPositive
    (context w root reference)
  right_supported : ((w.smallCarrierDefectParityModel rich).interventionalDist (hedgeDoSecond rich q.action)).EventPositive
    (context w root reference)
  separated : Not (QProb.Equiv
    ((((w.largeCarrierDefectParityModel rich).interventionalDist (hedgeDoSecond rich q.action)).conditionOn
      (context w root reference) left_supported).probVal (fun sample => decide (sample root = reference root)))
    ((((w.smallCarrierDefectParityModel rich).interventionalDist (hedgeDoSecond rich q.action)).conditionOn
      (context w root reference) right_supported).probVal (fun sample => decide (sample root = reference root))))

/-- Search every finite root coordinate and label context.  The already
proved joint parity gap rules out exhaustion, so the matched option returns
data without eliminating an existential proof into a chosen root. -/
def select (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) : Witness w rich := by
  let left := w.largeCarrierDefectParityModel rich
  let right := w.smallCarrierDefectParityModel rich
  let leftSupport := coordinateLaw_fullSupport w rich left (w.largeCarrierDefectParityModel_positive rich)
  let rightSupport := coordinateLaw_fullSupport w rich right (w.smallCarrierDefectParityModel_positive rich)
  have parityGap : Not (QProb.Equiv ((coordinateLaw w rich left).probVal (parityEvent w rich))
      ((coordinateLaw w rich right).probVal (parityEvent w rich))) := by
    intro same
    exact w.carrierDefectParityModels_rootParity_not_equiv_doSecond rich
      (QProb.equiv_trans (QProb.equiv_symm (parity_probVal w rich left))
        (QProb.equiv_trans same (parity_probVal w rich right)))
  let chosen := FiniteProductConditionals.disagreementOfEventGap
    (coordinateLaw w rich left) (coordinateLaw w rich right) leftSupport rightSupport
    w.roots.coordinateAssignmentEnumeration w.roots.coordinateAssignmentEnumeration_nodup
    w.roots.coordinateAssignmentEnumeration_complete (parityEvent w rich) parityGap
  let root := w.roots.members.get chosen.pivot
  let reference := w.roots.extendCoordinates chosen.reference rich.second
  have referenceCoordinates : w.roots.selectCoordinates reference = chosen.reference :=
    w.roots.selectCoordinates_extend chosen.reference rich.second
  have leftPositive := w.roots.coordinateContext_positive (left.interventionalDist (hedgeDoSecond rich q.action))
    leftSupport chosen.pivot reference
  have rightPositive := w.roots.coordinateContext_positive (right.interventionalDist (hedgeDoSecond rich q.action))
    rightSupport chosen.pivot reference
  have leftConditional := w.roots.conditionalAt_probVal (left.interventionalDist (hedgeDoSecond rich q.action))
    leftSupport chosen.pivot reference
  have rightConditional := w.roots.conditionalAt_probVal (right.interventionalDist (hedgeDoSecond rich q.action))
    rightSupport chosen.pivot reference
  rw [referenceCoordinates] at leftConditional rightConditional
  refine ⟨root, (NodeSet.mem_members_iff w.roots root).mp (List.get_mem w.roots.members chosen.pivot),
    reference, ?_, leftPositive, rightPositive, ?_⟩
  · intro node selected
    exact w.roots.extendCoordinates_of_false chosen.reference rich.second node (w.action_roots_disjoint node selected)
  · intro equivalent
    exact chosen.separated (QProb.equiv_trans leftConditional
      (QProb.equiv_trans equivalent (QProb.equiv_symm rightConditional)))

namespace Witness

variable {w : HedgeWitness G q} {rich : ObservedSignature.ValueRich S}

/-- Reserve the selected full label for a true readout.  If that label is the
old `first`, use the old `second` as its different companion; otherwise use
the old `first`.  This finite equality test works for arbitrary rich alphabets
without choosing a label outside a singleton or rebuilding either base SCM.

The intervened coordinates retain the old second values, by `action_values`.
Only a later readout construction uses this new label presentation: the two
source models in the witness still use the original carrier presentation. -/
def readoutValues (witness : Witness w rich) : ObservedSignature.ValueRich S where
  first := fun node => if witness.reference node = rich.first node then rich.second node else rich.first node
  second := witness.reference
  first_enumerated := fun node => S.value_complete node _
  second_enumerated := fun node => S.value_complete node _
  different := by
    intro node
    by_cases same : witness.reference node = rich.first node
    · simp only [same, if_true]
      exact Ne.symm (rich.different node)
    · simp only [same, if_false]
      exact Ne.symm same

/-- The newly selected readout labels do not change the original intervention.
This guards against turning a conditional signal at one action value into a
purported counterexample evaluated at another action value. -/
theorem readoutValues_doSecond_eq (witness : Witness w rich) :
    hedgeDoSecond witness.readoutValues q.action = hedgeDoSecond rich q.action := by
  funext node
  cases selected : q.action node with
  | false => simp only [hedgeDoSecond, selected, Bool.false_eq_true, if_false]
  | true => simp only [hedgeDoSecond, selected, if_true, readoutValues, witness.action_values node selected]

/-- Pull the actual observed evidence back to a model's own latent space.
The two carrier spaces need not be identified to compare these conditionals. -/
def sourceContext (witness : Witness w rich) (model : ExactModel S) : Event model.latent.Assignment :=
  fun unit => context w witness.root witness.reference (model.evalUnder (hedgeDoSecond rich q.action) unit)

theorem left_source_supported (witness : Witness w rich) :
    (w.largeCarrierDefectParityModel rich).prior.EventPositive (witness.sourceContext (w.largeCarrierDefectParityModel rich)) :=
  ((w.largeCarrierDefectParityModel rich).prior.map_eventPositive_iff
    ((w.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action))
    (context w witness.root witness.reference)).mp witness.left_supported

theorem right_source_supported (witness : Witness w rich) :
    (w.smallCarrierDefectParityModel rich).prior.EventPositive (witness.sourceContext (w.smallCarrierDefectParityModel rich)) :=
  ((w.smallCarrierDefectParityModel rich).prior.map_eventPositive_iff
    ((w.smallCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action))
    (context w witness.root witness.reference)).mp witness.right_supported

/-- The selected gap holds in the genuinely conditioned latent priors.
This is the source-level input needed by a posterior channel construction,
not a newly assumed gap for a modified collider or a different intervention. -/
theorem source_separated (witness : Witness w rich) :
    Not (QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).prior.conditionOn (witness.sourceContext (w.largeCarrierDefectParityModel rich))
        witness.left_source_supported).probVal (fun unit =>
          decide ((w.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action) unit witness.root = witness.reference witness.root)))
      (((w.smallCarrierDefectParityModel rich).prior.conditionOn (witness.sourceContext (w.smallCarrierDefectParityModel rich))
        witness.right_source_supported).probVal (fun unit =>
          decide ((w.smallCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action) unit witness.root = witness.reference witness.root)))) := by
  intro equivalent
  have left := (w.largeCarrierDefectParityModel rich).prior.map_conditionOn_probVal
    ((w.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action))
    (context w witness.root witness.reference) (fun sample => decide (sample witness.root = witness.reference witness.root))
    witness.left_supported
  have right := (w.smallCarrierDefectParityModel rich).prior.map_conditionOn_probVal
    ((w.smallCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action))
    (context w witness.root witness.reference) (fun sample => decide (sample witness.root = witness.reference witness.root))
    witness.right_supported
  exact witness.separated (QProb.equiv_trans left (QProb.equiv_trans equivalent (QProb.equiv_symm right)))

/-- The same source gap is a genuine distinguished-bit gap under the selected
readout presentation, including when the separated label was neither old
parity label.  This is the full-label-to-Boolean interface for a collider;
it does not assume a gap after installing the collider itself. -/
theorem source_readout_separated (witness : Witness w rich) :
    Not (QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).prior.conditionOn (witness.sourceContext (w.largeCarrierDefectParityModel rich))
        witness.left_source_supported).probVal (fun unit => hedgeIsSecond witness.readoutValues witness.root
          ((w.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action) unit witness.root)))
      (((w.smallCarrierDefectParityModel rich).prior.conditionOn (witness.sourceContext (w.smallCarrierDefectParityModel rich))
        witness.right_source_supported).probVal (fun unit => hedgeIsSecond witness.readoutValues witness.root
          ((w.smallCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action) unit witness.root)))) :=
  witness.source_separated

end Witness
end HedgeConditionalRoot

/-- An arbitrary hedge has an explicit separated common-root conditional in
its positive carrier pair.  No sole-root hypothesis is required. -/
def HedgeWitness.conditionedRoot (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    HedgeConditionalRoot.Witness w rich := HedgeConditionalRoot.select w rich

end Causality
end Thesis
