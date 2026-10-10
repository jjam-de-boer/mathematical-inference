import Thesis.CausalTransport.ConditionalFailureActivationInteraction

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction HedgeChannelEnvironmentInstallation

/-!
# Retain conditioned rows and assemble the actual complete Small phase

The normalized path/activation construction supplies a legal signal and a
supported odd outcome character.  A mandatory hedge row cannot be omitted
merely because it is outside that interaction.  There is, however, no need
to route an additional *conditioned* row: outside the actual fused union the
signal is exactly its own bit, which vanishes on the original evidence cylinder.

We therefore retain every original conditioner alongside the actual union.
Their missing rows are genuinely present and individually even, not erased
from Small or installed under a different alphabet.  Full-cylinder conservation
is preserved.  When the pivot is in Small and all Small rows are covered by
this completed selection, the outside-Small rows are even and conservation
derives the actual Small phase's oddness.  The full covariance construction
then gives positive countermodels for the unchanged original conditional query.

Only graph membership/coverage certificates remain premises of this adapter;
the masks, direction, row parities, outcome character and cylinder matching
are constructed from the actual normal form.  It does not assert that those
coverage certificates hold universally.  Unconditioned missing Small rows
still need real routing, and a pivot outside Small still needs oddness transfer.
The entire adapter now uses a retained conditioner and actual cut policy,
without original-graph latest maximality.  The direction and parity proofs
are the same general normalized-path construction at that supplied vertex.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

namespace ConditionalBackdoorPathNormalForm

variable (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

/-- Complete the actual interaction with every original conditioner.
Boolean union retains overlaps once, including conditioned collider sinks. -/
def smallInteractionRows : NodeSet S := NodeSet.union (normal.activationInteractionRows pivot forest) query.condition

/-- Outside the actual interaction the installed signal is precisely its
own bit.  This concerns the complete original cube, not only the direction
or one conditioned sample, and does not require a proposed zero-valued route. -/
theorem activationInteraction_rowPhase_outside (child : Fin S.count)
    (outside : normal.activationInteractionRows pivot forest child = false) (point : Cube graph) :
    ((normal.activationInteractionSignal pivot forest).rowPhase child).value point = cubeSample graph point child :=
  LinearSignal.absorbSuccessor_rowPhase_outside_union _ _ _ _
    (normal.activationTraceSuccessor_wellFormed pivot forest) child outside point

/-- The added original conditioners cannot be acted-on rows.  Actual
interaction rows already inherit action freedom from the graph cuts and traces. -/
theorem smallInteractionRows_action_free (child : Fin S.count)
    (selected : normal.smallInteractionRows pivot forest child = true) : query.action child = false := by
  rcases Bool.or_eq_true_iff.mp selected with original | conditioned
  · exact normal.activationInteractionRows_action_free pivot forest child original
  · cases acted : query.action child with
    | false => rfl
    | true =>
        have free := query.action_condition_disjoint child acted
        exact False.elim (Bool.false_ne_true (free.symm.trans conditioned))

/-- Every new row is truly retained and has zero phase on the entire
original conditioning cylinder.  The result fixes its own coordinate by
actual evidence membership; it does not posit a matched denominator. -/
theorem smallInteraction_new_row_zero (child : Fin S.count)
    (outside : normal.activationInteractionRows pivot forest child = false)
    (conditioned : query.condition child = true) (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    ((normal.activationInteractionSignal pivot forest).rowPhase child).value point = false := by
  rw [normal.activationInteraction_rowPhase_outside pivot forest child outside]
  exact cubeSample_false_of_mem graph (NodeSet.union query.action query.condition) point listed child
    (NodeSet.subset_union_right _ _ child conditioned)

/-- Completing with the original conditioners preserves the selected
outcome character on every supported cube assignment.  The fold retains
each added row once; its zero contribution is proved from real evidence. -/
theorem smallInteraction_conditionalPhase (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    ((normal.activationInteractionSignal pivot forest).forestPhase (normal.smallInteractionRows pivot forest)).value point =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
  calc
    _ = ((normal.activationInteractionSignal pivot forest).forestPhase (normal.activationInteractionRows pivot forest)).value point := by
      simp only [LinearSignal.forestPhase_value, NodeSet.members, List.foldl_filter]
      apply foldl_congr
      intro total child
      cases original : normal.activationInteractionRows pivot forest child with
      | true => simp only [smallInteractionRows, NodeSet.union, original, Bool.true_or, if_true]
      | false =>
          cases conditioned : query.condition child with
          | false => simp only [smallInteractionRows, NodeSet.union, original, conditioned, Bool.false_or, Bool.false_eq_true, if_false]
          | true =>
              simp only [smallInteractionRows, NodeSet.union, original, conditioned, Bool.false_or,
                Bool.false_eq_true, if_false, if_true]
              rw [normal.smallInteraction_new_row_zero pivot forest child original conditioned point listed, Bool.xor_false]
    _ = _ := normal.activationInteraction_conditionalPhase pivot forest point listed

/-- Every completed selected row except the pivot is even in the actual
supported direction.  Newly retained conditioners use their own zero bit;
original interaction rows use the already proved actual path/trace parities. -/
theorem smallInteraction_selected_even (child : Fin S.count)
    (selected : normal.smallInteractionRows pivot forest child = true) (different : child ≠ pivot.node) :
    ((normal.activationInteractionSignal pivot forest).rowPhase child).value normal.pathDirection = false := by
  cases original : normal.activationInteractionRows pivot forest child with
  | true => exact normal.activationInteraction_selected_even pivot forest child original different
  | false =>
      have conditioned : query.condition child = true := by
        simpa only [smallInteractionRows, NodeSet.union, original, Bool.false_or] using selected
      exact normal.smallInteraction_new_row_zero pivot forest child original conditioned normal.pathDirection normal.pathDirection_member

end ConditionalBackdoorPathNormalForm

/-! ## The mandatory Small forest is retained in the actual covariance witness -/

/-- Assemble a complete Small parity witness from the normalized graph
construction when actual membership/coverage places its unique odd pivot
in Small.  No parity, character, conservation or probability-gap premise
is supplied.  Every Small row is retained; the background is exactly the
completed interaction's difference from Small, not a guessed disjoint copy. -/
def HedgeChannelEnvironmentInstallation.ConditionalParityWitness.ofNormalizedActivation
    (w : HedgeWitness graph query.jointNumerator) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)
    (pivotInSmall : w.small pivot.node = true)
    (containsSmall : NodeSet.Subset w.small (normal.smallInteractionRows pivot forest)) :
    ConditionalParityWitness w (normal.activationInteractionSignal pivot forest) (normal.activationInteractionSignal pivot forest) := by
  let installed := normal.activationInteractionSignal pivot forest
  let selected := NodeSet.diff (normal.smallInteractionRows pivot forest) w.small
  have outsideSmall : forall child, selected child = true -> w.small child = false := by
    intro child chosen
    simpa only [selected, NodeSet.diff, Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp chosen).2
  have even : forall child, selected child = true -> (installed.rowPhase child).value normal.pathDirection = false := by
    intro child chosen
    apply normal.smallInteraction_selected_even pivot forest child (Bool.and_eq_true_iff.mp chosen).1
    intro equal
    have outside := outsideSmall child chosen
    rw [equal, pivotInSmall] at outside
    cases outside
  have whole : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) ->
      Bool.xor ((installed.forestPhase w.small).value point)
        ((selectedPhase _ S.count selected installed.rowPhase).value point) =
          (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
    intro point listed
    rw [LinearSignal.selectedPhase_value_eq_forestPhase,
      ← LinearSignal.forestPhase_union_of_disjoint installed w.small selected
        (NodeSet.disjoint_diff (normal.smallInteractionRows pivot forest) w.small), NodeSet.union_diff_eq containsSmall]
    exact normal.smallInteraction_conditionalPhase pivot forest point listed
  have matching : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) ->
      ((installed.forestPhase w.small).xor (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome)))).value point =
        (selectedPhase _ S.count selected installed.rowPhase).value point := by
    intro point listed
    have conserved := whole point listed
    change Bool.xor ((installed.forestPhase w.small).value point)
      ((maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point) = _
    rw [← conserved]
    generalize (installed.forestPhase w.small).value point = smallBit
    generalize (selectedPhase _ S.count selected installed.rowPhase).value point = backgroundBit
    cases smallBit <;> cases backgroundBit <;> rfl
  have smallOdd : (installed.forestPhase w.small).value normal.pathDirection = true := by
    have conserved := whole normal.pathDirection normal.pathDirection_member
    rw [normal.activationInteraction_outcome_odd pivot,
      selectedPhase_value_eq_false_of_even _ _ selected installed.rowPhase normal.pathDirection even, Bool.xor_false] at conserved
    exact conserved
  exact {
    outcomeMask := cubeMask graph (NodeSet.singleton normal.outcome)
    outcomeMask_member := normal.activationInteraction_outcome_mask_member pivot
    direction := normal.pathDirection
    direction_member := normal.pathDirection_member
    small_odd := smallOdd
    outcome_odd := normal.activationInteraction_outcome_odd pivot
    selected := selected
    selected_outside_small := outsideSmall
    selected_avoids_action := fun child chosen => normal.smallInteractionRows_action_free pivot forest child
      (Bool.and_eq_true_iff.mp chosen).1
    selected_even := even
    matching := matching
  }

/-- Construct positive full-original-alphabet countermodels from the
actual normalized interaction and its certified complete Small coverage.
Both changing evidence masses and every original queried outcome are
retained by the proved full-covariance and original-label construction. -/
noncomputable def conditionalCounterexampleOfNormalizedActivation
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)
    (pivotInSmall : w.small pivot.node = true)
    (containsSmall : NodeSet.Subset w.small (normal.smallInteractionRows pivot forest)) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity w rich (normal.activationInteractionSignal pivot forest) (normal.activationInteractionSignal pivot forest)
    (.ofNormalizedActivation w pivot normal forest pivotInSmall containsSmall)

end Causality
end Thesis
