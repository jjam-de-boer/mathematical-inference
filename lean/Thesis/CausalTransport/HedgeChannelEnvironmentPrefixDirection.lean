import Thesis.CausalTransport.HedgeChannelEnvironmentAbsorption
import Thesis.CausalTransport.HedgeChannelEnvironmentMaskPhase

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability PathSpecification HedgeChannelInstallation FiniteBooleanInteraction

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}
    {domain : NodeSet S} {successor : ForestChild S} {source : Fin S.count}

/-!
# Exact proper-prefix directions at receiving interaction rows

A complete successor-path flip has one odd source but also flips its endpoint.
For conditional transfer that endpoint may be fixed evidence, so the usable
direction flips only the proper prefix.  Its exact local-source parity has
two boundary indicators: the original source and the receiving endpoint.
They cancel on a zero-edge path, where the direction is genuinely zero.

The cube direction below retains all original observed and reserved-root
coordinates.  It changes no reserved input and is supported whenever the
actual proper prefix avoids the supplied fixed set.  Outside a receiving
interaction, its absorbed row contribution is precisely the source indicator.
At an interaction row the endpoint contribution is added to the original
signal's actual value on this prefix direction.  That original term is kept:
an omitted path fork can feed real original interaction rows, so it cannot
be declared zero merely because the fork is outside the selected interaction.

XOR with another supported direction therefore has an exact row-by-row
update rule, not a claimed universal successful transfer.  The remaining
graph argument must account for every receiving residual and every original
outside-Small parity before applying the countermodel theorem.
-/

namespace LinearSignal

/-- The actual proper-prefix observed flip, with every original reserved
coordinate fixed to false.  No globally shared input or new root is introduced. -/
def successorPrefixDirection (path : SuccessorPath domain successor source) : Cube graph :=
  joinCube graph (fun _ => false) path.prefixBits

/-- The observed block is exactly the constructed nonendpoint path mask. -/
theorem successorPrefixDirection_sample (path : SuccessorPath domain successor source) :
    cubeSample graph (successorPrefixDirection (graph := graph) path) = path.prefixBits :=
  cubeSample_joinCube _ _ _

/-- Original independent pair inputs are unchanged by this correction. -/
theorem successorPrefixDirection_environment (path : SuccessorPath domain successor source) :
    cubeEnvironment graph (successorPrefixDirection (graph := graph) path) = (fun _ => false) :=
  cubeEnvironment_joinCube _ _ _

/-- A certified actual forest row sees exactly the two boundary sources,
at every child.  This remains valid at merges and for the zero-edge path. -/
theorem successorPrefixDirection_rowPhase (path : SuccessorPath domain successor source)
    (wellFormed : childWellFormedBool domain successor = true) (child : Fin S.count) :
    ((ofSuccessor (G := graph) successor).rowPhase child).value (successorPrefixDirection path) =
      Bool.xor (decide (child = source)) (decide (child = path.endpoint)) := by
  rw [ofSuccessor_rowPhase domain successor wellFormed, successorPrefixDirection_sample, path.prefixBits_localSource]

/-- A changed policy has the same two-boundary correction when it agrees
at every flipped proper vertex.  The receiving endpoint has bit zero, so
its new continuation is irrelevant.  In particular a path stopped at a
fork may be continued into an actual head without inventing a stop proof
for that new map or changing the literal old first-contact list. -/
theorem successorPrefixDirection_rowPhase_of_agrees_on_prefix
    (path : SuccessorPath domain successor source) (nextDomain : NodeSet S) (next : ForestChild S)
    (wellFormed : childWellFormedBool nextDomain next = true)
    (agrees : forall parent, path.prefixBits parent = true -> next parent = successor parent)
    (child : Fin S.count) :
    ((ofSuccessor (G := graph) next).rowPhase child).value (successorPrefixDirection path) =
      Bool.xor (decide (child = source)) (decide (child = path.endpoint)) := by
  rw [ofSuccessor_rowPhase nextDomain next wellFormed, successorPrefixDirection_sample]
  have same : hedgeRoutingIncomingBits next path.prefixBits child =
      hedgeRoutingIncomingBits successor path.prefixBits child := by
    unfold hedgeRoutingIncomingBits hedgeRoutingParentEntry
    apply foldl_congr
    intro total parent
    cases flipped : path.prefixBits parent with
    | false => simp only [ite_self]
    | true => rw [agrees parent flipped]
  change Bool.xor (path.prefixBits child) (hedgeRoutingIncomingBits next path.prefixBits child) = _
  rw [same]
  exact path.prefixBits_localSource child

private theorem prefixBits_false_of_fixed (path : SuccessorPath domain successor source) (fixed : NodeSet S)
    (free : forall child, child ∈ path.nodes -> child ≠ path.endpoint -> fixed child = false)
    (child : Fin S.count) (selected : fixed child = true) : path.prefixBits child = false := by
  apply Bool.eq_false_iff.mpr
  intro positive
  have parts := (path.prefixBits_eq_true_iff child).mp positive
  exact Bool.false_ne_true ((free child parts.1 parts.2).symm.trans selected)

/-- Support on the complete supplied observed cylinder follows from
proper-prefix freedom alone.  The receiving endpoint need not be free. -/
theorem successorPrefixDirection_member (path : SuccessorPath domain successor source) (fixed : NodeSet S)
    (free : forall child, child ∈ path.nodes -> child ≠ path.endpoint -> fixed child = false) :
    successorPrefixDirection (graph := graph) path ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count) (cubeMask graph fixed) := by
  rw [FiniteProduct.BooleanBlocks.cylinder_member_iff]
  simp only [cubeMask, successorPrefixDirection, joinCube, FiniteProduct.BooleanBlocks.leftBlock_join,
    FiniteProduct.BooleanBlocks.rightBlock_join]
  constructor
  · rw [FiniteProduct.falseCylinderEnumeration_member_iff]
    intro root impossible
    cases impossible
  · rw [FiniteProduct.falseCylinderEnumeration_member_iff]
    exact prefixBits_false_of_fixed path fixed free

/-- A mask avoided by the actual proper prefix has zero character at
this correction, even if its endpoint belongs to the mask. -/
theorem successorPrefixDirection_mask_zero (path : SuccessorPath domain successor source) (nodes : NodeSet S)
    (free : forall child, child ∈ path.nodes -> child ≠ path.endpoint -> nodes child = false) :
    (maskPhase _ (cubeMask graph nodes)).value (successorPrefixDirection path) = false := by
  rw [cubeMaskPhase_value, successorPrefixDirection_sample]
  apply nodeXor_of_zero
  exact prefixBits_false_of_fixed path nodes free

/-- Outside the interaction, the installed correction is the actual
forest's two-boundary parity.  No original-row residual is present there. -/
theorem absorbedPrefixDirection_row_outside (data : LinearSignal graph) (interaction : NodeSet S)
    (path : SuccessorPath domain successor source) (wellFormed : childWellFormedBool domain successor = true)
    (child : Fin S.count) (outside : interaction child = false) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value (successorPrefixDirection path) =
      Bool.xor (decide (child = source)) (decide (child = path.endpoint)) := by
  rw [absorbSuccessor_rowPhase_outside data interaction successor child outside]
  exact successorPrefixDirection_rowPhase path wellFormed child

/-- At a receiving row, preserve the original signal's real prefix reads
and add the exact boundary correction.  Prefix freedom removes only that
row's own bit; it does not erase reads of off-interaction path forks. -/
theorem absorbedPrefixDirection_row_inside (data : LinearSignal graph) (interaction : NodeSet S)
    (path : SuccessorPath domain successor source) (wellFormed : childWellFormedBool domain successor = true)
    (free : forall node, node ∈ path.nodes -> node ≠ path.endpoint -> interaction node = false)
    (child : Fin S.count) (inside : interaction child = true) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value (successorPrefixDirection path) =
      Bool.xor ((data.rowPhase child).value (successorPrefixDirection path))
        (Bool.xor (decide (child = source)) (decide (child = path.endpoint))) := by
  rw [absorbSuccessor_rowPhase_inside data interaction successor child inside,
    successorPrefixDirection_rowPhase path wellFormed child, successorPrefixDirection_sample,
    prefixBits_false_of_fixed path interaction free child inside, Bool.xor_false]

/-- Apply the actual prefix correction by XOR on the unchanged original
cube.  This is data-level finite arithmetic, not a selected semantic witness. -/
def shiftBySuccessorPrefix (path : SuccessorPath domain successor source) (point : Cube graph) : Cube graph :=
  FiniteProduct.xorAssignment _ point (successorPrefixDirection path)

/-- Any installed homogeneous row has this exact update.  In particular
an odd receiving residual remains visible rather than being assumed away. -/
theorem shiftBySuccessorPrefix_rowPhase (data : LinearSignal graph)
    (path : SuccessorPath domain successor source) (point : Cube graph) (child : Fin S.count) :
    (data.rowPhase child).value (shiftBySuccessorPrefix path point) =
      Bool.xor ((data.rowPhase child).value point)
        ((data.rowPhase child).value (successorPrefixDirection path)) :=
  (data.rowPhase child).xor_additive point (successorPrefixDirection path)

/-- XOR of the original supported point and the proved supported prefix
stays on the full original cylinder; fixed coordinates remain false. -/
theorem shiftBySuccessorPrefix_member (path : SuccessorPath domain successor source) (fixed : NodeSet S)
    (free : forall child, child ∈ path.nodes -> child ≠ path.endpoint -> fixed child = false)
    (point : Cube graph) (listed : point ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count) (cubeMask graph fixed)) :
    shiftBySuccessorPrefix path point ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count) (cubeMask graph fixed) := by
  have prefixListed := successorPrefixDirection_member (graph := graph) path fixed free
  apply (FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mpr
  intro coordinate selected
  change Bool.xor (point coordinate) (successorPrefixDirection path coordinate) = false
  rw [(FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mp listed coordinate selected,
    (FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mp prefixListed coordinate selected]
  rfl

/-- A proper-prefix correction avoiding the queried outcome mask leaves
its character unchanged.  It can therefore transfer row parity without
destroying an already odd original outcome. -/
theorem shiftBySuccessorPrefix_maskPhase (path : SuccessorPath domain successor source) (nodes : NodeSet S)
    (free : forall child, child ∈ path.nodes -> child ≠ path.endpoint -> nodes child = false) (point : Cube graph) :
    (maskPhase _ (cubeMask graph nodes)).value (shiftBySuccessorPrefix path point) =
      (maskPhase _ (cubeMask graph nodes)).value point := by
  rw [shiftBySuccessorPrefix, (maskPhase _ (cubeMask graph nodes)).xor_additive,
    successorPrefixDirection_mask_zero path nodes free, Bool.xor_false]

end LinearSignal

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
