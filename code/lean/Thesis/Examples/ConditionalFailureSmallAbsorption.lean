import Thesis.CausalTransport.ConditionalFailureSmallAbsorption
import Thesis.Examples.ConditionalFailureSmallApproach

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureSmallAbsorption

open Probability PathSpecification FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureSmallApproach

/-!
# Actual all-Small absorption and first unconditioned contacts

The genuine three-valued hedge has Small `U,P` and original evidence `P,Z`.
Its stored boundary paths are `U -> P` and the singleton `P`.  Absorption
into that evidence keeps both original Small rows, uses the actual arrow
`U -> P`, stops at the shared receiving row, and excludes irrelevant `Z`
from the transmitting domain while still stopping there globally.

Adding unconditioned `U` to the receiving interaction deliberately makes its
first contact earlier than its conditioned boundary endpoint: the retained
trace is now the singleton `U`.  This checks that the constructor stops at
the first *interaction* contact, not only the first conditioner.  The original
query is unchanged; this is a different receiving-row selection, not new
evidence or a new countermodel query.

Finally the actual opaque normalized path and common cut policy receive the
same all-Small construction.  Coverage, action freedom, whole-cube conservation
and the full original-cylinder outcome character follow from the general
theorems, without evaluating normal-form search or supplying literal parity
and matching flags.  These regressions do not claim the remaining universal
outside-Small parity or Small-to-pivot oddness-transfer theorem.
-/

private theorem source_in_small : (witness false).small source = true := by decide +kernel
private theorem conditioner_in_small : (witness false).small firstConditioner = true := by decide +kernel

/-- All original conditioners are receiving rows in this first selection. -/
def receiving : NodeSet signature := (query false).condition

private theorem receives : NodeSet.Subset (query false).condition receiving := fun _ inside => inside

def nodes : NodeSet signature := boundary.absorbingNodes receiving receives
def successor : ForestChild signature := boundary.absorbingSuccessor receiving receives
def sourceTrace := boundary.absorbingPath receiving receives source source_in_small
def conditionedTrace := boundary.absorbingPath receiving receives firstConditioner conditioner_in_small

/-- Both actual mandatory source traces survive domain pruning unchanged. -/
theorem source_trace_codes : sourceTrace.nodes.map Fin.val = [2, 3] := by decide +kernel
theorem conditioned_trace_codes : conditionedTrace.nodes.map Fin.val = [3] := by decide +kernel

/-- The actual retained union contains exactly `U,P`, not every old flow
vertex or every original conditioner.  Boolean union counts their overlap once. -/
theorem actual_domain : NodeSet.members nodes = [source, firstConditioner] := by decide +kernel

theorem actual_successor : successor source = some firstConditioner ∧ successor firstConditioner = none := by decide +kernel

theorem complete_small_coverage : NodeSet.Subset (witness false).small nodes :=
  boundary.small_subset_absorbingNodes receiving receives

theorem actual_well_formed : childWellFormedBool nodes successor = true :=
  boundary.absorbingSuccessor_wellFormed receiving receives

theorem actual_sinks_inside : NodeSet.Subset (keptSinks nodes successor) receiving :=
  boundary.absorbingSinks_subset_interaction receiving receives

/-- The two source traces share their receiving vertex; the common map
therefore derives the same actual endpoint without disjointness premises. -/
theorem shared_contact_endpoint : sourceTrace.endpoint = conditionedTrace.endpoint :=
  sourceTrace.endpoint_eq_of_shared conditionedTrace firstConditioner
    (by decide +kernel) (by decide +kernel)

/-- An unvisited receiving row remains a genuine stop globally, but is
not needlessly added to the transmitting domain. -/
theorem irrelevant_receiver_stopped : nodes laterConditioner = false ∧ successor laterConditioner = none := by decide +kernel

/-! ## Stop at an earlier unconditioned interaction contact -/

def earlierReceiving : NodeSet signature := NodeSet.union receiving (NodeSet.singleton source)

private theorem earlier_receives : NodeSet.Subset (query false).condition earlierReceiving :=
  NodeSet.subset_union_left _ _

def earlierTrace := boundary.absorbingPath earlierReceiving earlier_receives source source_in_small

/-- The new first contact is already the source, although the unchanged
boundary path continues to conditioner `P`.  No edge is resumed at `U`. -/
theorem earlier_unconditioned_contact : earlierTrace.nodes = [source] ∧ earlierTrace.endpoint = source ∧
    (query false).condition earlierTrace.endpoint = false ∧
    boundary.absorbingSuccessor earlierReceiving earlier_receives source = none := by decide +kernel

/-! ## Apply the actual graph-normalized signal, not an alternative fixture -/

/-- Keep the actual no-exchange normal form opaque.  Only its proved
path/activation interfaces are used by conservation below. -/
def normal := approach.normalForm (no_exchange false)
def forest := approach.cutForest

def installedRows : NodeSet signature := normal.smallAbsorbedInteractionRows boundary approach.pivot forest
def installed : LinearSignal graph := normal.smallAbsorbedInteractionSignal boundary approach.pivot forest

/-- Every original mandatory row is present in the actual installed union,
including an unconditioned source not supplied as a normalized coverage flag. -/
theorem normalized_complete_small_coverage : NodeSet.Subset (witness false).small installedRows :=
  normal.smallAbsorbedInteraction_contains_small boundary approach.pivot forest

theorem normalized_action_free (child : Fin signature.count) (selected : installedRows child = true) :
    (query false).action child = false :=
  normal.smallAbsorbedInteraction_action_free boundary approach.pivot forest child selected

/-- Conservation holds on every original cube point, with no zero-tail
or supported-direction premise.  Reserved original pair inputs stay unchanged. -/
theorem whole_cube_conservation (point : Cube graph) :
    (installed.forestPhase installedRows).value point =
      ((normal.activationInteractionSignal approach.pivot forest).forestPhase
        (normal.smallInteractionRows approach.pivot forest)).value point :=
  normal.smallAbsorbedInteraction_phase boundary approach.pivot forest point

/-- On the full original evidence cylinder this is the exact actual
outcome character.  The Small/outside-Small direction partition is still open. -/
theorem original_cylinder_character (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union (query false).action (query false).condition))) :
    (installed.forestPhase installedRows).value point =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point :=
  normal.smallAbsorbedInteraction_conditionalPhase boundary approach.pivot forest point listed

/-- The actual mandatory Small/background partition has the complete
matching identity, not only the character of an unpartitioned row union.
Nothing here asserts the still-missing background evenness at a direction. -/
theorem full_small_background_matching (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union (query false).action (query false).condition))) :
    ((installed.forestPhase (witness false).small).xor
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome)))).value point =
      (selectedPhase _ signature.count (normal.smallAbsorbedInteractionBackgroundRows boundary approach.pivot forest)
        installed.rowPhase).value point :=
  normal.smallAbsorbedInteraction_matching boundary approach.pivot forest point listed

end CurrentConditionalFailureSmallAbsorption
end Examples
end Causality
end Thesis
