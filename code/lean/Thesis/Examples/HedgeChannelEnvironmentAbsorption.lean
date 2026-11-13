import Thesis.Examples.HedgeChannelEnvironmentAbsorptionGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelEnvironmentAbsorption

open Probability PathSpecification HedgeChannelInstallation
open HedgeChannelEnvironmentInstallation FiniteBooleanInteraction

/-!
# The complete countermodel after absorbing a merged mandatory forest

The graph companion certifies the actual conditioned collider and the forest
`S,T -> M -> C`, with `C` already an interaction row inside Small.  The base
interaction installs rows `C xor Y`, `Z xor C`, and `P`.  Absorption changes
the receiving row to `C xor Y xor M` and adds `S`, `T`, and `M xor S xor T`.
Consequently the complete installed union still has phase `Y xor Z xor P`.

The full mandatory Small phase includes `S,T,C,Z,P`; it is not replaced by
the old three-row interaction.  Its actual outside-Small partner is the one
merge row `M`, which occurs once.  The direction flips only original outcome
`Y`, leaving every added forest bit zero.  The generic theorem proves the
new row evenness, preserves the original direction, derives full-cylinder
matching and Small oddness, and supplies the original conditional query gap.

All alphabets remain three-valued.  The positive models and full observational
equality come from the existing proved covariance and original-label lift;
neither the model prior nor a conditional likelihood table is enumerated here.
This closes an actual merged Small-overlap instance.  It does not supply the
still-missing universal active-path interaction/absorbing-forest construction.
-/

def signalData : LinearSignal graph where
  parentMask := fun child parent => decide
    ((child = collider ∧ parent = outcomeNode) ∨ (child = evidence ∧ parent = collider))
  rootMask := fun _ _ => false

def installed : LinearSignal graph := signalData.absorbSuccessor interaction absorbingSuccessor

def direction : Cube graph :=
  basisAssignment (pairRootCount graph.binary + signature.count) (Fin.natAdd (pairRootCount graph.binary) outcomeNode)

/-- Exact equality on every point, not only on the chosen direction or a
favorable event cell.  The proof uses the general installed-flow theorem. -/
theorem complete_phase_preserved (point : Cube graph) :
    (installed.forestPhase (NodeSet.union interaction absorbingDomain)).value point =
      (signalData.forestPhase interaction).value point :=
  signalData.absorbSuccessor_forestPhase interaction absorbingDomain absorbingSuccessor
    absorbing_wellFormed absorbing_stops absorbing_sinks_inside point

private theorem outcome_member : cubeMask graph query.outcome ∈
    outcomeMasks (pairRootCount graph.binary + signature.count) (cubeMask graph query.outcome) := by
  apply (FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mpr
  intro coordinate omitted
  simpa only [Bool.not_eq_true'] using omitted

private theorem direction_member : direction ∈
    FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) := by
  apply (basisAssignment_member_iff _ _ _).mpr
  decide +kernel

private theorem outcome_odd : (maskPhase _ (cubeMask graph query.outcome)).value direction = true := by
  change (maskPhase _ _).value (basisAssignment _ _) = true
  rw [maskPhase_basis]
  decide +kernel

private theorem interaction_even : forall node, interaction node = true -> witness.small node = false ->
    (signalData.rowPhase node).value direction = false := by
  have contained : NodeSet.Subset interaction witness.small := by unfold NodeSet.Subset; decide +kernel
  intro node selected outside
  have inside := contained node selected
  rw [outside] at inside
  cases inside

private theorem tails_zero : forall node, absorbingDomain node = true -> interaction node = false ->
    cubeSample graph direction node = false := by
  have zero : forall node, absorbingDomain node = true -> interaction node = false ->
      basisAssignment signature.count outcomeNode node = false := by decide +kernel
  intro node selected outside
  change FiniteProduct.BooleanBlocks.rightBlock _ _ (basisAssignment _ (Fin.natAdd _ outcomeNode)) node = false
  rw [rightBlock_basis_right]
  exact zero node selected outside

/-- Tiny actual basis tests prove the base interaction identity on the
complete original cylinder.  This does not check an exponential likelihood
support, assume a numerical gap, or replace Small by these interaction rows. -/
private theorem interaction_matches : forall point, point ∈
    FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) ->
    (signalData.forestPhase interaction).value point = (maskPhase _ (cubeMask graph query.outcome)).value point := by
  apply (HomogeneousPhase.agree_on_falseCylinder_iff_basis _ _ _).mpr
  decide +kernel

/-- Actual generic installation and parity assembly.  The full Small set,
deduplicated merge background and receiving collider all come from the
certified union, rather than from new row-even or Small-odd readiness flags. -/
def parityWitness : ConditionalParityWitness witness installed installed :=
  .ofAbsorbedInteraction witness signalData interaction absorbingDomain absorbingSuccessor
    absorbing_wellFormed absorbing_stops absorbing_sinks_inside absorbing_contains_small absorbing_action_free
    (cubeMask graph query.outcome) outcome_member direction direction_member outcome_odd
    interaction_even tails_zero interaction_matches

/-- The two original Small sources merge at `M` and then at the original
collider row.  The installed receiving row still contains its own `C` bit;
XORing two complete rows instead would incorrectly cancel it. -/
theorem receiving_own_bit_not_duplicated :
    (installed.rowPhase collider).value
      (joinCube graph (fun _ => false) (basisAssignment signature.count collider)) = true ∧
    Bool.xor ((signalData.rowPhase collider).value
      (joinCube graph (fun _ => false) (basisAssignment signature.count collider)))
      (((LinearSignal.ofSuccessor (G := graph) absorbingSuccessor).rowPhase collider).value
        (joinCube graph (fun _ => false) (basisAssignment signature.count collider))) = false := by
  decide +kernel

theorem actual_selected_background : parityWitness.selected = NodeSet.singleton mergeNode :=
  actual_merge_and_small_overlap.2.2.2.2.2

/-- A fully positive pair on all original three-valued alphabets has equal
complete observational laws and differs on the unchanged query `Y | do(X),P,Z`.
The two changing evidence masses are retained by the covariance construction. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity witness rich installed installed parityWitness

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end CurrentHedgeChannelEnvironmentAbsorption
end Examples
end Causality
end Thesis
