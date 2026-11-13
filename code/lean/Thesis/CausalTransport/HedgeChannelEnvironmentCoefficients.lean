import Thesis.CausalTransport.HedgeChannelEnvironmentLinear
import Thesis.Probability.FiniteBooleanBasis

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open FiniteBooleanInteraction

/-!
# Actual local graph coefficients of the installed homogeneous phases

A whole-cylinder phase identity can be checked on free coordinate directions.
This module identifies those tests with local graph coefficients, retaining
the actual directed-edge and pair-root incidence guards of the installation.
An observed row contributes its own bit and each selected declared parent;
a reserved-root bit contributes only at selected genuine incident rows.

All coefficients are Boolean parities of explicit finite masks.  The small
forest keeps every original member row, and a background selection keeps
every selected row.  Neither is replaced by an endpoint or a formally chosen
linear representation.  The proofs collapse one coordinate's actual guarded
fold, rather than evaluating the full cube or a probability numerator.

These identities expose the conservation equations which a path construction
must prove.  They do not assert that every active path supplies balanced masks
or a supported odd direction.  In particular shared-latent coefficients are
still tied to their original pair roots, not a new globally incident source.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

namespace LinearSignal

/-- The coefficient of an observed coordinate in one actual row: its
own bit, XOR the selected declared-parent contribution.  An off-graph mask
entry cannot contribute, even before a routing proof is available. -/
def observedRowCoefficient (data : LinearSignal G) (child coordinate : Fin S.count) : Bool :=
  Bool.xor (decide (child = coordinate)) (S.directed coordinate child && data.parentMask child coordinate)

/-- The coefficient of one actual reserved root in one row.  Its incidence
guard prevents access to latent bits belonging only to other children. -/
def rootRowCoefficient (data : LinearSignal G) (child : Fin S.count) (coordinate : Fin (pairRootCount G.binary)) : Bool :=
  pairRootIncident G.binary coordinate child && data.rootMask child coordinate

/-- Observed-coordinate conservation over the complete supplied forest,
including every unqueried forest member and every selected incoming edge. -/
def forestObservedCoefficient (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin S.count) : Bool :=
  (NodeSet.members nodes).foldl (fun total child => Bool.xor total (observedRowCoefficient data child coordinate)) false

/-- Reserved-root conservation over the same full forest.  Two actual
incident reads cancel only when their finite mask parity proves cancellation. -/
def forestRootCoefficient (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin (pairRootCount G.binary)) : Bool :=
  (NodeSet.members nodes).foldl (fun total child => Bool.xor total (rootRowCoefficient data child coordinate)) false

/-- Observed-coordinate parity of the actual selected background rows.
Unselected rows contribute zero; the ascending fold matches the interaction
selection's terminal-coordinate recursion by the separate finite identity. -/
def selectedObservedCoefficient (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin S.count) : Bool :=
  (List.finRange S.count).foldl (fun total child => Bool.xor total
    (if nodes child then observedRowCoefficient data child coordinate else false)) false

/-- Actual reserved-root parity of the selected background rows.  The
root's original index and incidence are retained through the complete fold. -/
def selectedRootCoefficient (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin (pairRootCount G.binary)) : Bool :=
  (List.finRange S.count).foldl (fun total child => Bool.xor total
    (if nodes child then rootRowCoefficient data child coordinate else false)) false

private theorem guarded_fold_zero (count : Nat) (guard mask : Fin count -> Bool) :
    (List.finRange count).foldl (fun total index => Bool.xor total
      (if guard index = true then if mask index then false else false else false)) false = false := by
  apply foldl_unchanged
  intro total index
  simp only [ite_self, Bool.xor_false]

private theorem guarded_fold_basis (count : Nat) (coordinate : Fin count) (guard mask : Fin count -> Bool) :
    (List.finRange count).foldl (fun total index => Bool.xor total
      (if guard index = true then if mask index then basisAssignment count coordinate index else false else false)) false =
        (guard coordinate && mask coordinate) := by
  have same := foldl_congr
    (fun total index => Bool.xor total
      (if guard index = true then if mask index then basisAssignment count coordinate index else false else false))
    (fun total index => if index = coordinate then Bool.xor total (guard coordinate && mask coordinate) else total)
    false (List.finRange count) (by
      intro total index
      dsimp only
      by_cases atCoordinate : index = coordinate
      · subst index
        rw [basisAssignment_self, if_pos rfl]
        cases guard coordinate <;> cases mask coordinate <;> rfl
      · rw [basisAssignment_eq_false_of_ne count coordinate index atCoordinate]
        simp only [ite_self, Bool.xor_false, atCoordinate, if_false])
  exact same.trans (foldl_xor_bit_at count coordinate (guard coordinate && mask coordinate))

/-- The observed-basis test of the actual installed row is precisely its
own-coordinate/declared-parent coefficient.  All reserved inputs are zero
at this direction by the proved disjoint block reads, not by an assumed
independence or by removing latent roots from the model. -/
theorem rowPhase_observed_basis (data : LinearSignal G) (child coordinate : Fin S.count) :
    (rowPhase data child).value
        (basisAssignment (pairRootCount G.binary + S.count) (Fin.natAdd (pairRootCount G.binary) coordinate)) =
      observedRowCoefficient data child coordinate := by
  rw [rowPhase_value]
  unfold cubeSample cubeEnvironment
  rw [rightBlock_basis_right, leftBlock_basis_right, guarded_fold_basis, guarded_fold_zero, Bool.xor_false]
  rfl

/-- The reserved-root basis test of the actual installed row is its
genuine incident-root coefficient.  Every observed coordinate is zero at
this direction; a shared root can nevertheless contribute to each endpoint. -/
theorem rowPhase_root_basis (data : LinearSignal G) (child : Fin S.count) (coordinate : Fin (pairRootCount G.binary)) :
    (rowPhase data child).value
        (basisAssignment (pairRootCount G.binary + S.count) (coordinate.castAdd S.count)) =
      rootRowCoefficient data child coordinate := by
  rw [rowPhase_value]
  unfold cubeSample cubeEnvironment
  rw [rightBlock_basis_left, leftBlock_basis_left, guarded_fold_zero, guarded_fold_basis]
  simp only [Bool.false_xor]
  rfl

/-- Every observed coefficient of the complete actual forest phase is
the XOR of its actual member-row coefficients.  No small row is discarded. -/
theorem forestPhase_observed_basis (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin S.count) :
    (forestPhase data nodes).value
        (basisAssignment (pairRootCount G.binary + S.count) (Fin.natAdd (pairRootCount G.binary) coordinate)) =
      forestObservedCoefficient data nodes coordinate := by
  rw [forestPhase_value]
  unfold forestObservedCoefficient
  apply foldl_congr
  intro total child
  rw [rowPhase_observed_basis]

/-- Every reserved-root coefficient of the complete forest phase retains
all genuine incident contributions before their finite parity is taken. -/
theorem forestPhase_root_basis (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin (pairRootCount G.binary)) :
    (forestPhase data nodes).value
        (basisAssignment (pairRootCount G.binary + S.count) (coordinate.castAdd S.count)) =
      forestRootCoefficient data nodes coordinate := by
  rw [forestPhase_value]
  unfold forestRootCoefficient
  apply foldl_congr
  intro total child
  rw [rowPhase_root_basis]

/-- The selected interaction's observed-basis coefficient is the displayed
selected-row conservation fold.  The product expansion's row order has not
been changed or its unselected factors mistaken for selected ones. -/
theorem selectedPhase_observed_basis (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin S.count) :
    (selectedPhase (pairRootCount G.binary + S.count) S.count nodes (rowPhase data)).value
        (basisAssignment (pairRootCount G.binary + S.count) (Fin.natAdd (pairRootCount G.binary) coordinate)) =
      selectedObservedCoefficient data nodes coordinate := by
  rw [selectedPhase_value_eq_foldl]
  unfold selectedObservedCoefficient
  apply foldl_congr
  intro total child
  cases chosen : nodes child with
  | false => simp only [Bool.false_eq_true, if_false]
  | true => simp only [if_true, rowPhase_observed_basis]

/-- The selected interaction's actual reserved-root coefficient is the
complete selected-row incidence parity, with no extra root or global switch. -/
theorem selectedPhase_root_basis (data : LinearSignal G) (nodes : NodeSet S) (coordinate : Fin (pairRootCount G.binary)) :
    (selectedPhase (pairRootCount G.binary + S.count) S.count nodes (rowPhase data)).value
        (basisAssignment (pairRootCount G.binary + S.count) (coordinate.castAdd S.count)) =
      selectedRootCoefficient data nodes coordinate := by
  rw [selectedPhase_value_eq_foldl]
  unfold selectedRootCoefficient
  apply foldl_congr
  intro total child
  cases chosen : nodes child with
  | false => simp only [Bool.false_eq_true, if_false]
  | true => simp only [if_true, rowPhase_root_basis]

end LinearSignal

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
