import Thesis.CausalTransport.ActivePathInputSelection
import Thesis.CausalTransport.HedgeChannelEnvironmentCoefficients

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction

/-!
# Install the actual incoming inputs of an observed-endpoint active path

A path interaction cannot use an arbitrary shared switching coordinate.
Every observed input must be a declared parent, and every latent input must
be the original reserved root of its actual bidirected pair.  The finite
scans in `ActivePathInputSelection` construct those masks from the supplied
path, not from semantic readiness premises or a chosen witness of an
existence proposition.

An observed row is selected precisely when a path edge enters it.  In
particular an observed fork with two outgoing path arrows is not selected.
The parent mask retains exactly the path's incoming observed arrows.  The
root mask tests occurrence of either expanded label of an original pair;
the simple-path alias theorem ensures those are not two separate inputs.
Both real children of a used pair are adjacent to its latent occurrence,
so both have an incoming path edge and neither is incoming-cut.

Consequently every used original reserved input is read at exactly its two
selected child rows.  Its coefficient in the entire installed path phase
is zero.  This is a general conservation theorem about the actual guarded
signal, not a fixture-specific cancellation test or a supplied balance flag.
The whole installed phase is the character of the computed observed boundary.
Identifying that boundary with endpoint/collider terms, adding activation
rows, and integrating the complete Small forest remain graph obligations.
-/

variable {S : ObservedSignature.{0}}

namespace HedgeChannelEnvironmentInstallation
namespace LinearSignal

variable {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
  {source target : Fin S.count}

/-! ## Actual incoming masks and guarded row coefficients -/

/-- Install the actual path's incoming observed parents and original
reserved roots.  The signal interpreter still guards every local read by
its declared arrow or genuine incidence; these masks do not grant global
access to an auxiliary cube or another row's private inputs. -/
def ofActivePath (path : ActivePath graph m given (.observed source) (.observed target)) : LinearSignal graph where
  parentMask := fun child parent => ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child
  rootMask := fun child root => ActivePathInput.pairUsed graph path.nodes root &&
    pairRootIncident graph.binary root child && !(m.removeIncoming child)

/-- Every installed observed-parent entry is an actual kept path arrow.
The existence proof merely documents the finite scan's result. -/
theorem ofActivePath_parentMask_eq_true_iff
    (path : ActivePath graph m given (.observed source) (.observed target)) (child parent : Fin S.count) :
    (ofActivePath path).parentMask child parent = true ↔
      ActivePathInput.stepOnPath (.observed parent) (.observed child) path.nodes = true ∧
        graph.expandedMutilatedEdge m (.observed parent) (.observed child) = true :=
  Bool.and_eq_true_iff

/-- In particular no observed input is read without an original declared
parent arrow, even when the expanded graph contains additional latent edges. -/
theorem ofActivePath_parent_available
    (path : ActivePath graph m given (.observed source) (.observed target)) (child parent : Fin S.count)
    (selected : (ofActivePath path).parentMask child parent = true) : S.directed parent child = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    ((ofActivePath_parentMask_eq_true_iff path child parent).mp selected).2).1).1

/-- The actual observed-row coefficient retains its one own bit and
exactly the scanned incoming observed arrow.  Its declared-edge guard has
not enabled any off-path or unavailable parent contribution. -/
theorem ofActivePath_observedRowCoefficient
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child coordinate : Fin S.count) :
    (ofActivePath path).observedRowCoefficient child coordinate = Bool.xor (decide (child = coordinate))
      (ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child) := by
  unfold observedRowCoefficient
  cases selected : (ofActivePath path).parentMask child coordinate with
  | false =>
      change ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child = false at selected
      rw [selected, Bool.and_false]
  | true =>
      have declared := ofActivePath_parent_available path child coordinate selected
      change ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child = true at selected
      rw [declared, selected, Bool.true_and]

/-- Selection masks only the own-row contribution.  Every incoming path
parent already has its child among the selected heads, so its actual read
is retained without another selection prerequisite. -/
theorem ofActivePath_selected_observedRowCoefficient
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child coordinate : Fin S.count) :
    (if ActivePathInput.headRows graph m path.nodes child then
      (ofActivePath path).observedRowCoefficient child coordinate else false) =
        Bool.xor (ActivePathInput.headRows graph m path.nodes child && decide (child = coordinate))
          (ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child) := by
  cases head : ActivePathInput.headRows graph m path.nodes child with
  | true =>
      change (ofActivePath path).observedRowCoefficient child coordinate = _
      rw [ofActivePath_observedRowCoefficient, Bool.true_and]
  | false =>
      have absent : ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child = false := by
        cases selected : ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child with
        | false => rfl
        | true => exact False.elim (Bool.false_ne_true (head.symm.trans (ActivePathInput.incomingEdge_head selected)))
      rw [absent]
      rfl

/-- A selected reserved input is the actual incident original root and
its row is not incoming-cut.  The pair occurrence is executable finite data. -/
theorem ofActivePath_rootMask_eq_true_iff
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child : Fin S.count) (root : Fin (pairRootCount graph.binary)) :
    (ofActivePath path).rootMask child root = true ↔
      ActivePathInput.pairUsed graph path.nodes root = true ∧
        pairRootIncident graph.binary root child = true ∧ m.removeIncoming child = false := by
  change (_ && _ && _) = true ↔ _
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff, Bool.not_eq_true']
  exact and_assoc

/-- The incoming-cut guard of every used incident input is already proved
false by actual path adjacency.  Thus the installed root mask is exactly
the original-root occurrence test intersected with its genuine incidence. -/
theorem ofActivePath_rootMask
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child : Fin S.count) (root : Fin (pairRootCount graph.binary)) :
    (ofActivePath path).rootMask child root =
      (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph.binary root child) := by
  cases used : ActivePathInput.pairUsed graph path.nodes root with
  | false => simp only [ofActivePath, used, Bool.false_and]
  | true =>
      cases incident : pairRootIncident graph.binary root child with
      | false => simp only [ofActivePath, incident, Bool.and_false, Bool.false_and]
      | true =>
          have head := ActivePathInput.pairUsed_incident_head path root child used incident
          have kept := ActivePathInput.headRows_not_cut head
          simp only [ofActivePath, kept, used, incident, Bool.not_false, Bool.and_true]

/-- The actual interpreter's incidence guard is redundant for these
proved masks; unavailable inputs nevertheless remain guarded in the model. -/
theorem ofActivePath_rootRowCoefficient
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child : Fin S.count) (root : Fin (pairRootCount graph.binary)) :
    (ofActivePath path).rootRowCoefficient child root =
      (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph.binary root child) := by
  rw [rootRowCoefficient, ofActivePath_rootMask]
  cases ActivePathInput.pairUsed graph path.nodes root <;> cases pairRootIncident graph.binary root child <;> rfl

/-- Omitting unselected rows does not omit any genuine reserved-root
read: every such incident row was proved to be a path head above. -/
theorem ofActivePath_selected_rootRowCoefficient
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child : Fin S.count) (root : Fin (pairRootCount graph.binary)) :
    (if ActivePathInput.headRows graph m path.nodes child then (ofActivePath path).rootRowCoefficient child root else false) =
      (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph.binary root child) := by
  cases used : ActivePathInput.pairUsed graph path.nodes root with
  | false => rw [ofActivePath_rootRowCoefficient, used]; simp only [Bool.false_and, ite_self]
  | true =>
      cases incident : pairRootIncident graph.binary root child with
      | false => rw [ofActivePath_rootRowCoefficient, incident]; simp only [Bool.and_false, ite_self]
      | true =>
          have head := ActivePathInput.pairUsed_incident_head path root child used incident
          rw [head]
          change (ofActivePath path).rootRowCoefficient child root = _
          rw [ofActivePath_rootRowCoefficient, used, incident]

/-! ## Cancel every original reserved input at its two genuine child heads -/

private theorem pairRootIncident_eq_xor (root : Fin (pairRootCount graph.binary)) (child : Fin S.count) :
    pairRootIncident graph.binary root child = Bool.xor
      (decide (child = ((pairRoots graph.binary).get root).1))
      (decide (child = ((pairRoots graph.binary).get root).2)) := by
  have ordered := (pairRoots_get_spec graph.binary root).1
  have distinct : ((pairRoots graph.binary).get root).1 ≠ ((pairRoots graph.binary).get root).2 := by
    intro same
    rw [same] at ordered
    exact Nat.lt_irrefl _ ordered
  change (decide (child = ((pairRoots graph.binary).get root).1) ||
    decide (child = ((pairRoots graph.binary).get root).2)) = _
  by_cases atLeft : child = ((pairRoots graph.binary).get root).1
  · have notRight : child ≠ ((pairRoots graph.binary).get root).2 := fun same => distinct (atLeft.symm.trans same)
    rw [decide_eq_true atLeft, decide_eq_false notRight]
    rfl
  · by_cases atRight : child = ((pairRoots graph.binary).get root).2
    · rw [decide_eq_false atLeft, decide_eq_true atRight]
      rfl
    · rw [decide_eq_false atLeft, decide_eq_false atRight]
      rfl

private theorem xor_finRange_indicator {count : Nat} (child : Fin count) :
    (List.finRange count).foldl (fun total node => Bool.xor total (decide (node = child))) false = true := by
  have same : (fun node => decide (node = child)) = basisAssignment count child := by
    funext node
    by_cases atChild : node = child
    · subst node
      rw [basisAssignment_self]
      exact decide_eq_true rfl
    · rw [basisAssignment_eq_false_of_ne count child node atChild]
      exact decide_eq_false atChild
  calc
    _ = (List.finRange count).foldl (fun total node => Bool.xor total (basisAssignment count child node)) false := by
      apply foldl_congr
      intro total node
      rw [congrFun same node]
    _ = true := basisAssignment_masked_foldl count child (fun _ => true)

/-- Every actual reserved-root coefficient of the complete installed head
phase is zero.  A used root is read at its two distinct original children,
each selected once; an unused root is read nowhere.  The calculation retains
the original finite input index and all actual head rows, without imposing
an independent-input assumption on the expanded aliases. -/
theorem ofActivePath_forestRootCoefficient
    (path : ActivePath graph m given (.observed source) (.observed target))
    (root : Fin (pairRootCount graph.binary)) :
    (ofActivePath path).forestRootCoefficient (ActivePathInput.headRows graph m path.nodes) root = false := by
  have actualFold :
      (ofActivePath path).forestRootCoefficient (ActivePathInput.headRows graph m path.nodes) root =
        (List.finRange S.count).foldl (fun total child => Bool.xor total
          (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph.binary root child)) false := by
    unfold forestRootCoefficient NodeSet.members
    rw [List.foldl_filter]
    apply foldl_congr
    intro total child
    have coefficient := ofActivePath_selected_rootRowCoefficient path child root
    cases selected : ActivePathInput.headRows graph m path.nodes child with
    | false =>
        rw [selected] at coefficient
        change false = _ at coefficient
        rw [← coefficient, Bool.xor_false]
        rfl
    | true =>
        rw [selected] at coefficient
        change (ofActivePath path).rootRowCoefficient child root = _ at coefficient
        rw [← coefficient]
        rfl
  rw [actualFold]
  cases used : ActivePathInput.pairUsed graph path.nodes root with
  | false =>
      simp only [Bool.false_and]
      apply foldl_unchanged
      intro total child
      exact Bool.xor_false total
  | true =>
      simp only [Bool.true_and]
      have split :
          (List.finRange S.count).foldl (fun total child => Bool.xor total (pairRootIncident graph.binary root child)) false =
            (List.finRange S.count).foldl (fun total child => Bool.xor total (Bool.xor
              (decide (child = ((pairRoots graph.binary).get root).1))
              (decide (child = ((pairRoots graph.binary).get root).2)))) false := by
        apply foldl_congr
        intro total child
        rw [pairRootIncident_eq_xor]
        rfl
      rw [split, foldl_xor_pointwise]
      have leftOdd : (List.finRange S.count).foldl (fun total (child : Fin S.binary.count) =>
          Bool.xor total (decide (child = ((pairRoots graph.binary).get root).1))) false = true :=
        xor_finRange_indicator ((pairRoots graph.binary).get root).1
      have rightOdd : (List.finRange S.count).foldl (fun total (child : Fin S.binary.count) =>
          Bool.xor total (decide (child = ((pairRoots graph.binary).get root).2))) false = true :=
        xor_finRange_indicator ((pairRoots graph.binary).get root).2
      rw [leftOdd, rightOdd]
      rfl

/-- The conservation theorem concerns the actual installed homogeneous
phase, not just formal masks: every original reserved-input basis direction
is even in the complete path-head interaction. -/
theorem ofActivePath_forestPhase_root_basis
    (path : ActivePath graph m given (.observed source) (.observed target))
    (root : Fin (pairRootCount graph.binary)) :
    ((ofActivePath path).forestPhase (ActivePathInput.headRows graph m path.nodes)).value
      (basisAssignment (pairRootCount graph.binary + S.count) (root.castAdd S.count)) = false := by
  rw [forestPhase_root_basis, ofActivePath_forestRootCoefficient]

/-! ## Derive the observed boundary and the complete installed phase -/

private theorem xor_masked_indicator {count : Nat} (coordinate : Fin count) (mask : Fin count -> Bool) :
    (List.finRange count).foldl (fun total child => Bool.xor total (mask child && decide (child = coordinate))) false =
      mask coordinate := by
  have same : forall child, (mask child && decide (child = coordinate)) =
      (if mask child then basisAssignment count coordinate child else false) := by
    intro child
    cases selected : mask child with
    | false => rfl
    | true =>
        change decide (child = coordinate) = basisAssignment count coordinate child
        by_cases atCoordinate : child = coordinate
        · subst child
          rw [basisAssignment_self]
          exact decide_eq_true rfl
        · rw [basisAssignment_eq_false_of_ne count coordinate child atCoordinate]
          exact decide_eq_false atCoordinate
  calc
    _ = (List.finRange count).foldl (fun total child => Bool.xor total
        (if mask child then basisAssignment count coordinate child else false)) false := by
      apply foldl_congr
      intro total child
      rw [same]
    _ = _ := basisAssignment_masked_foldl count coordinate mask

/-- The remaining observed-coordinate balance is now a literal finite
graph calculation: the coordinate's selected own row, XOR the parity of
its actual outgoing path arrows.  All original reserved inputs have already
cancelled by the separate theorem above.  Path-window and collider arguments
must still identify this observed expression with the required character. -/
theorem ofActivePath_forestObservedCoefficient
    (path : ActivePath graph m given (.observed source) (.observed target)) (coordinate : Fin S.count) :
    (ofActivePath path).forestObservedCoefficient (ActivePathInput.headRows graph m path.nodes) coordinate =
      Bool.xor (ActivePathInput.headRows graph m path.nodes coordinate)
        ((List.finRange S.count).foldl (fun total child => Bool.xor total
          (ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child)) false) := by
  have actualFold :
      (ofActivePath path).forestObservedCoefficient (ActivePathInput.headRows graph m path.nodes) coordinate =
        (List.finRange S.count).foldl (fun total child => Bool.xor total (Bool.xor
          (ActivePathInput.headRows graph m path.nodes child && decide (child = coordinate))
          (ActivePathInput.incomingEdge graph m path.nodes (.observed coordinate) child))) false := by
    unfold forestObservedCoefficient NodeSet.members
    rw [List.foldl_filter]
    apply foldl_congr
    intro total child
    have coefficient := ofActivePath_selected_observedRowCoefficient path child coordinate
    cases selected : ActivePathInput.headRows graph m path.nodes child with
    | false =>
        rw [selected] at coefficient
        change false = _ at coefficient
        rw [← coefficient, Bool.xor_false]
        rfl
    | true =>
        rw [selected] at coefficient
        change (ofActivePath path).observedRowCoefficient child coordinate = _ at coefficient
        rw [← coefficient]
        rfl
  rw [actualFold, foldl_xor_pointwise, xor_masked_indicator]

/-- Whole-point conservation for the actual installed path-head phase.
The character contains only the derived observed boundary; every original
reserved-root contribution cancels.  This holds on the complete cube, not
just a chosen direction or a conditioning cylinder.  To obtain the desired
conditional character, the remaining graph proof must still identify this
boundary and attach the real collider activation rows. -/
theorem ofActivePath_forestPhase
    (path : ActivePath graph m given (.observed source) (.observed target)) (point : Cube graph) :
    ((ofActivePath path).forestPhase (ActivePathInput.headRows graph m path.nodes)).value point =
      (maskPhase _ (cubeMask graph (ActivePathInput.observedBoundary graph m path.nodes))).value point := by
  apply HomogeneousPhase.value_eq_of_basis _ _ (fun _ => false) (sample := point)
  · intro coordinate _free
    by_cases earlier : coordinate.val < pairRootCount graph.binary
    · let root : Fin (pairRootCount graph.binary) := ⟨coordinate.val, earlier⟩
      have embedded : root.castAdd S.count = coordinate := Fin.ext rfl
      rw [← embedded, ofActivePath_forestPhase_root_basis, maskPhase_basis]
      change false = FiniteProduct.BooleanBlocks.leftBlock _ _ (cubeMask graph _) root
      rw [cubeMask, FiniteProduct.BooleanBlocks.leftBlock_join]
    · let child : Fin S.count := ⟨coordinate.val - pairRootCount graph.binary, by
        have bound := coordinate.isLt
        omega⟩
      have embedded : Fin.natAdd (pairRootCount graph.binary) child = coordinate := by
        apply Fin.ext
        dsimp only [child, Fin.natAdd]
        omega
      rw [← embedded, forestPhase_observed_basis, ofActivePath_forestObservedCoefficient, maskPhase_basis]
      change ActivePathInput.observedBoundary graph m path.nodes child =
        FiniteProduct.BooleanBlocks.rightBlock _ _ (cubeMask graph _) child
      rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
  · intro coordinate impossible
    cases impossible



end LinearSignal
end HedgeChannelEnvironmentInstallation

end Causality
end Thesis
