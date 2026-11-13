import Thesis.CausalTransport.GuardedIdentificationKernel
import Thesis.CausalTransport.HiddenDAGSoundness
import Thesis.CausalTransport.HiddenDAGFullFamily

namespace Thesis
namespace Causality
namespace Examples
namespace GuardedKernelZeroRegression

open Probability

/-!
# A complete recursive guarded ID run across a zero component prefix

The observed order is `X,M,Y,Z`.  A hidden unbiased root is shared by
`X,Y,Z`; `M` is a noisy mediator on `X -> M -> Y`.  The actual `Y` mechanism
is constantly false, while `Z` copies the hidden root.  Unused declared
parents are permitted: no faithfulness assumption is made by this framework.

The query `P(Y,Z | do(X))` exercises the real multi-component branch, a
containing-component restriction and subsequent uncut ancestral pruning.
Both engines identify structurally.  The strict engine leaves an undefined
`Z` quotient behind the zero `Y` factor, while the guarded engine skips it
and returns a supported zero at `Y = true`.

These are computations of the actual program and native probability record,
not a substitute for the generic support-carrying success compiler in
`GuardedKernelSuccessCompilation`: they do not instantiate its local data.
The general decision and action-free theorems are checked on this run too.
-/

def signature : ObservedSignature where
  count := 4
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨ (parent.val = 1 ∧ child.val = 2))
  directed_earlier := by decide +kernel

def x : Fin signature.count := ⟨0, by decide⟩
def mediator : Fin signature.count := ⟨1, by decide⟩
def y : Fin signature.count := ⟨2, by decide⟩
def z : Fin signature.count := ⟨3, by decide⟩

def fullGraph : FiniteHiddenDAG signature where
  count := 5
  observedNode := fun node => ⟨node.val + 1, by have bounded := node.isLt; change node.val < 4 at bounded; omega⟩
  observedNode_injective := by
    intro first second same
    apply Fin.ext
    have values := congrArg Fin.val same
    change first.val + 1 = second.val + 1 at values
    omega
  hidden := fun node => decide (node.val = 0)
  observed_not_hidden := by decide +kernel
  node_classified := by decide +kernel
  edge := fun parent child => decide
    ((parent.val = 0 ∧ (child.val = 1 ∨ child.val = 3 ∨ child.val = 4)) ∨
      (parent.val = 1 ∧ child.val = 2) ∨ (parent.val = 2 ∧ child.val = 3))
  rank := Fin.val
  edge_rank_lt := by decide +kernel

private theorem directed_search_matches : forall first second : Fin signature.count,
    signature.directed first second =
      (fullGraph.hiddenInternalPath? (fullGraph.observedNode first) (fullGraph.observedNode second)).isSome := by
  decide +kernel

private theorem directed_matches : fullGraph.DirectedProjectionMatches := by
  intro first second
  change signature.directed first second = true ↔
    fullGraph.HiddenInternalPath (fullGraph.observedNode first) (fullGraph.observedNode second)
  rw [directed_search_matches first second]
  exact fullGraph.hiddenInternalPath?_iff _ _

def projection : FiniteLatentProjection signature := fullGraph.computedLatentProjection directed_matches

private def hiddenRoot : Fin fullGraph.count := ⟨0, by decide⟩
private def fullX : Fin fullGraph.count := ⟨1, by decide⟩

private def unbiased : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def model : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Bool
  nodeEnumeration := fun _ => [false, true]
  node_complete := by intro _ value; cases value <;> simp
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := fullGraph.observedIndex
  observedIndex_observed := fullGraph.observedIndex_observed
  observedIndex_sound := fullGraph.observedIndex_sound
  hidden_has_no_observed_index := fullGraph.observedIndex_hidden
  Noise := fun _ => Bool
  noiseEnumeration := fun _ => [false, true]
  noise_complete := by intro _ value; cases value <;> simp
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => unbiased
  prior := FiniteProduct.record 5 (fun _ => Bool) (fun _ => unbiased)
  product_law := FiniteProduct.record_rectangular_probVal 5 (fun _ => Bool) (fun _ => unbiased)
  mechanism := fun node parents seed =>
    if atRoot : node.val = 0 then seed
    else if atX : node.val = 1 then
      parents hiddenRoot (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, hiddenRoot, atX])
    else if atMediator : node.val = 2 then
      Bool.xor (parents fullX (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, fullX, atMediator])) seed
    else if atY : node.val = 3 then false
    else parents hiddenRoot (by
      have bounded : node.val < 5 := node.isLt
      have atZ : node.val = 4 := by omega
      simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, hiddenRoot, atZ])

def query : JointKernelQuery signature :=
  ⟨NodeSet.union (NodeSet.singleton y) (NodeSet.singleton z), NodeSet.singleton x, by
    unfold NodeSet.Disjoint
    decide +kernel⟩

def reference : signature.Assignment := fun _ => true

def guardedFormula : ProbabilityTerm signature :=
  match identifyGuardedJointKernel projection.observedGraph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

def strictFormula : ProbabilityTerm signature :=
  match identifyJointKernel projection.observedGraph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

/-- Checking the Boolean constructor tag avoids needing a classical equality
instance for a whole outcome containing functional node sets and terms. -/
theorem guarded_identified : identifyGuardedJointKernel projection.observedGraph query = .identified guardedFormula := by
  have found : (match identifyGuardedJointKernel projection.observedGraph query with
      | .identified _ => true | _ => false) = true := by decide +kernel
  cases result : identifyGuardedJointKernel projection.observedGraph query with
  | identified term => simp only [guardedFormula, result]
  | failed _failure => simp only [result, Bool.false_eq_true] at found
  | unfinished => simp only [result, Bool.false_eq_true] at found

theorem strict_identified : identifyJointKernel projection.observedGraph query = .identified strictFormula := by
  have found : (match identifyJointKernel projection.observedGraph query with
      | .identified _ => true | _ => false) = true := by decide +kernel
  cases result : identifyJointKernel projection.observedGraph query with
  | identified term => simp only [strictFormula, result]
  | failed _failure => simp only [result, Bool.false_eq_true] at found
  | unfinished => simp only [result, Bool.false_eq_true] at found

theorem guarded_actionFree : guardedFormula.ActionFree :=
  identifyGuardedJointKernel_identified_actionFree _ _ guarded_identified

theorem guarded_no_sentinel : identifyGuardedJointKernel projection.observedGraph query ≠ .unfinished :=
  identifyGuardedJointKernel_ne_unfinished _ _

theorem guarded_value_is_supported_zero :
    (model.termDenote guardedFormula reference).map (fun value => value.num) = some 0 := by
  decide +kernel

theorem strict_value_is_undefined : (model.termDenote strictFormula reference).isNone = true := by
  decide +kernel

theorem actual_effect_is_supported_zero :
    (model.termDenote query.sourceTerm reference).map (fun value => value.num) = some 0 := by
  decide +kernel

end GuardedKernelZeroRegression
end Examples
end Causality
end Thesis
