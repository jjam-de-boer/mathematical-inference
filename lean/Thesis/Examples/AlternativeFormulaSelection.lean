import Thesis.CausalTransport.BackdoorAdjustment

namespace Thesis
namespace Causality
namespace Examples
namespace AlternativeFormulaSelection

open Probability

/-!
# A genuine support gain from selecting an alternative adjustment formula

All four observed variables are Boolean, ordered `C,Z,X,Y`.  The graph has
`C -> X`, `Z -> X`, `C -> Y`, `X -> Y`.  Thus `C` and `C,Z` both satisfy the
two adjustment do-rule witnesses.  With independent fair `C,Z`, set
`X = C xor Z` and `Y = X xor C`.  Every `C,Z` cell is positive, but two
`X = true,C,Z` cells are null.  Adjustment using both covariates is undefined;
adjustment using only `C` is defined and gives the actual effect one half.

The catalogue first tries the literal guarded-ID output, then the larger
adjustment formula, then the smaller one.  Successful fallback therefore
enlarges applicability rather than merely selecting between identical
certificates.  A second actual model has overlap in every needed action cell;
there both independent formulas apply and their general agreement theorem
is exercised.  Neither fixture assumes a globally positive outcome law.
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
    ((parent.val = 0 ∧ child.val = 2) ∨ (parent.val = 1 ∧ child.val = 2) ∨
      (parent.val = 0 ∧ child.val = 3) ∨ (parent.val = 2 ∧ child.val = 3))
  directed_earlier := by decide +kernel

def c : Fin signature.count := ⟨0, by decide⟩
def z : Fin signature.count := ⟨1, by decide⟩
def x : Fin signature.count := ⟨2, by decide⟩
def y : Fin signature.count := ⟨3, by decide⟩

def fullGraph : FiniteHiddenDAG signature where
  count := 4
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := by intro _; rfl
  node_classified := fun node => Or.inr ⟨node, rfl⟩
  edge := signature.directed
  rank := Fin.val
  edge_rank_lt := signature.directed_earlier

private theorem directed_search_matches : forall first second : Fin signature.count,
    signature.directed first second =
      (fullGraph.hiddenInternalPath? first second).isSome := by
  decide +kernel

private theorem directed_matches : fullGraph.DirectedProjectionMatches := by
  intro first second
  change signature.directed first second = true ↔ fullGraph.HiddenInternalPath first second
  rw [directed_search_matches first second]
  exact fullGraph.hiddenInternalPath?_iff _ _

def projection : FiniteLatentProjection signature := fullGraph.computedLatentProjection directed_matches

def unbiased : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- Retain unused independent noises at `X,Y`, just as the existing native
fixtures do.  Every mechanism reads only its declared full-graph parents. -/
def model : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Bool
  nodeEnumeration := fun _ => [false, true]
  node_complete := by intro _ value; cases value <;> simp
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := fun node => some node
  observedIndex_observed := by intro _; rfl
  observedIndex_sound := by intro _ _ same; exact (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ impossible; cases impossible
  Noise := fun _ => Bool
  noiseEnumeration := fun _ => [false, true]
  noise_complete := by intro _ value; cases value <;> simp
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => unbiased
  prior := FiniteProduct.record 4 (fun _ => Bool) (fun _ => unbiased)
  product_law := FiniteProduct.record_rectangular_probVal 4 (fun _ => Bool) (fun _ => unbiased)
  mechanism := fun node parents seed =>
    if atX : node.val = 2 then
      Bool.xor (parents c (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, signature, c, atX]))
        (parents z (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, signature, z, atX]))
    else if atY : node.val = 3 then
      Bool.xor (parents x (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, signature, x, atY]))
        (parents c (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, signature, c, atY]))
    else seed

def query : JointKernelQuery signature :=
  ⟨NodeSet.singleton y, NodeSet.singleton x, NodeSet.disjoint_singletons_of_ne (by decide)⟩

def small : NodeSet signature := NodeSet.singleton c
def large : NodeSet signature := NodeSet.union (NodeSet.singleton c) (NodeSet.singleton z)
def reference : signature.Assignment := fun _ => true

/-- Actual executable d-separation checks certify the two do-rule leaves.
Their denotational interpretation is the general theorem, not a numerical
assertion about this particular fixture's causal mechanism. -/
def smallWitness : BackdoorAdjustmentWitness projection query small where
  action_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  removeAction := .rule3 NodeSet.empty small query.action NodeSet.empty
    (FourWayDisjoint.emptyAction _ _ _
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _))
    (by decide +kernel)
  exchangeAction := .rule2 NodeSet.empty query.outcome query.action small
    (FourWayDisjoint.emptyAction _ _ _
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_singletons_of_ne (by decide)))
    (by decide +kernel)

def largeWitness : BackdoorAdjustmentWitness projection query large where
  action_disjoint := NodeSet.disjoint_union_of
    (NodeSet.disjoint_singletons_of_ne (by decide)) (NodeSet.disjoint_singletons_of_ne (by decide))
  outcome_disjoint := NodeSet.disjoint_union_of
    (NodeSet.disjoint_singletons_of_ne (by decide)) (NodeSet.disjoint_singletons_of_ne (by decide))
  removeAction := .rule3 NodeSet.empty large query.action NodeSet.empty
    (FourWayDisjoint.emptyAction _ _ _
      (NodeSet.disjoint_union_left_of
        (NodeSet.disjoint_singletons_of_ne (by decide)) (NodeSet.disjoint_singletons_of_ne (by decide)))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _))
    (by decide +kernel)
  exchangeAction := .rule2 NodeSet.empty query.outcome query.action large
    (FourWayDisjoint.emptyAction _ _ _
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_union_of
        (NodeSet.disjoint_singletons_of_ne (by decide)) (NodeSet.disjoint_singletons_of_ne (by decide)))
      (NodeSet.disjoint_union_of
        (NodeSet.disjoint_singletons_of_ne (by decide)) (NodeSet.disjoint_singletons_of_ne (by decide))))
    (by decide +kernel)

noncomputable def smallCandidate := smallWitness.candidate
noncomputable def largeCandidate := largeWitness.candidate

def idFormula : ProbabilityTerm signature :=
  match identifyGuardedJointKernel projection.observedGraph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

theorem id_identified : identifyGuardedJointKernel projection.observedGraph query = .identified idFormula := by
  have found : (match identifyGuardedJointKernel projection.observedGraph query with
      | .identified _ => true | _ => false) = true := by decide +kernel
  cases result : identifyGuardedJointKernel projection.observedGraph query with
  | identified _term => simp only [idFormula, result]
  | failed _failure => simp only [result, Bool.false_eq_true] at found
  | unfinished => simp only [result, Bool.false_eq_true] at found

noncomputable def idCandidate : GuardedObservationalFormula projection query.sourceTerm :=
  .ofJoint (identifyGuardedJointKernel_admissibleCertificate query id_identified)

noncomputable def catalogue : List (GuardedObservationalFormula projection query.sourceTerm) :=
  [idCandidate, largeCandidate, smallCandidate]

theorem id_unavailable : idCandidate.available model.observationalDist reference = false := by
  decide +kernel

theorem large_unavailable : largeCandidate.available model.observationalDist reference = false := by
  decide +kernel

theorem small_available : smallCandidate.available model.observationalDist reference = true := by
  decide +kernel

/-- The actual engine succeeds structurally but its formula is unavailable;
selection reaches the independently certified smaller adjustment formula. -/
theorem selects_supported_alternative :
    GuardedObservationalFormula.select model.observationalDist reference catalogue = some smallCandidate := by
  simp only [catalogue, GuardedObservationalFormula.select, id_unavailable, large_unavailable,
    small_available, Bool.false_eq_true, if_false, if_true]

noncomputable def selected_native_sound : model.TermEquivalentAt query.sourceTerm smallCandidate.formula reference :=
  GuardedObservationalFormula.select_soundAt model reference catalogue smallCandidate selects_supported_alternative
    (model.kernelSupportedAt_unconditional query.outcome query.action reference)

def half : QProb := ⟨1, 2, by decide⟩

/-- The new formula and actual hard intervention both give the same exact
nonzero rational result.  This is not merely a supported-zero smoke test. -/
noncomputable def selected_value_half : ProbabilityResult.Equivalent
    (smallCandidate.formula.observationalDenote model.observationalDist reference) (some half) := by
  apply ProbabilityResult.Equivalent.value
  decide +kernel

noncomputable def actual_effect_half : ProbabilityResult.Equivalent
    (model.termDenote query.sourceTerm reference) (some half) :=
  ProbabilityResult.trans selected_native_sound (by
    rw [← ProbabilityTerm.observationalDenote_eq_native model smallCandidate.formula smallCandidate.actionFree reference]
    exact selected_value_half)

/-- Introduce full overlap for `X` while retaining the graph and the actual
deterministic outcome equation.  Outcome zeros remain allowed. -/
def overlapModel : FiniteHiddenDAGSCM signature projection := {
  model with
  mechanism := fun node parents seed =>
    if node.val = 2 then seed else model.mechanism node parents seed
}

theorem both_adjustments_available :
    largeCandidate.available overlapModel.observationalDist reference = true ∧
      smallCandidate.available overlapModel.observationalDist reference = true := by
  decide +kernel

/-- Agreement uses the universal candidate theorem, not equality of two
numbers calculated just for this fixture. -/
noncomputable def adjustments_agree_on_overlap : overlapModel.TermEquivalentAt
    largeCandidate.formula smallCandidate.formula reference :=
  largeCandidate.agreeAt smallCandidate overlapModel reference
    (overlapModel.kernelSupportedAt_unconditional query.outcome query.action reference)
    both_adjustments_available.1 both_adjustments_available.2

end AlternativeFormulaSelection
end Examples
end Causality
end Thesis
