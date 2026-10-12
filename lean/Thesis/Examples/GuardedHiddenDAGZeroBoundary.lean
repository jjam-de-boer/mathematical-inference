import Thesis.CausalTransport.GuardedHiddenDAGBoundary
import Thesis.CausalTransport.HiddenDAGFullFamily
import Thesis.Causality.ProbabilityTermEquality

namespace Thesis
namespace Causality
namespace Examples
namespace GuardedZeroClassBoundary

open Probability

/-!
# Guarded success does not imply unrestricted zero-class identification

The full graph is the two observed nodes `X -> Y`, with no hidden nodes.
Both models set `X = false`.  The first also sets `Y = false`; the second
copies `X` into `Y`.  Their entire observational records agree, but at
`do(X = true)` the first gives `Y = false` and the second gives `Y = true`.
All alphabets, priors, mechanisms and graph projection are explicit finite
records.  Unused declared parents are allowed; no faithfulness is assumed.

Guarded ID succeeds structurally, just as positive ID does, but its quotient
at the unobserved action value is undefined.  The actual native pair refutes
identifiability in `HiddenDAGModelClass.all`, even though the graph has no
confounding.  This is a counterexample to an unrestricted zero-class success
equivalence, not a failure of the support-qualified soundness theorem.

Finally the verified native soundness theorem proves that the compiler's
local data cannot exist at that unsupported action cell.  This checks that
the explicit boundary rejects the invalid use instead of manufacturing a
conditional value.  It does not deny valid reductions at null observed
actions in other graphs, such as the existing rule-3 regression.
-/

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by decide +kernel

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

def fullGraph : FiniteHiddenDAG signature where
  count := 2
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := by intro _; rfl
  node_classified := by decide +kernel
  edge := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
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

private def unitPrior : FiniteProbRecord Unit where
  atoms := [((), 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

/-- Unit private noises are an allowed finite presentation; there is no
implicit positive observed law or unspecified latent distribution. -/
def constantModel : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Bool
  nodeEnumeration := fun _ => [false, true]
  node_complete := by intro _ value; cases value <;> simp
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := fun node => some node
  observedIndex_observed := by intro _; rfl
  observedIndex_sound := by intro _ _ same; exact (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ impossible; cases impossible
  Noise := fun _ => Unit
  noiseEnumeration := fun _ => [()]
  noise_complete := by intro _ value; cases value; simp
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => unitPrior
  prior := FiniteProduct.record 2 (fun _ => Unit) (fun _ => unitPrior)
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Unit) (fun _ => unitPrior)
  mechanism := fun _ _ _ => false

/-- The only changed mechanism reads the declared `X -> Y` parent.  Its
factual output is still false because the unchanged `X` mechanism is false. -/
def copyingModel : FiniteHiddenDAGSCM signature projection := {
  constantModel with
  mechanism := fun node parents _seed =>
    if atY : node.val = 1 then
      parents x (by simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, x, atY])
    else false
}

def query : JointKernelQuery signature :=
  ⟨NodeSet.singleton y, NodeSet.singleton x, NodeSet.disjoint_singletons_of_ne (by decide)⟩

def reference : signature.Assignment := fun _ => true

def formula : ProbabilityTerm signature :=
  match identifyGuardedJointKernel projection.observedGraph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

theorem identified : identifyGuardedJointKernel projection.observedGraph query = .identified formula := by
  have found : (match identifyGuardedJointKernel projection.observedGraph query with
      | .identified _ => true | _ => false) = true := by decide +kernel
  cases result : identifyGuardedJointKernel projection.observedGraph query with
  | identified _term => simp only [formula, result]
  | failed _failure => simp only [result, Bool.false_eq_true] at found
  | unfinished => simp only [result, Bool.false_eq_true] at found

/-- Equality is of the complete observational records, not merely one
event or one coordinate marginal.  The two deterministic factual assignments
are equal for every unit before their common finite prior is pushed forward. -/
theorem observational_records_equal : constantModel.observationalDist = copyingModel.observationalDist := by
  change constantModel.prior.map (constantModel.evalObserved (HardIntervention.empty signature)) =
    constantModel.prior.map (copyingModel.evalObserved (HardIntervention.empty signature))
  apply congrArg (FiniteProbRecord.map constantModel.prior)
  funext unit node
  have either : node = x ∨ node = y := by
    have bounded : node.val < 2 := node.isLt
    if first : node.val = 0 then
      exact Or.inl (Fin.ext first)
    else
      exact Or.inr (Fin.ext (by omega))
  rcases either with first | second
  · subst node; rfl
  · subst node; rfl

theorem observational_agreement : constantModel.ObservationalAgreement copyingModel := by
  intro event
  change QProb.Equiv (constantModel.observationalDist.probVal event) (copyingModel.observationalDist.probVal event)
  rw [observational_records_equal]
  exact QProb.equiv_refl _

/-- Read the exact numerator/denominator pair after a finite result test.
This helper retains the value's positive-denominator proof by irrelevance;
it never selects a witness from an existential proposition. -/
private theorem result_eq_of_num_den (result : ProbabilityResult.Result) (value : QProb)
    (checked : result.map (fun actual => (actual.num, actual.den)) = some (value.num, value.den)) :
    result = some value := by
  cases result with
  | none => cases checked
  | some actual =>
      have fields := Option.some.inj checked
      cases actual with
      | mk actualNum actualDen actualPositive =>
          cases value with
          | mk expectedNum expectedDen expectedPositive =>
              have numerator := congrArg Prod.fst fields
              have denominator := congrArg Prod.snd fields
              dsimp at numerator denominator
              cases numerator
              cases denominator
              rfl

theorem constant_effect : constantModel.kernelDenote query.operationKernel reference = some QProb.zero :=
  result_eq_of_num_den _ _ (by decide +kernel)

theorem copying_effect : copyingModel.kernelDenote query.operationKernel reference = some QProb.one :=
  result_eq_of_num_den _ _ (by decide +kernel)

/-- The exhibited models disagree on genuinely supported intervention
values, zero and one, not merely on whether one side supplies a value. -/
theorem query_separated : ¬ constantModel.KernelResultEquivalent copyingModel query.operationKernel := by
  intro equivalent
  rcases equivalent reference with ⟨atReference⟩
  rw [constant_effect, copying_effect] at atReference
  cases atReference with
  | value rational => exact (by decide : ¬ QProb.Equiv QProb.zero QProb.one) rational

noncomputable def counterexample : HiddenDAGCounterexampleIn (HiddenDAGModelClass.all projection) query where
  left := constantModel
  right := copyingModel
  left_mem := trivial
  right_mem := trivial
  observationally_equal := observational_agreement
  query_separated := query_separated

/-- Structural success alone does not identify a query in the unrestricted
zero-permitting native class.  The class itself is not weakened or relabelled. -/
theorem not_identifiable_all : ¬ (HiddenDAGModelClass.all projection).identifiable query :=
  counterexample.not_identifiable

theorem observed_action_is_null :
    (constantModel.observationalDist.probVal (Kernel.agreesOn query.action reference)).num = 0 := by
  decide +kernel

theorem formula_is_undefined : (constantModel.termDenote formula reference).isNone = true := by
  decide +kernel

/-- The local-data boundary correctly excludes this invalid use.  If data
existed, the proved native soundness adapter would equate a supported zero
with the actual undefined program result, which is impossible. -/
theorem no_local_data : ¬ Nonempty
    ((identifyGuardedJointKernelLocalCompilation projection.observedGraph.dSeparationCorrectness query identified).aligned.Data
      constantModel.toLatentRootSCM reference) := by
  rintro ⟨data⟩
  let sound := identifyGuardedJointKernel_hiddenDAG_soundAt query identified constantModel reference data
  have missing : constantModel.termDenote formula reference = none := by
    have unsupported := formula_is_undefined
    cases result : constantModel.termDenote formula reference with
    | none => rfl
    | some _value => simp only [result, Option.isNone_some, Bool.false_eq_true] at unsupported
  change ProbabilityResult.Equivalent (constantModel.kernelDenote query.operationKernel reference)
    (constantModel.termDenote formula reference) at sound
  rw [constant_effect, missing] at sound
  cases sound

theorem constant_model_not_positive : ¬ constantModel.ObservationallyPositive := by
  intro positive
  have impossible := positive reference
  have zero : (constantModel.observationalDist.probVal (FiniteProbRecord.singletonEvent reference)).num = 0 := by
    decide +kernel
  rw [zero] at impossible
  exact Nat.not_lt_zero _ impossible

end GuardedZeroClassBoundary
end Examples
end Causality
end Thesis
