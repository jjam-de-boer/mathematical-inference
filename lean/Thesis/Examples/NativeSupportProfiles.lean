import Thesis.CausalTransport.NativeSupportProfiles
import Thesis.CausalTransport.ObservationalFormulaSupport
import Thesis.Examples.FiniteSupportCatalogue

namespace Thesis.Causality.Examples.NativeSupportProfiles

open Probability

/-!
# Native support-profile coverage with changed values and a null target

A declared three-valued observed variable reads its private three-code source.
The original actual law has probabilities one quarter, three quarters and
zero, with repeated source labels. Uniformizing its positive support changes
the first two probabilities to one half each, but retains the declared null
value as a legal hard-intervention target.

Direct kernel computations distinguish unsupported conditioning from a zero
outcome. Strict multiplication and marginalization retain missing branches;
weighted multiplication may skip its null factor only under a defined zero
left weight. A complete weighted-congruence support tree is transported too.
Finally the coverage theorems are exercised on both the fixed full graph and
the entire fixed-projection class, without evaluating their huge catalogues.
-/

def signature : ObservedSignature where
  count := 1
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => finRange_nodup 3
  defaultValue := fun _ => 0
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def node : Fin signature.count := ⟨0, by decide⟩
def reference (value : Fin 3) : signature.Assignment := fun _ => value

def fullGraph : FiniteHiddenDAG signature where
  count := 1
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := fun _ => rfl
  node_classified := fun current => Or.inr ⟨current, rfl⟩
  edge := fun _ _ => false
  rank := Fin.val
  edge_rank_lt := by intro _ _ impossible; cases impossible

def projection : FiniteLatentProjection signature where
  hiddenDAG := fullGraph
  directed_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · intro path
      cases path with
      | direct impossible => cases impossible
      | tail _ hidden _ => cases hidden
  bidirected := fun _ _ => false
  bidirected_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · rintro ⟨_, _, hidden, _, _⟩; cases hidden

def model : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Fin 3
  nodeEnumeration := fun _ => List.finRange 3
  node_complete := fun _ value => List.mem_finRange value
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := some
  observedIndex_observed := fun _ => rfl
  observedIndex_sound := fun _ _ same => (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ hidden; cases hidden
  Noise := fun _ => Fin 3
  noiseEnumeration := fun _ => List.finRange 3
  noise_complete := fun _ value => List.mem_finRange value
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => Probability.Examples.FiniteSupportCatalogue.original
  prior := FiniteProduct.record 1 (fun _ => Fin 3) (fun _ => Probability.Examples.FiniteSupportCatalogue.original)
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism := fun _ _ noise => noise

def entry : NativeTemplateInstance projection :=
  ⟨model.nativeTemplate (fun _ => 3) (fun _ => 3)
      (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩) (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩),
    model.nativeTemplateFactors (fun _ => 3) (fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩)⟩

theorem same_causal_support : CausalSupportAgreement entry.uniformSupport.model entry.model := entry.uniformSupport_agreement
theorem numerical_values_differ :
    ¬ QProb.Equiv (entry.uniformSupport.model.observationalValue (FiniteProbRecord.singletonEvent (reference 0)))
      (entry.model.observationalValue (FiniteProbRecord.singletonEvent (reference 0))) := by decide +kernel

def nullConditional : ProbabilityTerm signature := .kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.full⟩
def forcedConditional : ProbabilityTerm signature := .kernel ⟨NodeSet.full, NodeSet.full, NodeSet.full⟩
def strictZero : ProbabilityTerm signature := .multiply .zero nullConditional
def weightedZero : ProbabilityTerm signature := .weightedMultiply .zero nullConditional

theorem factual_null_undefined : ProbabilityResult.status (entry.model.termDenote nullConditional (reference 2)) = .undefined := by decide +kernel
theorem forced_null_positive : ProbabilityResult.status (entry.uniformSupport.model.termDenote forcedConditional (reference 2)) = .positive := by decide +kernel
theorem strict_zero_undefined : ProbabilityResult.status (entry.uniformSupport.model.termDenote strictZero (reference 2)) = .undefined := by decide +kernel
theorem weighted_zero_defined : ProbabilityResult.status (entry.uniformSupport.model.termDenote weightedZero (reference 2)) = .zero := by decide +kernel
theorem strict_marginal_undefined :
    ProbabilityResult.status (entry.uniformSupport.model.termDenote (.marginalize NodeSet.full nullConditional) (reference 0)) = .undefined := by decide +kernel

theorem every_term_status (term : ProbabilityTerm signature) (value : signature.Assignment) :
    ProbabilityResult.status (entry.uniformSupport.model.termDenote term value) = ProbabilityResult.status (entry.model.termDenote term value) :=
  same_causal_support.term_status term value

def weightedTrace : DoCalculusDerivation projection.observedGraph weightedZero weightedZero :=
  .weightedMultiplyCongr (.refl .zero) (.refl nullConditional)

def original_weighted_support : HiddenDAGLocalDerivationSupport entry.model (reference 2) weightedTrace := by
  let zeroSupport : entry.model.TermSupportedAt .zero (reference 2) := ⟨QProb.zero, .value (QProb.equiv_refl _)⟩
  let weightedSupport : entry.model.TermSupportedAt weightedZero (reference 2) := ⟨QProb.zero, .value (QProb.equiv_refl _)⟩
  refine ⟨weightedSupport, weightedSupport, ⟨zeroSupport, zeroSupport, ()⟩, ?_⟩
  intro positive
  have impossible : ProbabilityResult.Status.zero = ProbabilityResult.Status.positive := ProbabilityResult.positiveSupported_status positive
  cases impossible

noncomputable def transported_weighted_support : HiddenDAGLocalDerivationSupport entry.uniformSupport.model (reference 2) weightedTrace :=
  same_causal_support.symm.localSupportToRight weightedTrace (reference 2) original_weighted_support

/-- Both existing observable guard constructors remain numerically exact
after reweighting because their acceptance depends only on support. -/
theorem guards_unchanged (guard : ObservationalFormulaGuard signature) (value : signature.Assignment) :
    guard.check entry.uniformSupport.model.observationalDist value = guard.check entry.model.observationalDist value := by
  rw [← guard.checkSupport_exact, ← guard.checkSupport_exact, same_causal_support.observational_support]

theorem fixed_graph_coverage :
    ∃ candidate, candidate ∈ projection.completeSupportCatalogue ∧ CausalSupportAgreement candidate.model entry.model :=
  entry.model.completeSupportCatalogue_covers

def projected : ProjectedHiddenDAGModel projection.observedGraph := .ofModel entry.model (fun _ _ => rfl)

theorem all_hidden_graphs_coverage :
    ∃ candidate, candidate ∈ projection.observedGraph.cliqueRootProjection.completeSupportCatalogue ∧
      CausalSupportAgreement candidate.model projected.model := projected.completeSupportCatalogue_covers

end Thesis.Causality.Examples.NativeSupportProfiles
