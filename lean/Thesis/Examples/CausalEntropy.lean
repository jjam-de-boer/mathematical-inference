import Thesis.CausalTransport.EntropyAssessment
import Thesis.Causality.HiddenPathSearch
import Thesis.Probability.Distros.CrossEntropy
import Thesis.Probability.ExactLogRational

namespace Thesis
namespace Causality
namespace Examples
namespace CausalEntropy

open Probability Probability.Distros FiniteProduct

/-!
# Causal entropy regressions

The evaluator already supplies observational and interventional assignment
records.  Entropy is the existing Shannon functional of those records.

These examples separate (i) identification of an entire law, which identifies
its entropy, from (ii) observational association, which does not identify
interventional entropy or causal direction.  They also show that summing
observed-parent conditional entropies is not the hidden-DAG chain rule.
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
  node_classified := fun node => Or.inr ⟨node, rfl⟩
  edge := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  rank := Fin.val
  edge_rank_lt := by decide +kernel

private theorem directed_search_matches : forall first second : Fin signature.count,
    signature.directed first second =
      (fullGraph.hiddenInternalPath? (fullGraph.observedNode first)
        (fullGraph.observedNode second)).isSome := by
  decide +kernel

private theorem directed_matches : fullGraph.DirectedProjectionMatches := by
  intro first second
  change signature.directed first second = true ↔
    fullGraph.HiddenInternalPath (fullGraph.observedNode first)
      (fullGraph.observedNode second)
  rw [directed_search_matches first second]
  exact fullGraph.hiddenInternalPath?_iff _ _

def projection : FiniteLatentProjection signature :=
  fullGraph.computedLatentProjection directed_matches

def pointFalse : FiniteProbRecord Bool where
  atoms := [(false, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

def fairBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def noiseFactor (node : Fin projection.hiddenDAG.count) : FiniteProbRecord Bool :=
  if node.val = 1 then fairBit else pointFalse

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
  Noise := fun _ => Bool
  noiseEnumeration := fun _ => [false, true]
  noise_complete := by intro _ value; cases value <;> simp
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => pointFalse
  prior := FiniteProduct.record 2 (fun _ => Bool) (fun _ => pointFalse)
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool)
    (fun _ => pointFalse)
  mechanism := fun _ _ _ => false

/-- Same factual law as `constantModel`, but `Y` copies an independent fair
bit once `X` is true.  The arrow is idle observationally and active under
`do(X = true)`. -/
def randomModel : FiniteHiddenDAGSCM signature projection := {
  constantModel with
  factor := noiseFactor
  prior := FiniteProduct.record 2 (fun _ => Bool) noiseFactor
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool) noiseFactor
  mechanism := fun node parents seed =>
    if atY : node.val = 1 then
      (parents x (by
        simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, x, atY])) &&
        seed
    else false
}

def copyFactors (node : Fin projection.hiddenDAG.count) : FiniteProbRecord Bool :=
  if node.val = 0 then fairBit else pointFalse

/-- Structural copy `Y = X` with fair exogenous `X`. -/
def copyModel : FiniteHiddenDAGSCM signature projection := {
  constantModel with
  factor := copyFactors
  prior := FiniteProduct.record 2 (fun _ => Bool) copyFactors
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool) copyFactors
  mechanism := fun node parents seed =>
    if atY : node.val = 1 then
      parents x (by
        simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, x, atY])
    else seed
}

def copyParent : Fin projection.hiddenDAG.count := ⟨0, by decide⟩
def copyChild : Fin projection.hiddenDAG.count := ⟨1, by decide⟩

private theorem copy_edge : projection.hiddenDAG.edge copyParent copyChild = true := by
  decide +kernel

/-- Same-type Janzing cut: ignore `X` and substitute the default `false`.
The child's noise remains a point mass, so `Y` becomes constant. -/
def cutCopyModel : FiniteHiddenDAGSCM signature projection :=
  copyModel.cutIncoming copyParent copyChild copy_edge false

def independentFactors (_node : Fin projection.hiddenDAG.count) : FiniteProbRecord Bool :=
  fairBit

/-- Independent fair bits: the extra randomness the same-type cut cannot
create when the child's noise is degenerate. -/
def independentModel : FiniteHiddenDAGSCM signature projection := {
  constantModel with
  factor := independentFactors
  prior := FiniteProduct.record 2 (fun _ => Bool) independentFactors
  product_law := FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool) independentFactors
  mechanism := fun _node _parents seed => seed
}

def forceXTrue : HardIntervention signature :=
  (HardIntervention.empty signature).set x true

private def oneBit : ExactLog := ExactLog.ofSignedRatio ⟨1, 1, by decide⟩

private def falseAssignment : signature.Assignment := fun _ => false

private theorem constant_eval_false (noise : constantModel.NoiseAssignment) :
    constantModel.evalObserved (HardIntervention.empty signature) noise = falseAssignment := by
  funext node
  have either : node = x ∨ node = y := by
    have bounded := node.isLt
    change node.val < 2 at bounded
    if first : node.val = 0 then exact Or.inl (Fin.ext first)
    else exact Or.inr (Fin.ext (by change node.val = 1; omega))
  rcases either with first | second
  · subst node
    rw [FiniteHiddenDAGSCM.evalObserved, FiniteHiddenDAGSCM.evalNode]
    rfl
  · subst node
    rw [FiniteHiddenDAGSCM.evalObserved, FiniteHiddenDAGSCM.evalNode]
    rfl

private theorem random_eval_false (noise : randomModel.NoiseAssignment) :
    randomModel.evalObserved (HardIntervention.empty signature) noise = falseAssignment := by
  funext node
  have either : node = x ∨ node = y := by
    have bounded := node.isLt
    change node.val < 2 at bounded
    if first : node.val = 0 then exact Or.inl (Fin.ext first)
    else exact Or.inr (Fin.ext (by change node.val = 1; omega))
  rcases either with first | second
  · subst node
    rw [FiniteHiddenDAGSCM.evalObserved, FiniteHiddenDAGSCM.evalNode]
    rfl
  · subst node
    have xFalse :
        randomModel.evalNode (HardIntervention.empty signature) noise x = false := by
      rw [FiniteHiddenDAGSCM.evalNode]
      rfl
    rw [FiniteHiddenDAGSCM.evalObserved, FiniteHiddenDAGSCM.evalNode]
    simp [FiniteHiddenDAGSCM.interventionValueAt, HardIntervention.empty,
      FiniteLatentSCM.noIntervention, randomModel, constantModel, falseAssignment]
    change (decide ((projection.hiddenDAG.observedNode y).val = 1) &&
        (randomModel.evalNode (HardIntervention.empty signature) noise x &&
          noise (projection.hiddenDAG.observedNode y))) = false
    rw [xFalse]
    simp

private theorem constant_event (event : signature.Assignment → Bool) :
    QProb.Equiv (constantModel.observationalValue event)
      (if event falseAssignment then QProb.one else QProb.zero) := by
  have pushed := FiniteProbRecord.map_probVal constantModel.prior
    (constantModel.evalObserved (HardIntervention.empty signature)) event
  have rewritten := constantModel.prior.probVal_congr _ _
    (fun noise => congrArg event (constant_eval_false noise))
  have reduced := QProb.equiv_trans pushed rewritten
  cases hEvent : event falseAssignment
  · exact QProb.equiv_trans reduced (by simpa [hEvent] using constantModel.prior.probVal_false)
  · have top : (fun _ : constantModel.NoiseAssignment => event falseAssignment) = topEvent := by
      funext; simp [hEvent, topEvent]
    exact QProb.equiv_trans reduced (by simpa [hEvent, top] using constantModel.prior.normalization)

private theorem random_event (event : signature.Assignment → Bool) :
    QProb.Equiv (randomModel.observationalValue event)
      (if event falseAssignment then QProb.one else QProb.zero) := by
  have pushed := FiniteProbRecord.map_probVal randomModel.prior
    (randomModel.evalObserved (HardIntervention.empty signature)) event
  have rewritten := randomModel.prior.probVal_congr _ _
    (fun noise => congrArg event (random_eval_false noise))
  have reduced := QProb.equiv_trans pushed rewritten
  cases hEvent : event falseAssignment
  · exact QProb.equiv_trans reduced (by simpa [hEvent] using randomModel.prior.probVal_false)
  · have top : (fun _ : randomModel.NoiseAssignment => event falseAssignment) = topEvent := by
      funext; simp [hEvent, topEvent]
    exact QProb.equiv_trans reduced (by simpa [hEvent, top] using randomModel.prior.normalization)

theorem observational_laws_agree :
    ∀ event, QProb.Equiv (constantModel.observationalValue event)
      (randomModel.observationalValue event) := fun event =>
  QProb.equiv_trans (constant_event event) (QProb.equiv_symm (random_event event))

/-- Observational entropy is identified by the observational law, including
when the mechanisms differ. -/
theorem observational_entropy_agrees :
    ExactLog.Equiv constantModel.observationalEntropy randomModel.observationalEntropy :=
  FiniteHiddenDAGSCM.observationalEntropy_of_agreement observational_laws_agree

theorem observational_entropy_zero :
    ExactLog.Equiv constantModel.observationalEntropy ExactLog.zero := by
  decide +kernel

/-- Interventional entropy is not a function of the observational law. -/
theorem interventional_entropy_separates :
    ExactLog.Equiv (constantModel.interventionalEntropy forceXTrue) ExactLog.zero ∧
      ExactLog.Equiv (randomModel.interventionalEntropy forceXTrue) oneBit := by
  decide +kernel

theorem entropy_does_not_identify_direction :
    ExactLog.Equiv constantModel.observationalEntropy randomModel.observationalEntropy ∧
      ¬ ExactLog.Equiv (constantModel.interventionalEntropy forceXTrue)
        (randomModel.interventionalEntropy forceXTrue) :=
  ⟨observational_entropy_agrees, by
    intro same
    have separated := interventional_entropy_separates
    have collapsed := ExactLog.equiv_trans (ExactLog.equiv_symm separated.1)
      (ExactLog.equiv_trans same separated.2)
    exact (by decide : ¬ ExactLog.Equiv ExactLog.zero oneBit) collapsed⟩

/-! ## Observed-parent factorization fails after dependence is created -/

private def pairGrid : EntropyGrid (Bool × Bool) :=
  ⟨[(false, false), (false, true), (true, false), (true, true)], by decide⟩

/-- Perfectly correlated bits: the observational law of a hidden common
cause `U → X, U → Y` with `X = Y = U` fair.  Observed parents of both
coordinates are empty, so an observed-parent chain rule would predict
`H(X)+H(Y) = 2`, but `H(X,Y) = 1`. -/
private def correlated : Distro (Bool × Bool) :=
  ⟨⟨[((false, false), 1), ((true, true), 1)], 2, by decide, by decide⟩⟩

private def fairPair : Distro (Bool × Bool) :=
  ⟨⟨[((false, false), 1), ((false, true), 1), ((true, false), 1), ((true, true), 1)],
    4, by decide, by decide⟩⟩

private theorem correlatedSupport :
    correlated.AlmostSurely (fun value => value ∈ pairGrid.cells) := by
  change ∀ atom ∈ correlated.record.atoms, 0 < atom.2 → atom.1 ∈ pairGrid.cells
  decide +kernel

private theorem fairSupport :
    fairPair.AlmostSurely (fun value => value ∈ pairGrid.cells) := by
  change ∀ atom ∈ fairPair.record.atoms, 0 < atom.2 → atom.1 ∈ pairGrid.cells
  decide +kernel

private theorem fairPositive : fairPair.GridPositive pairGrid := by
  change ∀ value ∈ pairGrid.cells, 0 < (fairPair.pmf value).num
  decide +kernel

theorem observed_parent_factorization_fails :
    ExactLog.Equiv (correlated.entropy pairGrid correlatedSupport) oneBit ∧
      ExactLog.Equiv (fairPair.entropy pairGrid fairSupport)
        (ExactLog.ofSignedRatio ⟨2, 1, by decide⟩) := by
  decide +kernel

/-- Janzing-style KL against the product of marginals, with an explicitly
positive independent reference.  This is computable from a known joint; it
is not an observational identification of causal strength in a hidden-variable
model. -/
theorem correlated_kl_against_independent :
    ExactLog.Equiv
      (correlated.relativeEntropy fairPair pairGrid correlatedSupport fairSupport fairPositive)
      oneBit := by
  decide +kernel

/-- Shannon grouping monotonicity on an aligned two-stage fair choice. -/
private def fairVector : ProbabilityVector := ProbabilityVector.uniform 2 (by decide)

private def fairCompound : ProbabilityVector.Compound where
  branches := [(⟨1, 2, by decide⟩, fairVector), (⟨1, 2, by decide⟩, fairVector)]
  normalized := by decide +kernel

example : ExactLog.LE fairCompound.outer.entropy fairCompound.refined.entropy :=
  fairCompound.outer_entropy_le_refined

/-! ## Mechanism disruption versus extra noise -/

theorem copy_observational_entropy_one :
    ExactLog.Equiv copyModel.observationalEntropy oneBit := by
  decide +kernel

theorem cut_copy_observational_entropy_one :
    ExactLog.Equiv cutCopyModel.observationalEntropy oneBit := by
  decide +kernel

theorem independent_observational_entropy_two :
    ExactLog.Equiv independentModel.observationalEntropy
      (ExactLog.ofSignedRatio ⟨2, 1, by decide⟩) := by
  decide +kernel

/-- Same-type randomized intervention: `Y` emits its own noise, which is a
point mass, so the law is not independent fair bits. -/
def randomizeCopyChild : FiniteHiddenDAGSCM signature projection :=
  copyModel.randomizeWith copyChild id

theorem randomize_copy_observational_entropy_one :
    ExactLog.Equiv randomizeCopyChild.observationalEntropy oneBit := by
  decide +kernel

/-- Ignoring the parent at the original noise type does not produce the
independent fair law.  The Janzing stochastic cut needs extra randomness. -/
theorem cutIncoming_not_independent_fair :
    ¬ ExactLog.Equiv cutCopyModel.observationalEntropy independentModel.observationalEntropy := by
  intro same
  have collapsed := ExactLog.equiv_trans (ExactLog.equiv_symm cut_copy_observational_entropy_one)
    (ExactLog.equiv_trans same independent_observational_entropy_two)
  exact (by decide : ¬ ExactLog.Equiv oneBit (ExactLog.ofSignedRatio ⟨2, 1, by decide⟩)) collapsed

theorem randomizeWith_not_independent_fair :
    ¬ ExactLog.Equiv randomizeCopyChild.observationalEntropy
      independentModel.observationalEntropy := by
  intro same
  have collapsed := ExactLog.equiv_trans
    (ExactLog.equiv_symm randomize_copy_observational_entropy_one)
    (ExactLog.equiv_trans same independent_observational_entropy_two)
  exact (by decide : ¬ ExactLog.Equiv oneBit (ExactLog.ofSignedRatio ⟨2, 1, by decide⟩)) collapsed

/-- Full-DAG chain rule on the copy: `H(X,Y) = H(X) + H(Y|X)` with `H(Y|X)=0`. -/
theorem copy_selected_chain :
    ExactLog.Equiv (selectedEntropy copyModel.observationalLaw NodeSet.full) oneBit ∧
      ExactLog.Equiv (selectedEntropy copyModel.observationalLaw (NodeSet.singleton x)) oneBit := by
  decide +kernel

private theorem copy_x_subset_full :
    NodeSet.Subset (NodeSet.singleton x) NodeSet.full :=
  fun _ _ => rfl

theorem copy_selected_chain_rule :
    ExactLog.Equiv (selectedEntropy copyModel.observationalLaw NodeSet.full)
      (ExactLog.add
        (selectedEntropy copyModel.observationalLaw (NodeSet.singleton x))
        (selectedConditionalEntropy copyModel.observationalLaw
          (NodeSet.singleton x) NodeSet.full)) :=
  selectedEntropy_chain _ copy_x_subset_full

/-- Structural copy has `H(Y|X) = 0` as a grouping remainder, not as an
observed-parent sum. -/
theorem copy_conditional_given_x_zero :
    ExactLog.Equiv
      (selectedConditionalEntropy copyModel.observationalLaw
        (NodeSet.singleton x) NodeSet.full)
      ExactLog.zero :=
  ExactLog.equiv_trans
    (selectedConditionalEntropy_eq_sub copyModel.observationalLaw copy_x_subset_full)
    ((ExactLog.sub_equiv_zero_iff _ _).mpr
      (ExactLog.equiv_trans copy_selected_chain.1
        (ExactLog.equiv_symm copy_selected_chain.2)))

/-- Copy has `I(X;Y) = 1`: the bits are identical, not independent. -/
theorem copy_mutual_information_one :
    ExactLog.Equiv
      (selectedMutualInformation copyModel.observationalLaw
        (NodeSet.singleton x) (NodeSet.singleton y))
      oneBit := by
  decide +kernel

/-! ## Graph suitability given data -/

def independenceHypothesis : QueryGraphCandidate signature where
  independencies := [(NodeSet.singleton x, NodeSet.singleton y, NodeSet.empty)]
  identifiesQuery := true

def chainHypothesis : QueryGraphCandidate signature where
  independencies := []
  identifiesQuery := true

def bowHypothesis : QueryGraphCandidate signature where
  independencies := []
  identifiesQuery := false

def graphCatalogue : List (QueryGraphCandidate signature) :=
  [independenceHypothesis, chainHypothesis, bowHypothesis]

theorem independence_rejected_by_copy :
    independenceHypothesis.compatible copyModel.observationalLaw = false := by
  decide +kernel

theorem chain_and_bow_survive_copy :
    chainHypothesis.compatible copyModel.observationalLaw = true ∧
      bowHypothesis.compatible copyModel.observationalLaw = true := by
  decide +kernel

theorem copy_graph_uncertainty_one_bit :
    ∃ value, graphUncertaintyEntropy graphCatalogue copyModel.observationalLaw = some value ∧
      ExactLog.Equiv value oneBit := by
  have remaining :
      (graphCatalogue.filter (fun candidate => candidate.compatible copyModel.observationalLaw)).length = 2 := by
    decide +kernel
  unfold graphUncertaintyEntropy
  rw [remaining]
  exact finiteCatalogueEntropy_pair

theorem copy_query_suitability_zero :
    ∃ value, querySuitabilityEntropy graphCatalogue copyModel.observationalLaw = some value ∧
      ExactLog.Equiv value ExactLog.zero := by
  have remaining :
      (graphCatalogue.filter (fun candidate => candidate.suited copyModel.observationalLaw)).length = 1 := by
    decide +kernel
  unfold querySuitabilityEntropy
  rw [remaining]
  exact finiteCatalogueEntropy_singleton

theorem copy_shannon_submodularity :
    (⟨NodeSet.singleton x, NodeSet.singleton y⟩ : ShannonSubmodularityClaim signature).holds
      copyModel.observationalLaw := by
  decide +kernel

theorem copy_elemental_cone :
    ShannonCone.holdsOnDistro signature (elementalRows signature.count)
      copyModel.observationalLaw := by
  decide +kernel

end CausalEntropy
end Examples
end Causality
end Thesis
