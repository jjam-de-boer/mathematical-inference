import Thesis.CausalTransport.HiddenDAGFinitePresentation
import Thesis.CausalTransport.HiddenDAGSoundness
import Thesis.Probability.Distros.FinitePresentation
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.Distros.MultivariateHypergeometric

namespace Thesis.Causality.Examples.HiddenDAGFinitePresentation

open Probability Probability.Distros

/-!
# New finite distributions as genuine native causal noise

The graph has two independent Boolean observed nodes. `X` is always false;
`Y` reads a Boolean event of an arbitrary named finite distribution. Each
node retains its own independent finite private-noise coordinate, even though
`X` ignores its sample. Codes retain the original natural weights; neither
the denominator nor an infinite ambient label type is enumerated.

The symbolic probability theorem checks the actual native evaluator and
product prior, not just the distribution wrapper. Intervening on `X` leaves
every `Y` event unchanged. A separate instantiation of native do-rule
soundness checks the same graph reduction, including the observationally
null action `X = true`. The rational urn and finite-population applications
use their actual constructors and allow their ordinary zero-probability cells.
-/

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

/-- No hidden vertex or edge is smuggled into this independent-node fixture. -/
def fullGraph : FiniteHiddenDAG signature where
  count := 2
  observedNode := id
  observedNode_injective := fun _ _ same => same
  hidden := fun _ => false
  observed_not_hidden := fun _ => rfl
  node_classified := fun node => Or.inr ⟨node, rfl⟩
  edge := fun _ _ => false
  rank := Fin.val
  edge_rank_lt := by intro _ _ impossible; cases impossible

private theorem no_path {first second : Fin fullGraph.count}
    (path : fullGraph.HiddenInternalPath first second) : False := by
  cases path with
  | direct impossible => cases impossible
  | tail _ _ impossible => cases impossible

def projection : FiniteLatentProjection signature where
  hiddenDAG := fullGraph
  directed_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · intro path; exact False.elim (no_path path)
  bidirected := fun _ _ => false
  bidirected_matches := by
    intro first second
    constructor
    · intro impossible; cases impossible
    · rintro ⟨_, _, impossible, _, _⟩; cases impossible

/-- Every finite record, even on an infinite ambient label type, supplies
finite private noise with its unchanged weighted sampling law. -/
def model (distro : Distro Ω) (readout : Ω → Bool) : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Bool
  nodeEnumeration := fun _ => [false, true]
  node_complete := by intro _ value; cases value <;> simp
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := some
  observedIndex_observed := fun _ => rfl
  observedIndex_sound := fun _ _ same => (Option.some.inj same).symm
  hidden_has_no_observed_index := by intro _ impossible; cases impossible
  Noise := fun _ => Fin distro.finitePresentation.card
  noiseEnumeration := fun _ => List.finRange distro.finitePresentation.card
  noise_complete := fun _ value => List.mem_finRange value
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => distro.finitePresentation.record
  prior := FiniteProduct.record 2 (fun _ => Fin distro.finitePresentation.card)
    (fun _ => distro.finitePresentation.record)
  product_law := FiniteProduct.record_rectangular_probVal 2
    (fun _ => Fin distro.finitePresentation.card) (fun _ => distro.finitePresentation.record)
  mechanism := fun child _parents noise =>
    if child.val = 0 then false else readout (distro.finitePresentation.decode noise)

/-- Unforced `Y` reads its own decoded sample, under any intervention on
the other node. This follows from one structural equation, not a table test. -/
theorem eval_y (distro : Distro Ω) (readout : Ω → Bool)
    (intervention : HardIntervention signature) (unforced : intervention.value y = none)
    (noise : (model distro readout).NoiseAssignment) :
    (model distro readout).evalObserved intervention noise y =
      readout (distro.finitePresentation.decode (noise y)) := by
  change (model distro readout).evalNode intervention noise y = _
  rw [FiniteHiddenDAGSCM.evalNode]
  have absent : (model distro readout).interventionValueAt intervention y = none := by
    change (model distro readout).interventionValueAt intervention (projection.hiddenDAG.observedNode y) = none
    rw [FiniteHiddenDAGSCM.interventionValueAt_observed_eq_map, unforced]
    rfl
  rw [absent]
  rfl

/-- Every Boolean event of the native `Y` value has exactly the original
distribution's readout law. The proof uses the actual independent product
marginal and decoder recovery, without assuming strict positivity. -/
theorem interventional_y_event (distro : Distro Ω) (readout : Ω → Bool)
    (intervention : HardIntervention signature) (unforced : intervention.value y = none)
    (event : Event Bool) :
    QProb.Equiv
      ((model distro readout).interventionalValue intervention (fun values => event (values y)))
      (distro.record.probVal (fun value => event (readout value))) := by
  apply QProb.equiv_trans ((model distro readout).prior.map_probVal _ _)
  apply QProb.equiv_trans ((model distro readout).prior.probVal_congr _ _ (fun noise =>
    congrArg event (eval_y distro readout intervention unforced noise)))
  exact QProb.equiv_trans
    (FiniteProduct.record_coordinate_probVal_dependent 2
      (fun _ => Fin distro.finitePresentation.card) (fun _ => distro.finitePresentation.record) y
      (fun code => event (readout (distro.finitePresentation.decode code))))
    (distro.finitePresentation.probVal (fun value => event (readout value)))

/-- The same native marginal calculation includes the observational law. -/
theorem observational_y_event (distro : Distro Ω) (readout : Ω → Bool) (event : Event Bool) :
    QProb.Equiv ((model distro readout).observationalValue (fun values => event (values y)))
      (distro.record.probVal (fun value => event (readout value))) :=
  interventional_y_event distro readout (HardIntervention.empty signature) rfl event

/-- Factually `X` is false for every sample; its unused private-noise
coordinate is still present in the product model. -/
theorem eval_x_factual (distro : Distro Ω) (readout : Ω → Bool)
    (noise : (model distro readout).NoiseAssignment) :
    (model distro readout).evalObserved (HardIntervention.empty signature) noise x = false := by
  change (model distro readout).evalNode (HardIntervention.empty signature) noise x = false
  rw [FiniteHiddenDAGSCM.evalNode]
  have absent : (model distro readout).interventionValueAt (HardIntervention.empty signature) x = none := by
    change (model distro readout).interventionValueAt (HardIntervention.empty signature)
      (projection.hiddenDAG.observedNode x) = none
    rw [FiniteHiddenDAGSCM.interventionValueAt_observed_eq_map]
    rfl
  rw [absent]
  rfl

/-- The supported intervention `do(X = true)` is observationally null.
Thus the native integration test does not secretly require positive action
cells in the factual distribution. -/
theorem factual_action_null (distro : Distro Ω) (readout : Ω → Bool) :
    QProb.Equiv ((model distro readout).observationalValue (fun values => values x)) QProb.zero := by
  apply QProb.equiv_trans ((model distro readout).prior.map_probVal _ _)
  exact QProb.equiv_trans
    ((model distro readout).prior.probVal_congr _ _ (eval_x_factual distro readout))
    ((model distro readout).prior.probVal_false)

/-! ## Actual native do-calculus soundness, not an external interface -/

def rule3Application : DoRuleApplication projection.observedGraph
    (rule3Left NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty)
    (rule3Right NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty) :=
  .rule3 NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty
    (FourWayDisjoint.emptyAction _ _ NodeSet.empty
      (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _))
    (by decide +kernel)

/-- This applies the checked native soundness theorem to each constructed
model. Both unconditional endpoints have support even at null action values. -/
noncomputable def rule3_sound (distro : Distro Ω) (readout : Ω → Bool)
    (reference : signature.Assignment) :
    (model distro readout).TermEquivalentAt
      (.kernel (rule3Left NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty))
      (.kernel (rule3Right NodeSet.empty (NodeSet.singleton y) (NodeSet.singleton x) NodeSet.empty)) reference :=
  (model distro readout).doRule_soundAt reference rule3Application
    ((model distro readout).kernelSupportedAt_unconditional (NodeSet.singleton y)
      (NodeSet.union NodeSet.empty (NodeSet.singleton x)) reference)
    ((model distro readout).kernelSupportedAt_unconditional (NodeSet.singleton y) NodeSet.empty reference)

/-! ## Symbolic newer-distribution instances -/

/-- Arbitrary nonnegative rational urn parameters are native finite noise,
including zero-weight categories. No unit-weight expansion is used. -/
theorem rational_urn_do_x (trials : Nat) (parameters : List QProb)
    (positive : 0 < (QProb.listSum parameters).num) (readout : List Nat → Bool)
    (forced : Bool) (event : Event Bool) :
    let distro := rationalPolyaDistro trials parameters positive
    QProb.Equiv
      ((model distro readout).interventionalValue ((HardIntervention.empty signature).set x forced)
        (fun values => event (values y)))
      (distro.record.probVal (fun value => event (readout value))) :=
  interventional_y_event _ readout _
    (HardIntervention.set_away_from_target _ x y forced (by decide)) event

/-- Finite-population combinatorial weights pass through exactly the same
native model boundary; their list-valued ambient type need not be finite. -/
theorem hypergeometric_do_x (draws : Nat) (stocks : List Nat)
    (positive : 0 < Combinatorics.binom stocks.sum draws) (readout : List Nat → Bool)
    (forced : Bool) (event : Event Bool) :
    let distro := multivariateHypergeometricDistro draws stocks positive
    QProb.Equiv
      ((model distro readout).interventionalValue ((HardIntervention.empty signature).set x forced)
        (fun values => event (values y)))
      (distro.record.probVal (fun value => event (readout value))) :=
  interventional_y_event _ readout _
    (HardIntervention.set_away_from_target _ x y forced (by decide)) event

end Thesis.Causality.Examples.HiddenDAGFinitePresentation
