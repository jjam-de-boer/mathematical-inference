import Thesis.CausalTransport.LatentRootNativeModel

namespace Thesis.Causality.LatentRootNative

open Probability

/-!
# Unitwise and probabilistic preservation of the native root realization

An explicit candidate assignment copies each root's actual private block and
evaluates every observed node with the original structural model at decoded
noise. Show that assignment solves every intervened native equation, including
forced observed values. The existing acyclic evaluator uniqueness theorem
then gives exact observed evaluation at every noise unit and intervention.

The complete decoded independent-law theorem supplies the probability step.
No separate semantic transfer premise, observational positivity, chosen noise
default or restriction to positive trajectories is used. Supported original
conditionals transport by their actual numerator and denominator probabilities;
unsupported evidence is never assigned a conditional probability.
-/

universe u
variable {S : ObservedSignature.{u}} (original : ExactModel S)

def expectedValues (intervention : HardIntervention S) (noise : (model original).NoiseAssignment) : (model original).NodeAssignment :=
  Fin.addCases
    (fun root => (rootEquivalence original root).backward (noise (rootNode original root)))
    (fun observed => (observedEquivalence original observed).backward
      (original.evalNodeUnder intervention.value (decodeNoise original noise) observed))

theorem expectedValues_root (intervention : HardIntervention S) (noise : (model original).NoiseAssignment)
    (root : Fin original.latent.count) :
    expectedValues original intervention noise (rootNode original root) =
      (rootEquivalence original root).backward (noise (rootNode original root)) := by
  simp only [expectedValues, rootNode, LatentRootDAG.rootNode, Fin.addCases_left]

theorem expectedValues_observed (intervention : HardIntervention S) (noise : (model original).NoiseAssignment)
    (observed : Fin S.count) :
    expectedValues original intervention noise (observedNode original observed) =
      (observedEquivalence original observed).backward
        (original.evalNodeUnder intervention.value (decodeNoise original noise) observed) := by
  simp only [expectedValues, observedNode, LatentRootDAG.observedNode, Fin.addCases_right]

theorem interventionValueAt_root (intervention : HardIntervention S) (root : Fin original.latent.count) :
    (model original).interventionValueAt intervention (rootNode original root) = none :=
  (model original).interventionValueAt_eq_none intervention _
    (original.latent.rootProjection.hiddenDAG.observedIndex_hidden _
      (LatentRootDAG.graph_root_hidden S original.latent.count original.latent.incident root))

theorem interventionValueAt_observed (intervention : HardIntervention S) (observed : Fin S.count) :
    (model original).interventionValueAt intervention (observedNode original observed) =
      (intervention.value observed).map (observedEquivalence original observed).backward :=
  (model original).interventionValueAt_observed_eq_map intervention observed

theorem mechanism_root (root : Fin original.latent.count)
    (parents : original.latent.rootProjection.hiddenDAG.ParentValues (NodeValue original) (rootNode original root))
    (noise : Noise original (rootNode original root)) :
    (model original).mechanism (rootNode original root) parents noise = (rootEquivalence original root).backward noise := by
  change mechanism original (rootNode original root) parents noise = _
  simp only [mechanism, rootNode, LatentRootDAG.rootNode, Fin.addCases_left]

theorem mechanism_observed (observed : Fin S.count)
    (parents : original.latent.rootProjection.hiddenDAG.ParentValues (NodeValue original) (observedNode original observed))
    (noise : Noise original (observedNode original observed)) :
    (model original).mechanism (observedNode original observed) parents noise = observedMechanism original observed parents := by
  change mechanism original (observedNode original observed) parents noise = _
  simp only [mechanism, observedNode, LatentRootDAG.observedNode, Fin.addCases_right]

/-- Every permitted parent and latent input is the original model's input
at decoded noise. Readout conversions are inverted on the whole domain. -/
theorem observedMechanism_expected (intervention : HardIntervention S) (noise : (model original).NoiseAssignment)
    (child : Fin S.count) :
    observedMechanism original child (fun parent _ => expectedValues original intervention noise parent) =
      (observedEquivalence original child).backward
        (original.mechanism child
          (fun parent _ => original.evalNodeUnder intervention.value (decodeNoise original noise) parent)
          (fun root _ => decodeNoise original noise root)) := by
  unfold observedMechanism
  have parentsAgree :
      (fun parent (_ : S.directed parent child = true) => (observedEquivalence original parent).forward
        (expectedValues original intervention noise (observedNode original parent))) =
      (fun parent (_ : S.directed parent child = true) =>
        original.evalNodeUnder intervention.value (decodeNoise original noise) parent) := by
    funext parent edge
    rw [expectedValues_observed, (observedEquivalence original parent).forward_backward]
  have rootsAgree :
      (fun root (_ : original.latent.incident root child = true) => ((rootEquivalence original root).forward
        (expectedValues original intervention noise (rootNode original root))) root rfl) =
      (fun root (_ : original.latent.incident root child = true) => decodeNoise original noise root) := by
    funext root incident
    rw [expectedValues_root, (rootEquivalence original root).forward_backward]
    rfl
  rw [parentsAgree, rootsAgree]

theorem expectedValues_solution (intervention : HardIntervention S) (noise : (model original).NoiseAssignment)
    (node : Node original) :
    expectedValues original intervention noise node =
      match (model original).interventionValueAt intervention node with
      | some value => value
      | none => (model original).mechanism node (fun parent _ => expectedValues original intervention noise parent) (noise node) := by
  refine Fin.addCases (fun root => ?_) (fun observed => ?_) node
  · change expectedValues original intervention noise (rootNode original root) = _
    rw [expectedValues_root, interventionValueAt_root, mechanism_root]
  · change expectedValues original intervention noise (observedNode original observed) = _
    rw [expectedValues_observed, interventionValueAt_observed]
    cases forced : intervention.value observed with
    | some value =>
        simp only [Option.map_some]
        have oldForced := original.evalUnder_effectiveness intervention.value (decodeNoise original noise) observed value forced
        change original.evalNodeUnder intervention.value (decodeNoise original noise) observed = value at oldForced
        rw [oldForced]
    | none =>
        simp only [Option.map_none]
        rw [mechanism_observed, observedMechanism_expected]
        apply congrArg (observedEquivalence original observed).backward
        rw [FiniteLatentSCM.evalNodeUnder]
        simp only [FiniteLatentSCM.equationUnder, forced]

/-- Native evaluator uniqueness applies to the explicit solution above;
there is no extra global-Markov, graph-transfer or semantic-equality premise. -/
theorem evalNode (intervention : HardIntervention S) (noise : (model original).NoiseAssignment) (node : Node original) :
    (model original).evalNode intervention noise node = expectedValues original intervention noise node :=
  (model original).evalNode_eq_of_solution intervention noise (expectedValues original intervention noise)
    (expectedValues_solution original intervention noise) node

theorem evalObserved (intervention : HardIntervention S) (noise : (model original).NoiseAssignment) :
    (model original).evalObserved intervention noise = original.evalUnder intervention.value (decodeNoise original noise) := by
  funext observed
  change (observedEquivalence original observed).forward
    ((model original).evalNode intervention noise (observedNode original observed)) = _
  rw [evalNode, expectedValues_observed, (observedEquivalence original observed).forward_backward]
  rfl

theorem prior_probVal (event : Event original.latent.Assignment) :
    QProb.Equiv ((model original).prior.probVal (fun noise => event (decodeNoise original noise))) (original.prior.probVal event) :=
  FiniteProductGrouping.decoded_probVal (owner original) original.factor original.prior original.product_law
    original.latent.valueEnumeration original.latent.value_complete original.latent.valueDecidableEq event

theorem interventionalValue (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv ((model original).interventionalValue intervention event) (original.interventionalValue intervention.value event) := by
  have units := (model original).prior.probVal_congr _ _
    (fun noise => congrArg event (evalObserved original intervention noise))
  exact QProb.equiv_trans ((model original).prior.map_probVal ((model original).evalObserved intervention) event)
    (QProb.equiv_trans units (QProb.equiv_trans (prior_probVal original (fun roots => event (original.evalUnder intervention.value roots)))
      (QProb.equiv_symm (original.interventionalValue_eq intervention.value event))))

theorem observationalValue (event : Event S.Assignment) :
    QProb.Equiv ((model original).observationalValue event) (original.observationalValue event) :=
  interventionalValue original (HardIntervention.empty S) event

theorem eventPositive_iff (intervention : HardIntervention S) (evidence : Event S.Assignment) :
    ((model original).interventionalDist intervention).EventPositive evidence ↔
      (original.interventionalDist intervention.value).EventPositive evidence :=
  QProb.equiv_num_pos_iff (interventionalValue original intervention evidence)

/-- Actual supported conditioned records agree. No value at a null
conditioner is supplied by the native realization or its source coding. -/
theorem conditionOn_probVal (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (supported : (original.interventionalDist intervention.value).EventPositive evidence) :
    QProb.Equiv
      ((((model original).interventionalDist intervention).conditionOn evidence
        ((eventPositive_iff original intervention evidence).mpr supported)).probVal event)
      (((original.interventionalDist intervention.value).conditionOn evidence supported).probVal event) := by
  let supportedNew := (eventPositive_iff original intervention evidence).mpr supported
  exact QProb.equiv_trans (((model original).interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans (QProb.div_congr (interventionalValue original intervention (fun values => evidence values && event values))
      (interventionalValue original intervention evidence) supportedNew supported)
      (QProb.equiv_symm ((original.interventionalDist intervention.value).conditionOn_probVal evidence event supported)))

end Thesis.Causality.LatentRootNative
