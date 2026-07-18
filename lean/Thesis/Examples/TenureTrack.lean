import Thesis.Causality.Modalities
import Thesis.Causality.Reductions

namespace Thesis
namespace Causality
namespace Examples

open Probability

/-!
Small executable witnesses for the theorem-facing causal layer.  These are
deliberately concrete: they make the latent projection, intervention, and
proof-carrying modality claims pass through Lean's kernel.
-/

def twoBoolSignature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  value_nodup := by
    intro _
    simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by
    intro parent child h
    simp at h

def fairBool : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by omega
  total_mass := rfl

def sharedLatent : LatentExtension twoBoolSignature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun _ _ => true

def firstNode : Fin twoBoolSignature.count := ⟨0, by decide⟩

def secondNode : Fin twoBoolSignature.count := ⟨1, by decide⟩

def sharedSource : Fin sharedLatent.count := ⟨0, by decide⟩

def sharedPrior : FiniteProbRecord sharedLatent.Assignment :=
  fairBool.map (fun b _ => b)

/-- One hidden fair bit is a common cause of both observed variables. -/
def sharedCauseModel : ExactModel twoBoolSignature where
  latent := sharedLatent
  factor := fun _ => fairBool
  prior := sharedPrior
  product_law := by
    intro events
    simpa [sharedPrior, sharedLatent, LatentExtension.rectangularEvent,
      FiniteProduct.rectangularEvent, FiniteProduct.qProduct,
      QProb.mul, QProb.one, QProb.Equiv] using
      (FiniteProbRecord.map_probVal fairBool (fun b _ => b)
        (sharedLatent.rectangularEvent events))
  mechanism := fun _ _ latentInputs => latentInputs sharedSource rfl

theorem shared_source_projects_to_bidirected :
    sharedCauseModel.observedGraph.bidirected firstNode secondNode = true := by
  decide

def firstNodeSet : NodeSet twoBoolSignature :=
  NodeSet.singleton firstNode

def secondNodeSet : NodeSet twoBoolSignature :=
  NodeSet.singleton secondNode

theorem shared_cause_is_d_connected :
    sharedCauseModel.observedGraph.dSeparated
      (.none twoBoolSignature) firstNodeSet secondNodeSet NodeSet.empty =
        false := by
  decide

theorem intervention_cut_d_separates_shared_cause :
    sharedCauseModel.observedGraph.dSeparated
      (.bar firstNodeSet) firstNodeSet secondNodeSet NodeSet.empty = true := by
  decide

/-- Embed the two observed nodes after two hidden nodes. -/
def hiddenPathObservedNode (i : Fin twoBoolSignature.count) : Fin 4 :=
  ⟨i.val + 2, by
    change i.val + 2 < 4
    have hi : i.val < 2 := i.isLt
    omega⟩

def firstHidden : Fin 4 := ⟨0, by decide⟩

def secondHidden : Fin 4 := ⟨1, by decide⟩

/--
An all-directed hidden DAG in which the common cause reaches the first
observed node through a second hidden node and reaches the other directly.
-/
def hiddenPathDAG : FiniteHiddenDAG twoBoolSignature where
  count := 4
  observedNode := hiddenPathObservedNode
  observedNode_injective := by
    intro i j h
    apply Fin.ext
    simp [hiddenPathObservedNode] at h
    omega
  hidden := fun i => decide (i.val < 2)
  observed_not_hidden := by
    intro i
    simp [hiddenPathObservedNode]
  node_classified := by
    intro node
    by_cases hidden : node.val < 2
    · left
      simp [hidden]
    · right
      have nodeBound := node.isLt
      let observed : Fin twoBoolSignature.count :=
        ⟨node.val - 2, by
          change node.val - 2 < 2
          omega⟩
      exact ⟨observed, by
        apply Fin.ext
        simp [hiddenPathObservedNode, observed]
        omega⟩
  edge := fun i j => decide
    ((i.val = 0 /\ j.val = 1) \/
      (i.val = 1 /\ j.val = 2) \/
      (i.val = 0 /\ j.val = 3))
  rank := fun i => i.val
  edge_rank_lt := by
    intro i j h
    simp at h
    rcases h with h | h | h <;> omega

theorem hidden_path_projects_to_bidirected :
    hiddenPathDAG.projectedBidirected firstNode secondNode := by
  refine ⟨by decide, firstHidden, by decide, ?_, ?_⟩
  · refine .tail (j := secondHidden) (.direct (by decide)) (by decide) ?_
    decide
  · exact .direct (by decide)

theorem hiddenPathDAG_no_path_from_observed (i) (node) :
    Not (hiddenPathDAG.HiddenInternalPath
      (hiddenPathDAG.observedNode i) node) := by
  intro path
  induction path with
  | direct edge =>
      simp [hiddenPathDAG, hiddenPathObservedNode] at edge
  | tail _ _ _ ih => exact ih

theorem hiddenPathDAG_directed_matches :
    hiddenPathDAG.DirectedProjectionMatches := by
  intro i j
  constructor
  · intro edge
    simp [twoBoolSignature] at edge
  · intro path
    exact (hiddenPathDAG_no_path_from_observed i _ path).elim

def oneBoolSignature : ObservedSignature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  value_nodup := by
    intro _
    simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by
    intro _ _ edge
    simp at edge

def privateSeedPrior :
    FiniteProbRecord ((i : Fin oneBoolSignature.count) -> Bool) :=
  fairBool.map (fun seed _ => seed)

/-- A one-node functional network with an independent private fair seed. -/
def privateSeedNetwork : FunctionalCBN oneBoolSignature where
  Seed := fun _ => Bool
  seedEnumeration := fun _ => [false, true]
  seed_complete := by
    intro _ seed
    cases seed <;> simp
  seedDecidableEq := fun _ => inferInstance
  factor := fun _ => fairBool
  prior := privateSeedPrior
  product_law := by
    intro events
    simpa [privateSeedPrior, oneBoolSignature,
      FiniteProduct.rectangularEvent, FiniteProduct.qProduct,
      QProb.mul, QProb.one, QProb.Equiv] using
      (FiniteProbRecord.map_probVal fairBool (fun seed _ => seed)
        (FiniteProduct.rectangularEvent 1 (fun _ => Bool) events))
  mechanism := fun _ _ seed => seed

theorem private_seed_conversion_is_markovian :
    privateSeedNetwork.toSCM.IsMarkovian :=
  privateSeedNetwork.toSCM_isMarkovian

def setFirstTrue : HardIntervention twoBoolSignature :=
  (HardIntervention.empty twoBoolSignature).set firstNode true

def secondTrueAfterFirstTrue : InterventionalQuery twoBoolSignature where
  intervention := setFirstTrue
  outcomeNodes := secondNodeSet
  action_outcome_disjoint := by
    intro i targeted
    by_cases first : i = firstNode
    · subst i
      decide
    · simp [setFirstTrue, HardIntervention.targets, HardIntervention.empty,
        HardIntervention.set, FiniteLatentSCM.noIntervention, first] at targeted
  event := fun assignment => assignment secondNode
  event_local := by
    intro left right agreement
    exact agreement secondNode (by decide)

def observationalSecondQuery : JointKernelQuery twoBoolSignature where
  outcome := secondNodeSet
  action := NodeSet.empty
  action_outcome_disjoint := by
    intro i impossible
    simp [NodeSet.empty] at impossible

/-- A concrete certificate whose recursive support witness reaches Lean's kernel. -/
noncomputable def observationalSecondCertificate :
    JointIdentificationCertificate sharedCauseModel.observedGraph
      observationalSecondQuery where
  formula := observationalSecondQuery.sourceTerm
  actionFree := by
    intro _
    rfl
  derivation := .refl _
  supported := by
    intro model _compatible
    apply DerivationSupport.refl
    intro assignment
    let value :=
      (Kernel.mk secondNodeSet NodeSet.empty NodeSet.empty).distribution
        model assignment
    refine ⟨value.probVal (Kernel.agreesOn secondNodeSet assignment), ?_⟩
    simpa [observationalSecondQuery, JointKernelQuery.sourceTerm] using
      (Kernel.unconditionalDenote model secondNodeSet NodeSet.empty assignment)

theorem intervention_removes_projected_confounding :
    (sharedCauseModel.mutilatedGraph setFirstTrue.value).bidirected
      firstNode secondNode = false := by
  apply sharedCauseModel.do_removes_incident_bidirected
      setFirstTrue.value firstNode true
  exact setFirstTrue.set_at_target firstNode true

def sharedInitial : CausalEpistemicRecord twoBoolSignature :=
  CausalEpistemicRecord.initial sharedCauseModel

def setFirstTransition : CausalTransition twoBoolSignature :=
  CausalTransition.setting "observational" "do-first" sharedInitial
    firstNode true

theorem setting_transition_is_proof_carrying :
    CausalRecordStep setFirstTransition.label
      setFirstTransition.source.record setFirstTransition.target.record :=
  setFirstTransition.valid

theorem setting_changes_the_equation_override :
    setFirstTransition.target.record.intervention.value firstNode = some true := by
  exact CausalEpistemicRecord.setVariable_at_target sharedInitial firstNode true

theorem setting_preserves_epistemic_belief :
    setFirstTransition.target.record.belief = sharedInitial.belief := by
  rfl

def epistemicEdge : EpistemicRelation twoBoolSignature :=
  (firstNode, secondNode)

theorem relating_is_noncausal_metadata :
    ((sharedInitial.relate epistemicEdge).unrelate epistemicEdge) =
      sharedInitial :=
  sharedInitial.unrelate_relate_cancel epistemicEdge

end Examples
end Causality
end Thesis
