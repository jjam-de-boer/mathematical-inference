import Thesis.Causality.Reductions
import Thesis.Causality.ModalCounterfactual
import Thesis.CausalTransport.ModalCounterfactual

namespace Thesis
namespace Causality
namespace Examples

open Probability

/-!
Executable witnesses for the theorem-facing causal layer, including the full
eight-variable tenure-track model. They make the probability, latent
projection, intervention, counterfactual, and proof-carrying modality claims
pass through Lean's kernel.
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
    intro _model _compatible _assignment sourceSupported
    exact ⟨sourceSupported, sourceSupported, ()⟩

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

def setting_transition_is_proof_carrying :
    CausalRecordStep setFirstTransition.label
      setFirstTransition.source.record setFirstTransition.target.record :=
  setFirstTransition.valid

theorem setting_changes_the_equation_override :
    setFirstTransition.target.record.intervention.value firstNode = some true := by
  exact CausalEpistemicRecord.setVariable_at_target sharedInitial firstNode true

theorem setting_preserves_epistemic_belief :
    setFirstTransition.target.record.belief = sharedInitial.belief := by
  rfl

namespace TenureTrack

/-!
The complete eight-variable running example uses the theorem-facing
finite probability, latent-SCM, intervention, and modal APIs.
-/

/-!
The observed coordinates, in topological order, are prestige, quality, topic,
committee expertise, fit, shortlist, funding, and offer. The six latent
coordinates are respectively a shared background cause of prestige and
quality, private prestige and quality seeds, private topic and committee seeds,
and a private funding seed. The declarations below first make this finite model
explicit, then reduce its named events to predicates on the latent assignment,
and finally ask Lean to calculate the resulting finite rational probabilities.
-/

def signature : ObservedSignature where
  count := 8
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
  directed := fun parent child => decide
    ((parent.val = 2 /\ child.val = 4) \/
      (parent.val = 3 /\ child.val = 4) \/
      (parent.val = 1 /\ child.val = 5) \/
      (parent.val = 0 /\ child.val = 5) \/
      (parent.val = 4 /\ child.val = 5) \/
      (parent.val = 2 /\ child.val = 6) \/
      (parent.val = 5 /\ child.val = 7) \/
      (parent.val = 6 /\ child.val = 7))
  directed_earlier := by
    intro parent child edge
    simp at edge
    rcases edge with edge | edge | edge | edge | edge | edge | edge | edge <;>
      omega

def node (value : Nat) (bound : value < signature.count) : Fin signature.count :=
  ⟨value, bound⟩

def prestigeNode : Fin signature.count := node 0 (by decide)
def qualityNode : Fin signature.count := node 1 (by decide)
def topicNode : Fin signature.count := node 2 (by decide)
def committeeNode : Fin signature.count := node 3 (by decide)
def fitNode : Fin signature.count := node 4 (by decide)
def shortlistNode : Fin signature.count := node 5 (by decide)
def fundingNode : Fin signature.count := node 6 (by decide)
def offerNode : Fin signature.count := node 7 (by decide)

def bernoulli (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) : FiniteProbRecord Bool where
  atoms := [(false, falseWeight), (true, trueWeight)]
  den := falseWeight + trueWeight
  den_pos := positive
  total_mass := by
    simp [FiniteProbRecord.totalMass, Nat.add_comm]

def latent : LatentExtension signature where
  count := 6
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun source child => decide
    ((source.val = 0 /\ (child.val = 0 \/ child.val = 1)) \/
      (source.val = 1 /\ child.val = 0) \/
      (source.val = 2 /\ child.val = 1) \/
      (source.val = 3 /\ child.val = 2) \/
      (source.val = 4 /\ child.val = 3) \/
      (source.val = 5 /\ child.val = 6))

/-- The six independent Bernoulli factors, ordered by the latent names below. -/
def factor (source : Fin latent.count) : FiniteProbRecord Bool :=
  match source.val with
  | 0 => bernoulli 1 2 (by decide)
  | 1 => bernoulli 1 3 (by decide)
  | 2 => bernoulli 1 3 (by decide)
  | 3 => bernoulli 1 1 (by decide)
  | 4 => bernoulli 1 1 (by decide)
  | _ => bernoulli 1 3 (by decide)

def prior : FiniteProbRecord latent.Assignment :=
  FiniteProduct.record latent.count latent.Value factor

def source (value : Nat) (bound : value < latent.count) : Fin latent.count :=
  ⟨value, bound⟩

def backgroundSource : Fin latent.count := source 0 (by decide)
def prestigeSource : Fin latent.count := source 1 (by decide)
def qualitySource : Fin latent.count := source 2 (by decide)
def topicSource : Fin latent.count := source 3 (by decide)
def committeeSource : Fin latent.count := source 4 (by decide)
def fundingSource : Fin latent.count := source 5 (by decide)

theorem background_prestige :
    latent.incident backgroundSource prestigeNode = true := by decide
theorem prestige_prestige :
    latent.incident prestigeSource prestigeNode = true := by decide
theorem background_quality :
    latent.incident backgroundSource qualityNode = true := by decide
theorem quality_quality :
    latent.incident qualitySource qualityNode = true := by decide
theorem topic_topic :
    latent.incident topicSource topicNode = true := by decide
theorem committee_committee :
    latent.incident committeeSource committeeNode = true := by decide
theorem funding_funding :
    latent.incident fundingSource fundingNode = true := by decide

theorem topic_fit : signature.directed topicNode fitNode = true := by decide
theorem committee_fit :
    signature.directed committeeNode fitNode = true := by decide
theorem quality_shortlist :
    signature.directed qualityNode shortlistNode = true := by decide
theorem prestige_shortlist :
    signature.directed prestigeNode shortlistNode = true := by decide
theorem fit_shortlist :
    signature.directed fitNode shortlistNode = true := by decide
theorem topic_funding :
    signature.directed topicNode fundingNode = true := by decide
theorem shortlist_offer :
    signature.directed shortlistNode offerNode = true := by decide
theorem funding_offer :
    signature.directed fundingNode offerNode = true := by decide

theorem remaining_child_is_offer (child : Fin signature.count)
    (h0 : child ≠ prestigeNode) (h1 : child ≠ qualityNode)
    (h2 : child ≠ topicNode) (h3 : child ≠ committeeNode)
    (h4 : child ≠ fitNode) (h5 : child ≠ shortlistNode)
    (h6 : child ≠ fundingNode) : child = offerNode := by
  apply Fin.ext
  have childBound := child.isLt
  simp [signature] at childBound
  simp [prestigeNode, qualityNode, topicNode, committeeNode, fitNode,
    shortlistNode, fundingNode, offerNode, node, signature] at h0 h1 h2 h3 h4 h5 h6 ⊢
  omega

/--
The complete tenure-track SCM. The ordered conditional chain in this definition
is exactly the structural-equation display in the thesis; every branch is
selected by the documented coordinate names above.
-/
def model : ExactModel signature where
  latent := latent
  factor := factor
  prior := prior
  product_law := by
    intro events
    simpa [prior, latent, LatentExtension.rectangularEvent] using
      (FiniteProduct.record_rectangular_probVal latent.count latent.Value
        factor events)
  mechanism := fun child parents latents =>
    if h0 : child = prestigeNode then
      latents backgroundSource (h0 ▸ background_prestige) ||
        latents prestigeSource (h0 ▸ prestige_prestige)
    else if h1 : child = qualityNode then
      latents backgroundSource (h1 ▸ background_quality) ||
        latents qualitySource (h1 ▸ quality_quality)
    else if h2 : child = topicNode then
      latents topicSource (h2 ▸ topic_topic)
    else if h3 : child = committeeNode then
      latents committeeSource (h3 ▸ committee_committee)
    else if h4 : child = fitNode then
      parents topicNode (h4 ▸ topic_fit) &&
        parents committeeNode (h4 ▸ committee_fit)
    else if h5 : child = shortlistNode then
      parents qualityNode (h5 ▸ quality_shortlist) &&
        (parents prestigeNode (h5 ▸ prestige_shortlist) ||
          parents fitNode (h5 ▸ fit_shortlist))
    else if h6 : child = fundingNode then
      parents topicNode (h6 ▸ topic_funding) ||
        latents fundingSource (h6 ▸ funding_funding)
    else
      let h7 := remaining_child_is_offer child h0 h1 h2 h3 h4 h5 h6
      parents shortlistNode (h7 ▸ shortlist_offer) &&
        parents fundingNode (h7 ▸ funding_offer)

theorem model_is_canonical_semiMarkovian :
    model.IsCanonicalSemiMarkovian := by
  intro source i j k hi hj hk
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hik : i = k
  · exact Or.inr (Or.inl hik)
  by_cases hjk : j = k
  · exact Or.inr (Or.inr hjk)
  have hvij : i.val ≠ j.val := fun equal => hij (Fin.ext equal)
  have hvik : i.val ≠ k.val := fun equal => hik (Fin.ext equal)
  have hvjk : j.val ≠ k.val := fun equal => hjk (Fin.ext equal)
  simp [model, latent] at hi hj hk
  omega

theorem background_projects_to_confounding :
    model.observedGraph.bidirected prestigeNode qualityNode = true := by
  decide

/-! ## Events and their latent reductions -/

/-- The observational event that institutional prestige is true. -/
def prestigeEvent (assignment : signature.Assignment) : Bool :=
  assignment prestigeNode

def qualityEvent (assignment : signature.Assignment) : Bool :=
  assignment qualityNode

def fitEvent (assignment : signature.Assignment) : Bool :=
  assignment fitNode

def offerEvent (assignment : signature.Assignment) : Bool :=
  assignment offerNode

def prestigeAndQualityEvent (assignment : signature.Assignment) : Bool :=
  prestigeEvent assignment && qualityEvent assignment

def fitAndOfferEvent (assignment : signature.Assignment) : Bool :=
  fitEvent assignment && offerEvent assignment

def noPrestigeGoodNoOfferEvent (assignment : signature.Assignment) : Bool :=
  !prestigeEvent assignment && qualityEvent assignment && !offerEvent assignment

/-- A convenient unreduced rational literal for the displayed example values. -/
def ratio (num den : Nat) (positive : 0 < den) : QProb :=
  ⟨num, den, positive⟩

def setPrestigeTrue : HardIntervention signature :=
  (HardIntervention.empty signature).set prestigeNode true

def setFitTrue : HardIntervention signature :=
  (HardIntervention.empty signature).set fitNode true

def latentPrestige (u : model.latent.Assignment) : Bool :=
  u backgroundSource || u prestigeSource

def latentQuality (u : model.latent.Assignment) : Bool :=
  u backgroundSource || u qualitySource

def latentFit (u : model.latent.Assignment) : Bool :=
  u topicSource && u committeeSource

def latentShortlist (u : model.latent.Assignment) : Bool :=
  latentQuality u && (latentPrestige u || latentFit u)

def latentFunding (u : model.latent.Assignment) : Bool :=
  u topicSource || u fundingSource

def latentOffer (u : model.latent.Assignment) : Bool :=
  latentShortlist u && latentFunding u

def latentPrestigeAndQuality (u : model.latent.Assignment) : Bool :=
  latentPrestige u && latentQuality u

def latentFitAndOffer (u : model.latent.Assignment) : Bool :=
  latentFit u && latentOffer u

def latentEvidence (u : model.latent.Assignment) : Bool :=
  !latentPrestige u && latentQuality u && !latentOffer u

def latentOfferDoPrestige (u : model.latent.Assignment) : Bool :=
  latentQuality u && latentFunding u

def latentOfferDoFit (u : model.latent.Assignment) : Bool :=
  latentQuality u && latentFunding u

/-!
## Structural evaluation lemmas

These lemmas connect each named observed event to a Boolean predicate on the
six independent latent bits. They are the bridge between the structural
equations above and the closed finite computations below.
-/

theorem eval_prestige (u : model.latent.Assignment) :
    prestigeEvent (model.eval u) = latentPrestige u := by
  simp [prestigeEvent, latentPrestige, FiniteLatentSCM.eval,
    FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder,
    FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention, model,
    prestigeNode, qualityNode, topicNode, committeeNode, fitNode,
    shortlistNode, fundingNode, offerNode, node, signature]

theorem eval_quality (u : model.latent.Assignment) :
    qualityEvent (model.eval u) = latentQuality u := by
  simp [qualityEvent, latentQuality, FiniteLatentSCM.eval,
    FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder,
    FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention, model,
    prestigeNode, qualityNode, topicNode, committeeNode, fitNode,
    shortlistNode, fundingNode, offerNode, node, signature]

theorem eval_fit (u : model.latent.Assignment) :
    fitEvent (model.eval u) = latentFit u := by
  simp [fitEvent, latentFit, FiniteLatentSCM.eval,
    FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder,
    FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention, model,
    prestigeNode, qualityNode, topicNode, committeeNode, fitNode,
    shortlistNode, fundingNode, offerNode, node, signature]

theorem eval_offer (u : model.latent.Assignment) :
    offerEvent (model.eval u) = latentOffer u := by
  simp [offerEvent, latentOffer, latentShortlist, latentFunding, latentQuality,
    latentPrestige, latentFit, FiniteLatentSCM.eval, FiniteLatentSCM.evalUnder,
    FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.equationUnder,
    FiniteLatentSCM.noIntervention, model, prestigeNode, qualityNode,
    topicNode, committeeNode, fitNode, shortlistNode, fundingNode, offerNode,
    node, signature]

theorem eval_prestigeAndQuality (u : model.latent.Assignment) :
    prestigeAndQualityEvent (model.eval u) = latentPrestigeAndQuality u := by
  simp [prestigeAndQualityEvent, latentPrestigeAndQuality, eval_prestige,
    eval_quality]

theorem eval_fitAndOffer (u : model.latent.Assignment) :
    fitAndOfferEvent (model.eval u) = latentFitAndOffer u := by
  simp [fitAndOfferEvent, latentFitAndOffer, eval_fit, eval_offer]

theorem eval_evidence (u : model.latent.Assignment) :
    noPrestigeGoodNoOfferEvent (model.eval u) = latentEvidence u := by
  simp [noPrestigeGoodNoOfferEvent, latentEvidence, eval_prestige,
    eval_quality, eval_offer]

theorem eval_offer_doPrestige (u : model.latent.Assignment) :
    offerEvent (model.evalUnder setPrestigeTrue.value u) =
      latentOfferDoPrestige u := by
  simp [offerEvent, latentOfferDoPrestige, latentQuality, latentFunding,
    setPrestigeTrue, HardIntervention.set, HardIntervention.empty,
    FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder,
    FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention, model,
    prestigeNode, qualityNode, topicNode, committeeNode, fitNode,
    shortlistNode, fundingNode, offerNode, node, signature]

theorem eval_offer_doFit (u : model.latent.Assignment) :
    offerEvent (model.evalUnder setFitTrue.value u) = latentOfferDoFit u := by
  simp [offerEvent, latentOfferDoFit, latentQuality, latentFunding,
    setFitTrue, HardIntervention.set, HardIntervention.empty,
    FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder,
    FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention, model,
    prestigeNode, qualityNode, topicNode, committeeNode, fitNode,
    shortlistNode, fundingNode, offerNode, node, signature]

/-!
## Closed finite probability calculations

Each theorem in this block is discharged by kernel reduction over the finite
six-bit latent sample space. The local recursion-depth setting only permits
that normalisation to finish; it changes neither the model nor the statement
being checked.
-/

set_option maxRecDepth 100000 in
theorem prior_prestige :
    QProb.Equiv (model.prior.probVal latentPrestige)
      (ratio 1 2 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem prior_quality :
    QProb.Equiv (model.prior.probVal latentQuality)
      (ratio 1 2 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem prior_prestigeAndQuality :
    QProb.Equiv (model.prior.probVal latentPrestigeAndQuality)
      (ratio 3 8 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem prior_fit :
    QProb.Equiv (model.prior.probVal latentFit)
      (ratio 1 4 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem prior_fitAndOffer :
    QProb.Equiv (model.prior.probVal latentFitAndOffer)
      (ratio 1 8 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem prior_offerDoFit :
    QProb.Equiv (model.prior.probVal latentOfferDoFit)
      (ratio 5 16 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem prior_evidence :
    QProb.Equiv (model.prior.probVal latentEvidence)
      (ratio 3 32 (by decide)) := by decide

def latentEvidenceAndOfferDoPrestige (u : model.latent.Assignment) : Bool :=
  latentEvidence u && latentOfferDoPrestige u

def latentEvidenceAndOfferDoFit (u : model.latent.Assignment) : Bool :=
  latentEvidence u && latentOfferDoFit u

set_option maxRecDepth 100000 in
theorem prior_evidenceAndOfferDoPrestige :
    QProb.Equiv (model.prior.probVal latentEvidenceAndOfferDoPrestige)
      (ratio 3 64 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem prior_evidenceAndOfferDoFit :
    QProb.Equiv (model.prior.probVal latentEvidenceAndOfferDoFit)
      (ratio 3 64 (by decide)) := by decide

/-!
## Lift latent calculations to observed and interventional queries

The next two reusable lemmas are intentionally not computational: they state
the general pushforward step that turns an evaluation equality plus one checked
latent probability into a probability of an SCM event. The named probability
theorems following them are short applications of this bridge.
-/

theorem observational_from_prior
    (event : signature.Assignment -> Bool)
    (latentEvent : model.latent.Assignment -> Bool)
    (evaluation : forall u, event (model.eval u) = latentEvent u)
    (value : QProb) (priorValue : QProb.Equiv
      (model.prior.probVal latentEvent) value) :
    QProb.Equiv (model.observationalValue event) value :=
  QProb.equiv_trans (model.observationalValue_eq event)
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _ evaluation)
      priorValue)

theorem interventional_from_prior
    (target : (i : Fin signature.count) -> Option (signature.Value i))
    (event : signature.Assignment -> Bool)
    (latentEvent : model.latent.Assignment -> Bool)
    (evaluation : forall u, event (model.evalUnder target u) = latentEvent u)
    (value : QProb) (priorValue : QProb.Equiv
      (model.prior.probVal latentEvent) value) :
    QProb.Equiv (model.interventionalValue target event) value :=
  QProb.equiv_trans (model.interventionalValue_eq target event)
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _ evaluation)
      priorValue)

theorem prob_prestige_true :
    QProb.Equiv (model.observationalValue prestigeEvent)
      (ratio 1 2 (by decide)) := by
  exact QProb.equiv_trans (model.observationalValue_eq prestigeEvent)
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _ eval_prestige)
      prior_prestige)

theorem prob_quality_true :
    QProb.Equiv (model.observationalValue qualityEvent)
      (ratio 1 2 (by decide)) := by
  exact observational_from_prior qualityEvent latentQuality eval_quality _
    prior_quality

theorem prob_prestige_and_quality_true :
    QProb.Equiv (model.observationalValue prestigeAndQualityEvent)
      (ratio 3 8 (by decide)) := by
  exact observational_from_prior prestigeAndQualityEvent
    latentPrestigeAndQuality eval_prestigeAndQuality _
      prior_prestigeAndQuality

theorem prob_fit_true :
    QProb.Equiv (model.observationalValue fitEvent)
      (ratio 1 4 (by decide)) := by
  exact observational_from_prior fitEvent latentFit eval_fit _ prior_fit

theorem prob_fit_and_offer_true :
    QProb.Equiv (model.observationalValue fitAndOfferEvent)
      (ratio 1 8 (by decide)) := by
  exact observational_from_prior fitAndOfferEvent latentFitAndOffer
    eval_fitAndOffer _ prior_fitAndOffer

theorem prob_quality_given_prestige :
    QProb.Equiv
      (QProb.div (model.observationalValue prestigeAndQualityEvent)
        (model.observationalValue prestigeEvent)
          ((QProb.equiv_num_pos_iff prob_prestige_true).mpr (by decide)))
      (ratio 3 4 (by decide)) := by
  exact QProb.equiv_trans
    (QProb.div_congr prob_prestige_and_quality_true prob_prestige_true
      ((QProb.equiv_num_pos_iff prob_prestige_true).mpr (by decide))
      (by decide))
    (by decide)

theorem prob_quality_do_prestige_true :
    QProb.Equiv
      (model.interventionalValue setPrestigeTrue.value qualityEvent)
      (ratio 1 2 (by decide)) := by
  apply interventional_from_prior setPrestigeTrue.value qualityEvent
    latentQuality
  · intro u
    simp [qualityEvent, latentQuality, setPrestigeTrue,
      HardIntervention.set, HardIntervention.empty,
      FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder,
      FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention, model,
      prestigeNode, qualityNode, topicNode, committeeNode, fitNode,
      shortlistNode, fundingNode, offerNode, node, signature]
  · exact prior_quality

theorem prob_offer_given_fit :
    QProb.Equiv
      (QProb.div (model.observationalValue fitAndOfferEvent)
        (model.observationalValue fitEvent)
          ((QProb.equiv_num_pos_iff prob_fit_true).mpr (by decide)))
      (ratio 1 2 (by decide)) := by
  exact QProb.equiv_trans
    (QProb.div_congr prob_fit_and_offer_true prob_fit_true
      ((QProb.equiv_num_pos_iff prob_fit_true).mpr (by decide))
      (by decide))
    (by decide)

theorem prob_offer_do_fit_true :
    QProb.Equiv
      (model.interventionalValue setFitTrue.value offerEvent)
      (ratio 5 16 (by decide)) := by
  exact interventional_from_prior setFitTrue.value offerEvent
    latentOfferDoFit eval_offer_doFit _ prior_offerDoFit

theorem evidence_probability :
    QProb.Equiv (model.observationalValue noPrestigeGoodNoOfferEvent)
      (ratio 3 32 (by decide)) := by
  exact observational_from_prior noPrestigeGoodNoOfferEvent latentEvidence
    eval_evidence _ prior_evidence

theorem evidence_positive :
    model.CounterfactualSupported noPrestigeGoodNoOfferEvent := by
  simpa [FiniteLatentSCM.CounterfactualSupported,
    FiniteLatentSCM.observationalValue, FiniteProbRecord.probVal] using
      ((QProb.equiv_num_pos_iff evidence_probability).mpr (by decide))

/-!
## Counterfactual, twin-network, and modal endpoint checks

The posterior conditions the shared latent prior on the displayed evidence.
The next results compute the same counterfactual first through direct SCM
semantics, then through a separately materialized twin network, and finally
through the two executed modal construction routes.
-/

def posterior : FiniteProbRecord model.latent.Assignment :=
  model.prior.conditionOn
    (fun u => noPrestigeGoodNoOfferEvent (model.eval u)) (by
      simpa [FiniteLatentSCM.CounterfactualSupported,
        FiniteLatentSCM.observationalDist, FiniteProbRecord.EventPositive,
        FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using
          evidence_positive)

theorem posterior_normalized :
    QProb.Equiv (posterior.probVal topEvent) QProb.one :=
  posterior.normalization

theorem counterfactual_offer_do_prestige_given_evidence :
    QProb.Equiv
      (model.counterfactualValue noPrestigeGoodNoOfferEvent evidence_positive
        setPrestigeTrue.value offerEvent)
      (ratio 1 2 (by decide)) := by
  have numerator : QProb.Equiv
      (model.prior.probVal (fun u =>
        noPrestigeGoodNoOfferEvent (model.eval u) &&
          offerEvent (model.evalUnder setPrestigeTrue.value u)))
      (ratio 3 64 (by decide)) :=
    QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _ (fun u => by
        simp [latentEvidenceAndOfferDoPrestige, eval_evidence,
          eval_offer_doPrestige]))
      prior_evidenceAndOfferDoPrestige
  have denominator : QProb.Equiv
      (model.prior.probVal (fun u =>
        noPrestigeGoodNoOfferEvent (model.eval u)))
      (ratio 3 32 (by decide)) :=
    QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _ eval_evidence)
      prior_evidence
  exact QProb.equiv_trans
    (model.counterfactualValue_eq noPrestigeGoodNoOfferEvent
      evidence_positive setPrestigeTrue.value offerEvent)
    (QProb.equiv_trans
      (QProb.div_congr numerator denominator
        ((QProb.equiv_num_pos_iff denominator).mpr (by decide)) (by decide))
      (by decide))

def prestigeTwin : TwinNetwork signature :=
  model.twinNetwork setPrestigeTrue.value

theorem twin_counterfactual_offer_do_prestige_given_evidence :
    QProb.Equiv
      (prestigeTwin.abductedCounterfactualValue
        noPrestigeGoodNoOfferEvent evidence_positive offerEvent)
      (ratio 1 2 (by decide)) := by
  exact QProb.equiv_trans
    (prestigeTwin.abductedCounterfactualValue_eq_counterfactualValue
      noPrestigeGoodNoOfferEvent evidence_positive offerEvent)
    counterfactual_offer_do_prestige_given_evidence

theorem prestigeTwin_intervention_cuts_incoming
    (parent : Fin signature.count) :
    prestigeTwin.directed (.counterfactual parent)
      (.counterfactual prestigeNode) = false := by
  have selected : prestigeTwin.intervention prestigeNode = some true := by
    simpa [prestigeTwin, FiniteLatentSCM.twinNetwork, setPrestigeTrue] using
      ((HardIntervention.empty signature).set_at_target prestigeNode true)
  exact prestigeTwin.intervention_cuts_counterfactual_directed prestigeNode true
    selected parent

theorem counterfactual_offer_do_fit_given_evidence :
    QProb.Equiv
      (model.counterfactualValue noPrestigeGoodNoOfferEvent evidence_positive
        setFitTrue.value offerEvent)
      (ratio 1 2 (by decide)) := by
  have numerator : QProb.Equiv
      (model.prior.probVal (fun u =>
        noPrestigeGoodNoOfferEvent (model.eval u) &&
          offerEvent (model.evalUnder setFitTrue.value u)))
      (ratio 3 64 (by decide)) :=
    QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _ (fun u => by
        simp [latentEvidenceAndOfferDoFit, eval_evidence, eval_offer_doFit]))
      prior_evidenceAndOfferDoFit
  have denominator : QProb.Equiv
      (model.prior.probVal (fun u =>
        noPrestigeGoodNoOfferEvent (model.eval u)))
      (ratio 3 32 (by decide)) :=
    QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _ eval_evidence)
      prior_evidence
  exact QProb.equiv_trans
    (model.counterfactualValue_eq noPrestigeGoodNoOfferEvent
      evidence_positive setFitTrue.value offerEvent)
    (QProb.equiv_trans
      (QProb.div_congr numerator denominator
        ((QProb.equiv_num_pos_iff denominator).mpr (by decide)) (by decide))
      (by decide))

/-!
## Principal modal query

This final block packages the prestige intervention as the query consumed by
the generic occurrence-indexed construction and connects its actual endpoint
record to the displayed value one half.
-/

/-- The principal counterfactual query used by the modal multiworld example. -/
def prestigeCounterfactualQuery : CounterfactualQuery signature :=
  CounterfactualQuery.singleAction noPrestigeGoodNoOfferEvent
    setPrestigeTrue.value offerEvent

/--
Both atomic construction routes execute the occurrence-indexed SCM for the
principal query.
-/
noncomputable def prestigeModalCombinedConstruction :
    ModalCombinedCounterfactualConstruction
      (AbductionActionPrediction.initialMode model)
      prestigeCounterfactualQuery :=
  ModalCombinedCounterfactualConstruction.canonical
    (AbductionActionPrediction.initialMode model)
    prestigeCounterfactualQuery

/-- The executed atomic endpoint has the query language's semantics. -/
noncomputable def prestigeModalCombinedConstruction_semantics :
    ProbabilityResult.Equivalent
      prestigeModalCombinedConstruction.endpointDenote
      (prestigeCounterfactualQuery.denote model) :=
  prestigeModalCombinedConstruction.semanticAgreement

/-- The actual executed endpoint computes the principal value `1/2`. -/
noncomputable def prestigeModalCombinedConstruction_value :
    ProbabilityResult.Equivalent
      prestigeModalCombinedConstruction.endpointDenote
      (some (ratio 1 2 (by decide))) :=
  ProbabilityResult.trans
    (ModalCombinedCounterfactualConstruction.singleAction_semantics_eq_twinNetwork
      (AbductionActionPrediction.initialMode model)
      noPrestigeGoodNoOfferEvent evidence_positive setPrestigeTrue.value
      offerEvent prestigeModalCombinedConstruction)
    (.value twin_counterfactual_offer_do_prestige_given_evidence)

/-- The structural modal AAP sequence performs the principal counterfactual. -/
theorem modal_aap_counterfactual_offer_do_prestige :
    QProb.Equiv
      (AbductionActionPrediction.prediction model
        noPrestigeGoodNoOfferEvent evidence_positive setPrestigeTrue.value
        offerEvent)
      (ratio 1 2 (by decide)) := by
  exact QProb.equiv_trans
    (AbductionActionPrediction.prediction_eq_counterfactualValue model
      noPrestigeGoodNoOfferEvent evidence_positive setPrestigeTrue.value
      offerEvent)
    counterfactual_offer_do_prestige_given_evidence

/-- Support of the example query is neither stronger nor weaker than evidence positivity. -/
theorem prestigeSingleAction_supported_iff :
    Nonempty ((CounterfactualQuery.singleAction noPrestigeGoodNoOfferEvent
      setPrestigeTrue.value offerEvent).SupportedAt model) <->
      model.CounterfactualSupported noPrestigeGoodNoOfferEvent :=
  CounterfactualQuery.singleAction_supportedAt_iff model
    noPrestigeGoodNoOfferEvent setPrestigeTrue.value offerEvent

end TenureTrack

end Examples
end Causality
end Thesis
