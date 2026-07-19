import Thesis.CausalTransport.FiniteSource

namespace Thesis
namespace Causality

open Probability

/-!
Proof-carrying epistemic transitions for the graph-aware causal model.

Operations are ordinary executable record transformations.  A transition does
not perform an operation by inspecting a context; it stores source and target
modes together with a proof that the named operation relates their records.
Conditioning updates `belief`, not the model's product prior.
-/

abbrev EpistemicRelation (S : ObservedSignature) :=
  Fin S.count × Fin S.count

structure CausalEpistemicRecord (S : ObservedSignature) where
  model : ExactModel S
  belief : FiniteProbRecord model.latent.Assignment
  intervention : HardIntervention S
  relations : List (EpistemicRelation S)

namespace CausalEpistemicRecord

def initial (model : ExactModel S) : CausalEpistemicRecord S where
  model := model
  belief := model.prior
  intervention := HardIntervention.empty S
  relations := []

def observedDist (R : CausalEpistemicRecord S) :
    FiniteProbRecord S.Assignment :=
  R.belief.map (R.model.evalUnder R.intervention.value)

def observedValue (R : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) : QProb :=
  R.observedDist.probVal event

def conditionLatent (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief.conditionOn evidence hEvidence
  intervention := R.intervention
  relations := R.relations

def conditionObservation (R : CausalEpistemicRecord S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : R.observedDist.EventPositive evidence) :
    CausalEpistemicRecord S :=
  R.conditionLatent
    (fun u => evidence (R.model.evalUnder R.intervention.value u)) (by
      simpa [observedDist, FiniteProbRecord.EventPositive,
        FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using
          hEvidence)

def setVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.set target value
  relations := R.relations

def unsetVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) : CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.unset target
  relations := R.relations

def relate (R : CausalEpistemicRecord S) (edge : EpistemicRelation S) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention
  relations := edge :: R.relations

def unrelate (R : CausalEpistemicRecord S) (edge : EpistemicRelation S) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention
  relations := R.relations.erase edge

theorem conditioning_keeps_model (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).model = R.model := by
  rfl

theorem conditioning_keeps_product_prior (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).model.prior = R.model.prior := by
  rfl

theorem setting_keeps_belief (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).belief = R.belief := by
  rfl

theorem unsetting_keeps_belief (R : CausalEpistemicRecord S)
    (target : Fin S.count) :
    (R.unsetVariable target).belief = R.belief := by
  rfl

theorem setVariable_at_target (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).intervention.value target = some value := by
  exact R.intervention.set_at_target target value

theorem unrelate_relate_cancel (R : CausalEpistemicRecord S)
    (edge : EpistemicRelation S) :
    (R.relate edge).unrelate edge = R := by
  cases R
  simp [relate, unrelate]

theorem conditionLatent_probVal (R : CausalEpistemicRecord S)
    (evidence event : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    QProb.Equiv
      ((R.conditionLatent evidence hEvidence).belief.probVal event)
      (QProb.div
        (R.belief.probVal (fun u => evidence u && event u))
        (R.belief.probVal evidence) hEvidence) :=
  R.belief.conditionOn_probVal evidence event hEvidence

theorem observedDist_probVal (R : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (R.observedDist.probVal event)
      (R.belief.probVal
        (fun u => event (R.model.evalUnder R.intervention.value u))) :=
  FiniteProbRecord.map_probVal R.belief
    (R.model.evalUnder R.intervention.value) event

end CausalEpistemicRecord

inductive CausalTransitionLabel where
  | conditioning
  | setting
  | unsetting
  | relating
  | unrelating
  deriving DecidableEq, Repr

inductive CausalRecordStep :
    CausalTransitionLabel ->
      CausalEpistemicRecord S -> CausalEpistemicRecord S -> Prop
  | conditioning (R : CausalEpistemicRecord S)
      (evidence : R.model.latent.Assignment -> Bool)
      (hEvidence : R.belief.EventPositive evidence) :
      CausalRecordStep .conditioning R (R.conditionLatent evidence hEvidence)
  | setting (R : CausalEpistemicRecord S)
      (target : Fin S.count) (value : S.Value target) :
      CausalRecordStep .setting R (R.setVariable target value)
  | unsetting (R : CausalEpistemicRecord S) (target : Fin S.count) :
      CausalRecordStep .unsetting R (R.unsetVariable target)
  | relating (R : CausalEpistemicRecord S) (edge : EpistemicRelation S) :
      CausalRecordStep .relating R (R.relate edge)
  | unrelating (R : CausalEpistemicRecord S) (edge : EpistemicRelation S) :
      CausalRecordStep .unrelating R (R.unrelate edge)

theorem CausalRecordStep.model_eq
    (step : CausalRecordStep label source target) :
    target.model = source.model := by
  cases step <;> rfl

structure CausalMode (S : ObservedSignature) where
  name : String
  record : CausalEpistemicRecord S

namespace CausalMode

def JointIdentifiable (mode : CausalMode S) (query : JointKernelQuery S) : Prop :=
  TypeTheoreticIdentifiable mode.record.model.observedGraph query

def ConditionalIdentifiable (mode : CausalMode S)
    (query : ConditionalKernelQuery S) : Prop :=
  TypeTheoreticConditionalIdentifiable mode.record.model.observedGraph query

def CompatibleWith (mode : CausalMode S) (graph : ObservedGraph S) : Prop :=
  Compatible mode.record.model graph

def JointIdentifiableOn (_mode : CausalMode S) (graph : ObservedGraph S)
    (query : JointKernelQuery S) : Prop :=
  TypeTheoreticIdentifiable graph query

def ConditionalIdentifiableOn (_mode : CausalMode S)
    (graph : ObservedGraph S) (query : ConditionalKernelQuery S) : Prop :=
  TypeTheoreticConditionalIdentifiable graph query

theorem transported_joint_iff (mode : CausalMode S)
    (complete : PublishedCompleteness S mode.record.model.observedGraph)
    (sound : PublishedSoundness S mode.record.model.observedGraph)
    (query : JointKernelQuery S) :
    mode.JointIdentifiable query <->
      Nonempty (EncodedJointDerivation mode.record.model.observedGraph query) :=
  Causality.transported_joint_iff complete sound query

theorem transported_conditional_iff (mode : CausalMode S)
    (complete : PublishedCompleteness S mode.record.model.observedGraph)
    (sound : PublishedSoundness S mode.record.model.observedGraph)
    (query : ConditionalKernelQuery S) :
    mode.ConditionalIdentifiable query <->
      Nonempty (EncodedConditionalDerivation
        mode.record.model.observedGraph query) :=
  Causality.transported_conditional_iff complete sound query

theorem finiteSource_transported_joint_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (_currentCompatible : mode.CompatibleWith G.interpret)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : JointKernelQuery T.toObserved) :
    mode.JointIdentifiableOn G.interpret query <->
      Nonempty (EncodedJointDerivation G.interpret query) :=
  Causality.finiteSource_transported_joint_iff complete sound query

theorem finiteSource_transported_conditional_iff
    (mode : CausalMode T.toObserved) (G : FiniteTableGraph T)
    (_currentCompatible : mode.CompatibleWith G.interpret)
    (complete : PublishedFiniteSourceCompleteness T G)
    (sound : PublishedFiniteSourceSoundness T G)
    (query : ConditionalKernelQuery T.toObserved) :
    mode.ConditionalIdentifiableOn G.interpret query <->
      Nonempty (EncodedConditionalDerivation G.interpret query) :=
  Causality.finiteSource_transported_conditional_iff complete sound query

end CausalMode

structure CausalTransition (S : ObservedSignature) where
  label : CausalTransitionLabel
  source : CausalMode S
  target : CausalMode S
  valid : CausalRecordStep label source.record target.record

namespace CausalTransition

theorem model_eq (transition : CausalTransition S) :
    transition.target.record.model = transition.source.record.model :=
  transition.valid.model_eq

theorem jointIdentifiable_iff (transition : CausalTransition S)
    (query : JointKernelQuery S) :
    transition.source.JointIdentifiable query <->
      transition.target.JointIdentifiable query := by
  rw [CausalMode.JointIdentifiable, CausalMode.JointIdentifiable,
    transition.model_eq]

theorem conditionalIdentifiable_iff (transition : CausalTransition S)
    (query : ConditionalKernelQuery S) :
    transition.source.ConditionalIdentifiable query <->
      transition.target.ConditionalIdentifiable query := by
  rw [CausalMode.ConditionalIdentifiable, CausalMode.ConditionalIdentifiable,
    transition.model_eq]

theorem compatibleWith_iff (transition : CausalTransition S)
    (graph : ObservedGraph S) :
    transition.source.CompatibleWith graph <->
      transition.target.CompatibleWith graph := by
  rw [CausalMode.CompatibleWith, CausalMode.CompatibleWith,
    transition.model_eq]

def conditioning (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) : CausalTransition S where
  label := .conditioning
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.conditionLatent evidence hEvidence⟩
  valid := CausalRecordStep.conditioning R evidence hEvidence

def setting (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) : CausalTransition S where
  label := .setting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.setVariable target value⟩
  valid := CausalRecordStep.setting R target value

def unsetting (sourceName targetName : String)
    (R : CausalEpistemicRecord S) (target : Fin S.count) :
    CausalTransition S where
  label := .unsetting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.unsetVariable target⟩
  valid := CausalRecordStep.unsetting R target

def relating (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (edge : EpistemicRelation S) : CausalTransition S where
  label := .relating
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.relate edge⟩
  valid := CausalRecordStep.relating R edge

def unrelating (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (edge : EpistemicRelation S) : CausalTransition S where
  label := .unrelating
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.unrelate edge⟩
  valid := CausalRecordStep.unrelating R edge

end CausalTransition

end Causality
end Thesis
