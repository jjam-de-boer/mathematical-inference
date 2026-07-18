import Thesis.CausalTransport.Correspondence

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

def observedProb (R : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) : Rat :=
  R.observedDist.probRat event

def conditionLatent (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : 0 < R.belief.probRat evidence) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief.condition evidence hEvidence
  intervention := R.intervention
  relations := R.relations

def conditionObservation (R : CausalEpistemicRecord S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : 0 < R.observedProb evidence) :
    CausalEpistemicRecord S :=
  R.conditionLatent
    (fun u => evidence (R.model.evalUnder R.intervention.value u)) (by
      simpa [observedProb, observedDist, FiniteProbRecord.map_probRat] using
        hEvidence)

def setVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.set target value
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
    (hEvidence : 0 < R.belief.probRat evidence) :
    (R.conditionLatent evidence hEvidence).model = R.model := by
  rfl

theorem conditioning_keeps_product_prior (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : 0 < R.belief.probRat evidence) :
    (R.conditionLatent evidence hEvidence).model.prior = R.model.prior := by
  rfl

theorem setting_keeps_belief (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).belief = R.belief := by
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

end CausalEpistemicRecord

inductive CausalTransitionLabel where
  | conditioning
  | setting
  | relating
  | unrelating
  deriving DecidableEq, Repr

inductive CausalRecordStep :
    CausalTransitionLabel ->
      CausalEpistemicRecord S -> CausalEpistemicRecord S -> Prop
  | conditioning (R : CausalEpistemicRecord S)
      (evidence : R.model.latent.Assignment -> Bool)
      (hEvidence : 0 < R.belief.probRat evidence) :
      CausalRecordStep .conditioning R (R.conditionLatent evidence hEvidence)
  | setting (R : CausalEpistemicRecord S)
      (target : Fin S.count) (value : S.Value target) :
      CausalRecordStep .setting R (R.setVariable target value)
  | relating (R : CausalEpistemicRecord S) (edge : EpistemicRelation S) :
      CausalRecordStep .relating R (R.relate edge)
  | unrelating (R : CausalEpistemicRecord S) (edge : EpistemicRelation S) :
      CausalRecordStep .unrelating R (R.unrelate edge)

structure CausalMode (S : ObservedSignature) where
  name : String
  record : CausalEpistemicRecord S

structure CausalTransition (S : ObservedSignature) where
  label : CausalTransitionLabel
  source : CausalMode S
  target : CausalMode S
  valid : CausalRecordStep label source.record target.record

namespace CausalTransition

def conditioning (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : 0 < R.belief.probRat evidence) : CausalTransition S where
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
