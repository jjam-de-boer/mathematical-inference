import Thesis.Legacy.SCM

namespace Thesis
namespace Modalities

open Probability

/-!
A small finite transition layer for the thesis' epistemic modalities.

This is not a formalization of Gratzer's modal type theory.  The mode theory is
represented only by fixed transition labels.  The actual context/SCM changes
are explicit finite record transformations on source and target modes.
-/

inductive TransitionLabel where
  | learning
  | forgetting
  | conditioning
  | relating
  | unrelating
  | setting
  | unsetting
  deriving DecidableEq, Repr

inductive VarKind where
  | endogenous
  | exogenous
  deriving DecidableEq, Repr

structure VarRef where
  kind : VarKind
  index : Nat
  deriving DecidableEq, Repr

abbrev Relation := VarRef × VarRef

def VarRefBounded (endoCount exoCount : Nat) (ref : VarRef) : Prop :=
  match ref.kind with
  | VarKind.endogenous => ref.index < endoCount
  | VarKind.exogenous => ref.index < exoCount

def RelationBounded (endoCount exoCount : Nat) (edge : Relation) : Prop :=
  VarRefBounded endoCount exoCount edge.1 ∧
    VarRefBounded endoCount exoCount edge.2

theorem VarRefBounded.endoSucc {endoCount exoCount : Nat} {ref : VarRef}
    (h : VarRefBounded endoCount exoCount ref) :
    VarRefBounded (endoCount + 1) exoCount ref := by
  cases ref with
  | mk kind index =>
      cases kind <;> simp [VarRefBounded] at h ⊢
      · exact Nat.lt_trans h (Nat.lt_succ_self endoCount)
      · exact h

theorem RelationBounded.endoSucc {endoCount exoCount : Nat} {edge : Relation}
    (h : RelationBounded endoCount exoCount edge) :
    RelationBounded (endoCount + 1) exoCount edge :=
  ⟨h.1.endoSucc, h.2.endoSucc⟩

def learnFreshModel (M : RecursiveSCMData A U) (fresh : List A -> U -> A) :
    RecursiveSCMData A U where
  n := M.n + 1
  noise := M.noise
  fn := fun i xs u =>
    if h : i.val < M.n then M.fn ⟨i.val, h⟩ xs u else fresh xs u

theorem learnFreshModel_old_fn (M : RecursiveSCMData A U)
    (fresh : List A -> U -> A) (i : Fin M.n) (xs : List A) (u : U) :
    (learnFreshModel M fresh).fn ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ xs u =
      M.fn i xs u := by
  simp [learnFreshModel]

def forgetLastModel (M : RecursiveSCMData A U) (_hpos : 0 < M.n) :
    RecursiveSCMData A U where
  n := M.n - 1
  noise := M.noise
  fn := fun i xs u =>
    M.fn ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le M.n 1)⟩ xs u

theorem forgetLastModel_learnFresh_cancel (M : RecursiveSCMData A U)
    (fresh : List A -> U -> A) :
    forgetLastModel (learnFreshModel M fresh) (Nat.succ_pos M.n) = M := by
  cases M
  simp [forgetLastModel, learnFreshModel]

def setModel (M : RecursiveSCMData A U) (target : Fin M.n) (value : A) :
    RecursiveSCMData A U where
  n := M.n
  noise := M.noise
  fn := fun i xs u => if i = target then value else M.fn i xs u

theorem setModel_target_fn (M : RecursiveSCMData A U)
    (target : Fin M.n) (value : A) (xs : List A) (u : U) :
    (setModel M target value).fn target xs u = value := by
  simp [setModel]

theorem setModel_other_fn (M : RecursiveSCMData A U)
    (target i : Fin M.n) (value : A) (xs : List A) (u : U)
    (h : i ≠ target) :
    (setModel M target value).fn i xs u = M.fn i xs u := by
  simp [setModel, h]

def unsetModel (M : RecursiveSCMData A U) (target : Fin M.n)
    (oldFn : List A -> U -> A) : RecursiveSCMData A U where
  n := M.n
  noise := M.noise
  fn := fun i xs u => if i = target then oldFn xs u else M.fn i xs u

def conditionNoiseModel (M : RecursiveSCMData A U)
    (posterior : FiniteProbRecord U) :
    RecursiveSCMData A U where
  n := M.n
  noise := posterior
  fn := M.fn

theorem unsetModel_setModel_cancel (M : RecursiveSCMData A U)
    (target : Fin M.n) (value : A) :
    unsetModel (setModel M target value) target (M.fn target) = M := by
  cases M with
  | mk n noise fn =>
      simp [unsetModel, setModel]
      funext i xs u
      by_cases h : i = target
      · simp [h]
      · simp [h]

theorem evalPrefix_mk_congr (k n : Nat) (hk : k ≤ n)
    (noise₁ noise₂ : FiniteProbRecord U)
    (fn₁ fn₂ : (i : Fin n) -> List A -> U -> A)
    (hfn : ∀ i xs u, fn₁ i xs u = fn₂ i xs u) (u : U) :
    ({ n := n, noise := noise₁, fn := fn₁ } : RecursiveSCMData A U).evalPrefix u k hk =
      ({ n := n, noise := noise₂, fn := fn₂ } : RecursiveSCMData A U).evalPrefix u k hk := by
  induction k with
  | zero =>
      rfl
  | succ n ih =>
      simp [RecursiveSCMData.evalPrefix, ih (Nat.le_of_succ_le hk), hfn]

theorem eval_mk_congr (n : Nat)
    (noise₁ noise₂ : FiniteProbRecord U)
    (fn₁ fn₂ : (i : Fin n) -> List A -> U -> A)
    (hfn : ∀ i xs u, fn₁ i xs u = fn₂ i xs u) (u : U) :
    ({ n := n, noise := noise₁, fn := fn₁ } : RecursiveSCMData A U).eval u =
      ({ n := n, noise := noise₂, fn := fn₂ } : RecursiveSCMData A U).eval u := by
  exact evalPrefix_mk_congr n n (Nat.le_refl n) noise₁ noise₂ fn₁ fn₂ hfn u

structure EpistemicRecord (A : Type u) (U : Type v) where
  model : RecursiveSCMData A U
  exoCount : Nat
  relations : List Relation
  wfRelations :
    ∀ edge, edge ∈ relations -> RelationBounded model.n exoCount edge

namespace EpistemicRecord

def WellFormed (R : EpistemicRecord A U) : Prop :=
  0 < R.model.noise.den ∧
    FiniteProbRecord.totalMass R.model.noise.atoms = R.model.noise.den ∧
    ∀ edge, edge ∈ R.relations -> RelationBounded R.model.n R.exoCount edge

theorem wellFormed (R : EpistemicRecord A U) : R.WellFormed :=
  ⟨R.model.noise.den_pos, R.model.noise.total_mass, R.wfRelations⟩

def learnFresh (R : EpistemicRecord A U) (fresh : List A -> U -> A) :
    EpistemicRecord A U where
  model := learnFreshModel R.model fresh
  exoCount := R.exoCount
  relations := R.relations
  wfRelations := by
    intro edge hmem
    exact (R.wfRelations edge hmem).endoSucc

theorem learnFresh_preserves_wellFormed (R : EpistemicRecord A U)
    (fresh : List A -> U -> A) :
    (R.learnFresh fresh).WellFormed :=
  (R.learnFresh fresh).wellFormed

def forgetLast (R : EpistemicRecord A U) (_hpos : 0 < R.model.n)
    (hRelations :
      ∀ edge, edge ∈ R.relations ->
        RelationBounded (R.model.n - 1) R.exoCount edge) :
    EpistemicRecord A U where
  model := forgetLastModel R.model _hpos
  exoCount := R.exoCount
  relations := R.relations
  wfRelations := hRelations

theorem forgetLast_preserves_wellFormed (R : EpistemicRecord A U)
    (hpos : 0 < R.model.n)
    (hRelations :
      ∀ edge, edge ∈ R.relations ->
        RelationBounded (R.model.n - 1) R.exoCount edge) :
    (R.forgetLast hpos hRelations).WellFormed :=
  (R.forgetLast hpos hRelations).wellFormed

theorem forgetLast_learnFresh_cancel (R : EpistemicRecord A U)
    (fresh : List A -> U -> A) :
    (R.learnFresh fresh).forgetLast (Nat.succ_pos R.model.n)
      (by
        intro edge hmem
        simpa [learnFreshModel] using R.wfRelations edge hmem) = R := by
  cases R
  simp [forgetLast, learnFresh, forgetLastModel_learnFresh_cancel]

def conditionNoise (R : EpistemicRecord A U)
    (posterior : FiniteProbRecord U) : EpistemicRecord A U where
  model := conditionNoiseModel R.model posterior
  exoCount := R.exoCount
  relations := R.relations
  wfRelations := R.wfRelations

theorem conditionNoise_preserves_wellFormed (R : EpistemicRecord A U)
    (posterior : FiniteProbRecord U) :
    (R.conditionNoise posterior).WellFormed :=
  (R.conditionNoise posterior).wellFormed

def conditionOnExogenousEvidence (R : EpistemicRecord A U)
    (evidence : U -> Bool) (hEvidence : 0 < R.model.noise.probRat evidence) :
    EpistemicRecord A U :=
  R.conditionNoise (R.model.noise.condition evidence hEvidence)

theorem conditionOnExogenousEvidence_preserves_wellFormed (R : EpistemicRecord A U)
    (evidence : U -> Bool) (hEvidence : 0 < R.model.noise.probRat evidence) :
    (R.conditionOnExogenousEvidence evidence hEvidence).WellFormed :=
  (R.conditionOnExogenousEvidence evidence hEvidence).wellFormed

theorem conditionOnExogenousEvidence_probRat (R : EpistemicRecord A U)
    (evidence event : U -> Bool) (hEvidence : 0 < R.model.noise.probRat evidence) :
    (R.conditionOnExogenousEvidence evidence hEvidence).model.noise.probRat event =
      R.model.noise.probRat (fun u => evidence u && event u) /
        R.model.noise.probRat evidence := by
  simp [conditionOnExogenousEvidence, conditionNoise, conditionNoiseModel,
    FiniteProbRecord.condition_probRat]

def conditionOnObservation (R : EpistemicRecord A U)
    (observation : List A -> Bool)
    (hEvidence : 0 < R.model.noise.probRat (fun u => observation (R.model.eval u))) :
    EpistemicRecord A U :=
  R.conditionOnExogenousEvidence (fun u => observation (R.model.eval u)) hEvidence

theorem conditionOnObservation_preserves_wellFormed (R : EpistemicRecord A U)
    (observation : List A -> Bool)
    (hEvidence : 0 < R.model.noise.probRat (fun u => observation (R.model.eval u))) :
    (R.conditionOnObservation observation hEvidence).WellFormed :=
  (R.conditionOnObservation observation hEvidence).wellFormed

def setVariable (R : EpistemicRecord A U) (target : Fin R.model.n) (value : A) :
    EpistemicRecord A U where
  model := setModel R.model target value
  exoCount := R.exoCount
  relations := R.relations
  wfRelations := R.wfRelations

theorem setVariable_preserves_wellFormed (R : EpistemicRecord A U)
    (target : Fin R.model.n) (value : A) :
    (R.setVariable target value).WellFormed :=
  (R.setVariable target value).wellFormed

def conditionOnObservationThenSet (R : EpistemicRecord A U)
    (observation : List A -> Bool)
    (hEvidence : 0 < R.model.noise.probRat (fun u => observation (R.model.eval u)))
    (target : Fin R.model.n) (value : A) : EpistemicRecord A U :=
  (R.conditionOnObservation observation hEvidence).setVariable
    ⟨target.val, by
      dsimp [conditionOnObservation, conditionOnExogenousEvidence, conditionNoise,
        conditionNoiseModel]
      exact target.isLt⟩
    value

theorem conditionOnObservationThenSet_preserves_wellFormed (R : EpistemicRecord A U)
    (observation : List A -> Bool)
    (hEvidence : 0 < R.model.noise.probRat (fun u => observation (R.model.eval u)))
    (target : Fin R.model.n) (value : A) :
    (R.conditionOnObservationThenSet observation hEvidence target value).WellFormed :=
  (R.conditionOnObservationThenSet observation hEvidence target value).wellFormed

def counterfactualAfterSetProb (R : EpistemicRecord A U)
    (observation : List A -> Bool)
    (hEvidence : 0 < R.model.noise.probRat (fun u => observation (R.model.eval u)))
    (target : Fin R.model.n) (value : A) (event : List A -> Bool) : Rat :=
  (R.conditionOnObservationThenSet observation hEvidence target value).model.observationalProb
    event

theorem counterfactualAfterSetProb_eq_counterfactualProb (R : EpistemicRecord A U)
    (observation : List A -> Bool)
    (hEvidence : 0 < R.model.noise.probRat (fun u => observation (R.model.eval u)))
    (target : Fin R.model.n) (value : A) (event : List A -> Bool) :
    R.counterfactualAfterSetProb observation hEvidence target value event =
      R.model.counterfactualProb observation
        (by
          simpa [RecursiveSCMData.observationalProb,
            RecursiveSCMData.observationalDist,
            FiniteProbRecord.map_probRat] using hEvidence)
        (fun i => if i = target then some value else none) event := by
  simp [counterfactualAfterSetProb, conditionOnObservationThenSet,
    conditionOnObservation, conditionOnExogenousEvidence, conditionNoise,
    conditionNoiseModel, setVariable, setModel, RecursiveSCMData.counterfactualProb,
    RecursiveSCMData.observationalProb, RecursiveSCMData.observationalDist,
    RecursiveSCMData.intervene, FiniteProbRecord.map_probRat]
  apply congrArg
    (fun ev =>
      (R.model.noise.condition
        (fun u => observation (R.model.eval u)) hEvidence).probRat ev)
  funext u
  exact congrArg event
    (eval_mk_congr R.model.n
      (R.model.noise.condition
        (fun u => observation (R.model.eval u)) hEvidence)
      R.model.noise
      (fun i xs u => if i = target then value else R.model.fn i xs u)
      (fun i xs u =>
        match if i = target then some value else none with
        | some x => x
        | none => R.model.fn i xs u)
      (by
        intro i xs u
        by_cases h : i = target <;> simp [h])
      u)

def unsetVariable (R : EpistemicRecord A U) (target : Fin R.model.n)
    (oldFn : List A -> U -> A) : EpistemicRecord A U where
  model := unsetModel R.model target oldFn
  exoCount := R.exoCount
  relations := R.relations
  wfRelations := R.wfRelations

theorem unsetVariable_preserves_wellFormed (R : EpistemicRecord A U)
    (target : Fin R.model.n) (oldFn : List A -> U -> A) :
    (R.unsetVariable target oldFn).WellFormed :=
  (R.unsetVariable target oldFn).wellFormed

theorem unset_set_cancel (R : EpistemicRecord A U)
    (target : Fin R.model.n) (value : A) :
    (R.setVariable target value).unsetVariable target (R.model.fn target) = R := by
  cases R
  simp [unsetVariable, setVariable, unsetModel_setModel_cancel]

def relate (R : EpistemicRecord A U) (edge : Relation)
    (hEdge : RelationBounded R.model.n R.exoCount edge) :
    EpistemicRecord A U :=
  { R with
    relations := edge :: R.relations
    wfRelations := by
      intro edge' hmem
      cases hmem with
      | head =>
          exact hEdge
      | tail _ htail =>
          exact R.wfRelations edge' htail }

theorem relate_preserves_wellFormed (R : EpistemicRecord A U)
    (edge : Relation) (hEdge : RelationBounded R.model.n R.exoCount edge) :
    (R.relate edge hEdge).WellFormed :=
  (R.relate edge hEdge).wellFormed

def unrelate (R : EpistemicRecord A U) (edge : Relation) : EpistemicRecord A U :=
  { R with
    relations := R.relations.erase edge
    wfRelations := by
      intro edge' hmem
      exact R.wfRelations edge' (List.mem_of_mem_erase hmem) }

theorem unrelate_preserves_wellFormed (R : EpistemicRecord A U)
    (edge : Relation) :
    (R.unrelate edge).WellFormed :=
  (R.unrelate edge).wellFormed

theorem unrelate_relate_cancel (R : EpistemicRecord A U)
    (edge : Relation) (hEdge : RelationBounded R.model.n R.exoCount edge) :
    (R.relate edge hEdge).unrelate edge = R := by
  cases R
  simp [unrelate, relate]

end EpistemicRecord

/-!
The operation constructs the target record; the transition label merely names
the admissible move.  `RecordStep` is the proof object connecting those two
layers, preventing a label from being attached to unrelated endpoints.
-/
inductive RecordStep :
    TransitionLabel -> EpistemicRecord A U -> EpistemicRecord A U -> Prop
  | learning (R : EpistemicRecord A U) (fresh : List A -> U -> A) :
      RecordStep .learning R (R.learnFresh fresh)
  | forgetting (R : EpistemicRecord A U) (hpos : 0 < R.model.n)
      (hRelations :
        forall edge, edge ∈ R.relations ->
          RelationBounded (R.model.n - 1) R.exoCount edge) :
      RecordStep .forgetting R (R.forgetLast hpos hRelations)
  | conditioning (R : EpistemicRecord A U) (posterior : FiniteProbRecord U) :
      RecordStep .conditioning R (R.conditionNoise posterior)
  | setting (R : EpistemicRecord A U) (target : Fin R.model.n) (value : A) :
      RecordStep .setting R (R.setVariable target value)
  | unsetting (R : EpistemicRecord A U) (target : Fin R.model.n)
      (oldFn : List A -> U -> A) :
      RecordStep .unsetting R (R.unsetVariable target oldFn)
  | relating (R : EpistemicRecord A U) (edge : Relation)
      (hEdge : RelationBounded R.model.n R.exoCount edge) :
      RecordStep .relating R (R.relate edge hEdge)
  | unrelating (R : EpistemicRecord A U) (edge : Relation) :
      RecordStep .unrelating R (R.unrelate edge)

structure EpistemicMode (A : Type u) (U : Type v) where
  name : String
  record : EpistemicRecord A U

namespace EpistemicMode

def WellFormed (m : EpistemicMode A U) : Prop :=
  m.record.WellFormed

theorem wellFormed (m : EpistemicMode A U) : m.WellFormed :=
  m.record.wellFormed

end EpistemicMode

structure ModalTransition (A : Type u) (U : Type v) where
  label : TransitionLabel
  source : EpistemicMode A U
  target : EpistemicMode A U
  valid : RecordStep label source.record target.record

namespace ModalTransition

theorem source_wellFormed (τ : ModalTransition A U) : τ.source.WellFormed :=
  τ.source.wellFormed

theorem target_wellFormed (τ : ModalTransition A U) : τ.target.WellFormed :=
  τ.target.wellFormed

end ModalTransition

def learning (sourceName targetName : String) (R : EpistemicRecord A U)
    (fresh : List A -> U -> A) : ModalTransition A U where
  label := TransitionLabel.learning
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.learnFresh fresh }
  valid := RecordStep.learning R fresh

def forgetting (sourceName targetName : String) (R : EpistemicRecord A U)
    (hpos : 0 < R.model.n)
    (hRelations :
      ∀ edge, edge ∈ R.relations ->
        RelationBounded (R.model.n - 1) R.exoCount edge) :
    ModalTransition A U where
  label := TransitionLabel.forgetting
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.forgetLast hpos hRelations }
  valid := RecordStep.forgetting R hpos hRelations

def conditioning (sourceName targetName : String) (R : EpistemicRecord A U)
    (posterior : FiniteProbRecord U) :
    ModalTransition A U where
  label := TransitionLabel.conditioning
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.conditionNoise posterior }
  valid := RecordStep.conditioning R posterior

def conditioningOnExogenousEvidence (sourceName targetName : String)
    (R : EpistemicRecord A U) (evidence : U -> Bool)
    (hEvidence : 0 < R.model.noise.probRat evidence) :
    ModalTransition A U where
  label := TransitionLabel.conditioning
  source := { name := sourceName, record := R }
  target :=
    { name := targetName
      record := R.conditionOnExogenousEvidence evidence hEvidence }
  valid := by
    exact RecordStep.conditioning R
      (R.model.noise.condition evidence hEvidence)

def conditioningOnObservation (sourceName targetName : String)
    (R : EpistemicRecord A U) (observation : List A -> Bool)
    (hEvidence : 0 < R.model.noise.probRat (fun u => observation (R.model.eval u))) :
    ModalTransition A U where
  label := TransitionLabel.conditioning
  source := { name := sourceName, record := R }
  target :=
    { name := targetName
      record := R.conditionOnObservation observation hEvidence }
  valid := by
    exact RecordStep.conditioning R
      (R.model.noise.condition
        (fun u => observation (R.model.eval u)) hEvidence)

def setting (sourceName targetName : String) (R : EpistemicRecord A U)
    (target : Fin R.model.n) (value : A) : ModalTransition A U where
  label := TransitionLabel.setting
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.setVariable target value }
  valid := RecordStep.setting R target value

def unsetting (sourceName targetName : String) (R : EpistemicRecord A U)
    (target : Fin R.model.n) (oldFn : List A -> U -> A) :
    ModalTransition A U where
  label := TransitionLabel.unsetting
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.unsetVariable target oldFn }
  valid := RecordStep.unsetting R target oldFn

def relating (sourceName targetName : String) (R : EpistemicRecord A U)
    (edge : Relation) (hEdge : RelationBounded R.model.n R.exoCount edge) :
    ModalTransition A U where
  label := TransitionLabel.relating
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.relate edge hEdge }
  valid := RecordStep.relating R edge hEdge

def unrelating (sourceName targetName : String) (R : EpistemicRecord A U)
    (edge : Relation) : ModalTransition A U where
  label := TransitionLabel.unrelating
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.unrelate edge }
  valid := RecordStep.unrelating R edge

namespace TenureTrackCounterfactual

def record : EpistemicRecord Bool Thesis.TenureTrack.Noise where
  model := Thesis.TenureTrack.model
  exoCount := 6
  relations := []
  wfRelations := by
    intro edge hmem
    cases hmem

def prIndex : Fin record.model.n :=
  ⟨0, by native_decide⟩

def fitIndex : Fin record.model.n :=
  ⟨4, by native_decide⟩

theorem evidence_positive :
    0 < record.model.noise.probRat
      (fun u => Thesis.TenureTrack.noPrestigeGoodNoOfferEvent (record.model.eval u)) := by
  native_decide

theorem modal_counterfactual_offer_do_pr_given_noPrestigeGoodNoOffer :
    record.counterfactualAfterSetProb Thesis.TenureTrack.noPrestigeGoodNoOfferEvent
      evidence_positive prIndex true Thesis.TenureTrack.offEvent =
      (1 / 2 : Rat) := by
  native_decide

theorem modal_counterfactual_offer_do_fit_given_noPrestigeGoodNoOffer :
    record.counterfactualAfterSetProb Thesis.TenureTrack.noPrestigeGoodNoOfferEvent
      evidence_positive fitIndex true Thesis.TenureTrack.offEvent =
      (1 / 2 : Rat) := by
  native_decide

end TenureTrackCounterfactual

end Modalities
end Thesis
