import Thesis.SCM

namespace Thesis
namespace Modalities

/-!
A small finite transition layer for the thesis' epistemic modalities.

This is not a formalization of Gratzer's modal type theory.  The mode theory is
represented only by fixed transition labels.  The actual context/SCM changes
are explicit finite record transformations on source and target modes.
-/

inductive TransitionLabel where
  | learning
  | forgetting
  | relating
  | unrelating
  | setting
  | unsetting
  deriving DecidableEq, Repr

abbrev Relation := Nat × Nat

def RelationBounded (n : Nat) (edge : Relation) : Prop :=
  edge.1 < n ∧ edge.2 < n

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

structure EpistemicRecord (A : Type u) (U : Type v) where
  model : RecursiveSCMData A U
  wfNoise : model.noise.IsProbability
  relations : List Relation
  wfRelations : ∀ edge, edge ∈ relations -> RelationBounded model.n edge

namespace EpistemicRecord

def WellFormed (R : EpistemicRecord A U) : Prop :=
  R.model.noise.IsProbability ∧
    ∀ edge, edge ∈ R.relations -> RelationBounded R.model.n edge

theorem wellFormed (R : EpistemicRecord A U) : R.WellFormed :=
  ⟨R.wfNoise, R.wfRelations⟩

def learnFresh (R : EpistemicRecord A U) (fresh : List A -> U -> A) :
    EpistemicRecord A U where
  model := learnFreshModel R.model fresh
  wfNoise := R.wfNoise
  relations := R.relations
  wfRelations := by
    intro edge hmem
    have h := R.wfRelations edge hmem
    exact ⟨Nat.lt_trans h.1 (Nat.lt_succ_self R.model.n),
      Nat.lt_trans h.2 (Nat.lt_succ_self R.model.n)⟩

theorem learnFresh_preserves_wellFormed (R : EpistemicRecord A U)
    (fresh : List A -> U -> A) :
    (R.learnFresh fresh).WellFormed :=
  (R.learnFresh fresh).wellFormed

def forgetLast (R : EpistemicRecord A U) (_hpos : 0 < R.model.n)
    (hRelations :
      ∀ edge, edge ∈ R.relations -> RelationBounded (R.model.n - 1) edge) :
    EpistemicRecord A U where
  model := forgetLastModel R.model _hpos
  wfNoise := R.wfNoise
  relations := R.relations
  wfRelations := hRelations

theorem forgetLast_preserves_wellFormed (R : EpistemicRecord A U)
    (hpos : 0 < R.model.n)
    (hRelations :
      ∀ edge, edge ∈ R.relations -> RelationBounded (R.model.n - 1) edge) :
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

def setVariable (R : EpistemicRecord A U) (target : Fin R.model.n) (value : A) :
    EpistemicRecord A U where
  model := setModel R.model target value
  wfNoise := R.wfNoise
  relations := R.relations
  wfRelations := R.wfRelations

theorem setVariable_preserves_wellFormed (R : EpistemicRecord A U)
    (target : Fin R.model.n) (value : A) :
    (R.setVariable target value).WellFormed :=
  (R.setVariable target value).wellFormed

def unsetVariable (R : EpistemicRecord A U) (target : Fin R.model.n)
    (oldFn : List A -> U -> A) : EpistemicRecord A U where
  model := unsetModel R.model target oldFn
  wfNoise := R.wfNoise
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
    (hEdge : RelationBounded R.model.n edge) : EpistemicRecord A U :=
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
    (edge : Relation) (hEdge : RelationBounded R.model.n edge) :
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
    (edge : Relation) (hEdge : RelationBounded R.model.n edge) :
    (R.relate edge hEdge).unrelate edge = R := by
  cases R
  simp [unrelate, relate]

end EpistemicRecord

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

def forgetting (sourceName targetName : String) (R : EpistemicRecord A U)
    (hpos : 0 < R.model.n)
    (hRelations :
      ∀ edge, edge ∈ R.relations -> RelationBounded (R.model.n - 1) edge) :
    ModalTransition A U where
  label := TransitionLabel.forgetting
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.forgetLast hpos hRelations }

def setting (sourceName targetName : String) (R : EpistemicRecord A U)
    (target : Fin R.model.n) (value : A) : ModalTransition A U where
  label := TransitionLabel.setting
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.setVariable target value }

def unsetting (sourceName targetName : String) (R : EpistemicRecord A U)
    (target : Fin R.model.n) (oldFn : List A -> U -> A) :
    ModalTransition A U where
  label := TransitionLabel.unsetting
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.unsetVariable target oldFn }

def relating (sourceName targetName : String) (R : EpistemicRecord A U)
    (edge : Relation) (hEdge : RelationBounded R.model.n edge) :
    ModalTransition A U where
  label := TransitionLabel.relating
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.relate edge hEdge }

def unrelating (sourceName targetName : String) (R : EpistemicRecord A U)
    (edge : Relation) : ModalTransition A U where
  label := TransitionLabel.unrelating
  source := { name := sourceName, record := R }
  target := { name := targetName, record := R.unrelate edge }

end Modalities
end Thesis
