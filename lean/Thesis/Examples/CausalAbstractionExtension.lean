import Thesis.Examples.CausalAbstraction

namespace Thesis.Examples.CausalAbstraction
open Probability Causality

/-!
The AND/copy class has six macro surgeries: leave the merged cause alone
or force it true, independently leaving Y alone or forcing either Boolean.
Every forced cluster value in this class has one preimage. AND=false is
excluded, rather than assigned one of its three possible cause pairs.
-/

def coarseAction (cause response : Option Bool) : HardIntervention macroSignature where
  value node := if node.val = 0 then cause else response

def fineAction (first second response : Option Bool) : HardIntervention microSignature where
  value node := if node.val = 0 then first else if node.val = 1 then second else response

def coarseState (cause response : Bool) : macroSignature.Assignment :=
  fun node => if node.val = 0 then cause else response

def fineState (first second response : Bool) : microSignature.Assignment :=
  fun node => if node.val = 0 then first else if node.val = 1 then second else response

theorem coarseAction_eta (action : HardIntervention macroSignature) :
    action = coarseAction (action.value (0 : Fin 2)) (action.value (1 : Fin 2)) := by
  apply HardIntervention.extensional
  intro node
  have bound : node.val < 2 := node.isLt
  have casesNode : node = (0 : Fin 2) ∨ node = (1 : Fin 2) := by
    by_cases zero : node.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by change node.val = 1; omega))
  rcases casesNode with rfl | rfl <;> rfl

theorem fineAction_eta (action : HardIntervention microSignature) :
    action = fineAction (action.value (0 : Fin 3)) (action.value (1 : Fin 3))
      (action.value (2 : Fin 3)) := by
  apply HardIntervention.extensional
  intro node
  have bound : node.val < 3 := node.isLt
  have casesNode : node = (0 : Fin 3) ∨ node = (1 : Fin 3) ∨ node = (2 : Fin 3) := by
    by_cases zero : node.val = 0
    · exact Or.inl (Fin.ext zero)
    · by_cases one : node.val = 1
      · exact Or.inr (Or.inl (Fin.ext one))
      · exact Or.inr (Or.inr (Fin.ext (by change node.val = 2; omega)))
  rcases casesNode with rfl | rfl | rfl <;> rfl

theorem coarseState_eta (state : macroSignature.Assignment) :
    state = coarseState (state (0 : Fin 2)) (state (1 : Fin 2)) := by
  funext node
  have bound : node.val < 2 := node.isLt
  by_cases zero : node.val = 0
  · have equal : node = (0 : Fin 2) := Fin.ext zero
    subst node; rfl
  · have equal : node = (1 : Fin 2) := Fin.ext (by change node.val = 1; omega)
    subst node; rfl

theorem fineState_eta (state : microSignature.Assignment) :
    state = fineState (state (0 : Fin 3)) (state (1 : Fin 3)) (state (2 : Fin 3)) := by
  funext node
  have bound : node.val < 3 := node.isLt
  by_cases zero : node.val = 0
  · have equal : node = (0 : Fin 3) := Fin.ext zero
    subst node; rfl
  · by_cases one : node.val = 1
    · have equal : node = (1 : Fin 3) := Fin.ext one
      subst node; rfl
    · have equal : node = (2 : Fin 3) := Fin.ext (by change node.val = 2; omega)
      subst node; rfl

/-- Defined exactly on unforced cause pairs and on the unique AND=true
pair, with arbitrary response surgery. Partial/mismatched pairs are excluded. -/
def andOmega (intervention : HardIntervention microSignature) : Option (HardIntervention macroSignature) :=
  match intervention.value (0 : Fin 3), intervention.value (1 : Fin 3) with
  | none, none => some (coarseAction none (intervention.value (2 : Fin 3)))
  | some true, some true => some (coarseAction (some true) (intervention.value (2 : Fin 3)))
  | _, _ => none

private theorem andOmega_respects_finite : ∀ first second response a b y,
    ∀ action, andOmega (fineAction first second response) = some action →
    (fineAction first second response).RealizedBy (fineState a b y) →
      action.RealizedBy (mergeAssignment Bool.and (fineState a b y)) := by
  intro first second response a b y action defined realizes
  cases first with
  | none =>
    cases second with
    | none =>
      cases Option.some.inj defined
      exact fun node value forced => by
        have bound : node.val < 2 := node.isLt
        by_cases zero : node.val = 0
        · simp [coarseAction, zero] at forced
        · have equal : node = (1 : Fin 2) := Fin.ext (by change node.val = 1; omega)
          subst node
          exact realizes (2 : Fin 3) value forced
    | some b => cases b <;> cases defined
  | some a =>
    cases a with
    | false => cases second <;> cases defined
    | true =>
      cases second with
      | none => cases defined
      | some b =>
        cases b with
        | false => cases defined
        | true =>
          cases Option.some.inj defined
          intro node value forced
          by_cases zero : node.val = 0
          · have equal : node = (0 : Fin 2) := Fin.ext zero
            subst node
            have val : true = value := Option.some.inj forced
            rw [← val]
            change (a && b) = true
            have left : a = true := realizes (0 : Fin 3) true rfl
            have right : b = true := realizes (1 : Fin 3) true rfl
            rw [left, right]
            rfl
          · have bound : node.val < 2 := node.isLt
            have equal : node = (1 : Fin 2) := Fin.ext (by change node.val = 1; omega)
            subst node
            exact realizes (2 : Fin 3) value forced

def andInterventionMap : CausalInterventionMap microSignature macroSignature where
  microModel := microModel
  macroModel := andMacro
  assignmentMap := mergeAssignment Bool.and
  omega := andOmega
  respects := by
    intro intervention action defined assignment realizes
    have interventionEq := fineAction_eta intervention
    have assignmentEq := fineState_eta assignment
    rw [interventionEq] at defined realizes
    rw [assignmentEq] at realizes ⊢
    exact andOmega_respects_finite _ _ _ _ _ _ action defined realizes

/-- The six allowed macro surgeries, including no forced cause. -/
def uniqueAdmissible (action : HardIntervention macroSignature) : Prop :=
  action.value (0 : Fin 2) ≠ some false

def andRepresentative (action : HardIntervention macroSignature) : HardIntervention microSignature :=
  fineAction (action.value (0 : Fin 2)) (action.value (0 : Fin 2)) (action.value (1 : Fin 2))

theorem and_omega_section : andInterventionMap.IsSection uniqueAdmissible (fun action _ => andRepresentative action) := by
  intro action admitted
  have canonical := coarseAction_eta action
  unfold uniqueAdmissible at admitted
  change andOmega (andRepresentative action) = some action
  rw [canonical]
  cases cause : action.value (0 : Fin 2) with
  | none => rfl
  | some value =>
    cases value with
    | false => exact False.elim (admitted cause)
    | true => rfl

private theorem and_cells : ∀ (cause response : Option Bool) (x y : Bool),
    cause ≠ some false →
    QProb.Equiv
      ((andMacro.interventionalDist (coarseAction cause response).value).probVal
        (FiniteProbRecord.singletonEvent (coarseState x y)))
      (((microModel.interventionalDist (fineAction cause cause response).value).map (mergeAssignment Bool.and)).probVal
        (FiniteProbRecord.singletonEvent (coarseState x y))) := by
  intro cause
  cases cause with
  | none =>
    intro response
    cases response with
    | none => decide +kernel
    | some value => cases value <;> decide +kernel
  | some value =>
    cases value with
    | false => intro _ _ _ impossible; exact False.elim (impossible rfl)
    | true =>
      intro response
      cases response with
      | none => decide +kernel
      | some value => cases value <;> decide +kernel

/-- Full-law preservation uniformly over the whole six-intervention class,
including both forced response values and leaving the response unforced. -/
theorem and_preservesAt_all (action : HardIntervention macroSignature) (admitted : uniqueAdmissible action) :
    ∀ event, QProb.Equiv
      (andMacro.interventionalValue action.value event)
      (((microModel.interventionalDist (andRepresentative action).value).map (mergeAssignment Bool.and)).probVal event) := by
  intro event
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _
    macroSignature.assignmentEnumeration macroSignature.assignmentEnumeration_nodup
    macroSignature.assignmentEnumeration_complete
  intro state
  have canonical := coarseAction_eta action
  have stateEq := coarseState_eta state
  rw [canonical, stateEq]
  exact and_cells _ _ _ _ admitted


private theorem andOmega_fibre_finite (first second response : Option Bool)
    (action : HardIntervention macroSignature)
    (defined : andOmega (fineAction first second response) = some action) :
    uniqueAdmissible action ∧ fineAction first second response = andRepresentative action := by
  cases first with
  | none =>
    cases second with
    | none => cases Option.some.inj defined; exact ⟨(by intro impossible; cases impossible), rfl⟩
    | some value => cases value <;> cases defined
  | some value =>
    cases value with
    | false => cases second <;> cases defined
    | true =>
      cases second with
      | none => cases defined
      | some value =>
        cases value with
        | false => cases defined
        | true => cases Option.some.inj defined; exact ⟨(by intro impossible; cases impossible), rfl⟩

/-- Every allowed micro surgery is the unique cluster lift of its macro
surgery. Thus the equality theorem below covers the whole ω domain. -/
theorem andOmega_fibre (intervention action) (defined : andOmega intervention = some action) :
    uniqueAdmissible action ∧ intervention = andRepresentative action := by
  have canonical := fineAction_eta intervention
  rw [canonical] at defined ⊢
  exact andOmega_fibre_finite _ _ _ _ defined

theorem and_intervention_exact : andInterventionMap.Exact := by
  intro intervention action defined event
  have fibre := andOmega_fibre intervention action defined
  have fullLaw := and_preservesAt_all action fibre.1 event
  rw [← fibre.2] at fullLaw
  exact QProb.equiv_trans fullLaw (FiniteProbRecord.map_probVal _ _ _)

def andFullCoarsening : FiniteCausalCoarseGraining microSignature macroSignature where
  microModel := microModel
  macroModel := andMacro
  cluster := clusters
  cluster_nonempty := andCoarsening.cluster_nonempty
  cluster_disjoint := andCoarsening.cluster_disjoint
  assignmentMap := mergeAssignment Bool.and
  coordinate_local := andCoarsening.coordinate_local
  admissible := uniqueAdmissible
  representative action _ := andRepresentative action
  representative_respects action admitted :=
    andInterventionMap.respects _ _ (and_omega_section action admitted)

theorem and_full_preservesAt (action) (admitted : andFullCoarsening.admissible action) :
    andFullCoarsening.PreservesAt action admitted :=
  andFullCoarsening.preservesAt_of_section andInterventionMap rfl rfl rfl
    and_omega_section and_intervention_exact action admitted

/-- Every forced value has a unique preimage on its own cluster. The
unforced cause has no preimage obligation; the response cluster is singleton. -/
theorem and_unique_preimage_class (action) (admitted : uniqueAdmissible action)
    (node : Fin 2) (value : Bool) (forced : action.value node = some value)
    (left right : microSignature.Assignment)
    (leftValue : mergeAssignment Bool.and left node = value)
    (rightValue : mergeAssignment Bool.and right node = value) :
    ∀ member, clusters node member = true → left member = right member := by
  by_cases root : node.val = 0
  · have nodeEq : node = (0 : Fin 2) := Fin.ext root
    subst node
    have isTrue : value = true := by
      cases value with
      | false => exact False.elim (admitted forced)
      | true => rfl
    rw [isTrue] at leftValue rightValue
    have l := Bool.and_eq_true_iff.mp leftValue
    have r := Bool.and_eq_true_iff.mp rightValue
    intro member included
    have atCause : member.val < 2 := of_decide_eq_true included
    have casesMember : member = (0 : Fin 3) ∨ member = (1 : Fin 3) := by
      by_cases zero : member.val = 0
      · exact Or.inl (Fin.ext zero)
      · exact Or.inr (Fin.ext (by change member.val = 1; omega))
    rcases casesMember with rfl | rfl
    · exact l.1.trans r.1.symm
    · exact l.2.trans r.2.symm
  · have bound : node.val < 2 := node.isLt
    have nodeEq : node = (1 : Fin 2) := Fin.ext (by change node.val = 1; omega)
    subst node
    intro member included
    have atResponse : member.val = 2 := of_decide_eq_true included
    have memberEq : member = (2 : Fin 3) := Fin.ext atResponse
    subst member
    exact leftValue.trans rightValue.symm

/-- The declared class is exactly the unique-forced-cluster class, not
an arbitrarily smaller selection of interventions with that property. -/
theorem and_unique_class_iff (action : HardIntervention macroSignature) :
    uniqueAdmissible action ↔
      ∀ (node : Fin 2) (value : Bool), action.value node = some value →
      ∀ left right : microSignature.Assignment,
      mergeAssignment Bool.and left node = value →
      mergeAssignment Bool.and right node = value →
      ∀ member, clusters node member = true → left member = right member := by
  constructor
  · exact and_unique_preimage_class action
  · intro unique notAdmitted
    have impossible := unique (0 : Fin 2) false notAdmitted
      (fineState false false false) (fineState false true false) rfl rfl
      (1 : Fin 3) (by decide +kernel)
    cases impossible

/-- Rejection is explicit: a false merged cause is never in the image of ω. -/
theorem and_false_not_defined (intervention : HardIntervention microSignature) (response : Option Bool) :
    andOmega intervention ≠ some (coarseAction (some false) response) := by
  intro defined
  exact (andOmega_fibre intervention _ defined).1 rfl

/-- Construction input consists of a literal AND child mechanism and its
interchangeability proof. No symmetry is inferred from an observed table. -/
structure InterchangeableAndParents where
  operation : Bool → Bool → Bool
  child_is_and : ∀ first second, operation first second = (first && second)
  mechanism_agrees : ∀ first second inputs,
    microModel.mechanism (2 : Fin 3) (responseParents first second) inputs = operation first second
  swap : ∀ first second, operation first second = operation second first

/-- Build τ from the supplied child operation on the two-parent cluster. -/
def InterchangeableAndParents.merge (parents : InterchangeableAndParents) :
    FiniteCausalCoarseGraining microSignature macroSignature :=
  { andFullCoarsening with
    assignmentMap := mergeAssignment parents.operation
    coordinate_local := by
      have operationEq : parents.operation = Bool.and := by funext a b; exact parents.child_is_and a b
      rw [operationEq]
      exact andFullCoarsening.coordinate_local
    representative_respects := by
      have operationEq : parents.operation = Bool.and := by funext a b; exact parents.child_is_and a b
      rw [operationEq]
      exact andFullCoarsening.representative_respects }

theorem InterchangeableAndParents.merge_swap (parents : InterchangeableAndParents) (first second response : Bool) :
    parents.merge.assignmentMap (fineState first second response) =
      parents.merge.assignmentMap (fineState second first response) := by
  funext node
  change (if node.val = 0 then parents.operation first second else response) =
    (if node.val = 0 then parents.operation second first else response)
  rw [parents.swap first second]

theorem InterchangeableAndParents.merge_preservesAt (parents : InterchangeableAndParents)
    (action) (admitted : parents.merge.admissible action) : parents.merge.PreservesAt action admitted := by
  have operationEq : parents.operation = Bool.and := by funext a b; exact parents.child_is_and a b
  change ∀ event, _
  simp only [InterchangeableAndParents.merge, operationEq]
  exact and_full_preservesAt action admitted

def checkedAndParents : InterchangeableAndParents where
  operation := Bool.and
  child_is_and _ _ := rfl
  mechanism_agrees _ _ _ := rfl
  swap := Bool.and_comm

theorem swap_constructs_existing_merge : checkedAndParents.merge = andFullCoarsening := rfl

end Thesis.Examples.CausalAbstraction
