import Thesis.CausalTransport.CausalAbstractionInverseConditional
import Thesis.Causality.BinaryBowModel
import Thesis.Examples.CausalAbstractionSynthesis

/-!
# What an exact AND collapse reveals about its two causes

Keep just the two Boolean roots of the AND fixture. A measured AND success
probability of one quarter fixes the joint event that both roots are true.
Each individual root has a range from one quarter to one: the unused
coarse mass can be assigned to either value of that root. The solver must
produce both endpoints as actual fine models. Forcing both roots to true
can never give a coarse false value, even with arbitrary shared noise.
-/

namespace Thesis.Examples.CausalAbstractionInverse

open Probability Causality
open Causality.CausalAbstractionSynthesis (Aggregation interventionDecidableEq)
open Causality.CausalAbstractionInverse
open Thesis.Examples.CausalAbstractionSynthesis (compactSignature compactDoTrue)

def fine : ObservedSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed _ _ := false
  directed_earlier := by intro _ _ edge; cases edge

def bothTrue (state : fine.Assignment) : Bool := state (0 : Fin 2) && state (1 : Fin 2)

def andAggregation : Aggregation fine compactSignature where
  cluster _ _ := true
  cluster_nonempty _ := ⟨(0 : Fin 2), rfl⟩
  cluster_disjoint first second different := by
    have same : first = second := Fin.ext (by
      have left : first.val < 1 := first.isLt
      have right : second.val < 1 := second.isLt
      omega)
    exact False.elim (different same)
  assignmentMap state _ := bothTrue state
  coordinate_local _ first second agree := by
    unfold bothTrue
    rw [agree (0 : Fin 2) rfl, agree (1 : Fin 2) rfl]

def bothForced : HardIntervention fine where
  value _ := some true

def andOmega (action : HardIntervention fine) : Option (HardIntervention compactSignature) :=
  if action = .empty fine then some (.empty compactSignature)
  else if action = bothForced then some compactDoTrue
  else none

def observed : FiniteProbRecord compactSignature.Assignment where
  atoms := [(fun _ => false, 3), (fun _ => true, 1)]
  den := 4
  den_pos := by decide
  total_mass := rfl

def deterministic (value : Bool) : FiniteProbRecord compactSignature.Assignment where
  atoms := [(fun _ => value, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

def spec : Specification fine compactSignature where
  aggregation := andAggregation
  omega := andOmega
  required := [.empty compactSignature, compactDoTrue]
  measurements := [⟨.empty compactSignature, observed⟩, ⟨compactDoTrue, deterministic true⟩]

theorem protocol_valid : spec.Valid := by decide +kernel

/-- The model-independent point answer for the event represented directly
by the macro outcome retains the exact observational value. -/
def pointAnswer : Bool :=
  match spec.solve (.empty fine) bothTrue with
  | .point _ sharp _ => decide (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩)
  | _ => false

theorem point_answer_executes : pointAnswer = true := by decide +kernel

/-- Projecting to AND leaves both attaining fine models accessible through
the interval branch of the actual solver. -/
def rootRange : Bool :=
  match spec.solve (.empty fine) (fun state => state (0 : Fin 2)) with
  | .interval _ sharp _ => decide
      (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩ ∧ SignedRatio.Equiv sharp.upper .one)
  | _ => false

theorem root_range_executes : rootRange = true := by decide +kernel

def conflicting : Specification fine compactSignature :=
  { spec with measurements := [⟨.empty compactSignature, observed⟩,
      ⟨compactDoTrue, deterministic false⟩] }

def incompatibleAnswer : Bool :=
  match conflicting.solve (.empty fine) bothTrue with
  | .incompatible _ _ => true
  | _ => false

theorem incompatible_measurement_refuted : incompatibleAnswer = true := by decide +kernel

def missingObservation : Specification fine compactSignature :=
  { spec with measurements := [⟨compactDoTrue, deterministic true⟩] }

theorem missing_measurement_rejected :
    (match missingObservation.solve (.empty fine) bothTrue with
    | .invalid _ => true
    | _ => false) = true := by decide +kernel

/-! ## Conditional answers retain mixed support -/

def firstFalse : EventQuery fine :=
  .intervention (.empty fine) (fun state => !(state (0 : Fin 2)))

def observedBothTrue : EventQuery fine :=
  .intervention (.empty fine) bothTrue

/-- The fine evidence X=false may be unavailable. When it is supported,
the conjunction X=true and Y=true has zero conditional probability. -/
def mixedSupportZero : Bool :=
  match spec.solveConditional firstFalse observedBothTrue with
  | .supported _ sharp (.possible ..) => decide
      ((sharp.lower.value observedBothTrue).num = 0 ∧ (sharp.upper.value observedBothTrue).num = 0)
  | _ => false

theorem mixed_support_keeps_defined_zero : mixedSupportZero = true := by decide +kernel

def impossibleEvidence : EventQuery fine :=
  .intervention bothForced (fun state => !bothTrue state)

theorem impossible_evidence_is_undefined :
    (match spec.solveConditional impossibleEvidence observedBothTrue with
    | .undefined .. => true
    | _ => false) = true := by decide +kernel

/-! ## One-world laws leave cross-world effects open -/

open BinaryBow (signature x y)

/-- Only Y is retained. Both settings of the excluded root are measured,
and each gives the same coarse law as observation in this fixture. -/
def outcomeAggregation : Aggregation signature compactSignature where
  cluster _ := NodeSet.singleton y
  cluster_nonempty _ := ⟨y, (NodeSet.singleton_eq_true_iff y y).mpr rfl⟩
  cluster_disjoint first second different := by
    have left : first.val < 1 := first.isLt
    have right : second.val < 1 := second.isLt
    exact False.elim (different (Fin.ext (by omega)))
  assignmentMap state _ := state y
  coordinate_local _ first second agree := agree y ((NodeSet.singleton_eq_true_iff y y).mpr rfl)

def setTreatment (value : Bool) : HardIntervention signature :=
  (HardIntervention.empty signature).set x value

def outcomeProtocol (action : HardIntervention signature) :
    Option (HardIntervention compactSignature) :=
  if action = .empty signature ∨ action = setTreatment false ∨ action = setTreatment true then
    some (.empty compactSignature)
  else none

def fairOutcome : FiniteProbRecord compactSignature.Assignment where
  atoms := [(fun _ => false, 1), (fun _ => true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def fairWorlds : Specification signature compactSignature where
  aggregation := outcomeAggregation
  omega := outcomeProtocol
  required := [.empty compactSignature]
  measurements := [⟨.empty compactSignature, fairOutcome⟩]

def outcomeWorld (setting : Bool) : CounterfactualEvent signature :=
  .atom ⟨(setTreatment setting).value, y, true⟩

/-- Evaluate both potential outcomes for the same fine unit. -/
def changesOutcome : EventQuery signature :=
  .counterfactual (.disj (.conj (outcomeWorld false) (.neg (outcomeWorld true)))
    (.conj (.neg (outcomeWorld false)) (outcomeWorld true)))

/-- One shared source contains two independent fair bits. One controls X;
the other is the baseline value of Y. -/
def fairBits : FiniteProbRecord signature.Assignment where
  atoms := signature.assignmentEnumeration.map (fun state => (state, 1))
  den := 4
  den_pos := by decide
  total_mass := rfl

/-- Either keep the fair Y bit in every world or complement it when the
treatment is true. The same source bit is used in both worlds. -/
def pairedModel (flip : Bool) : ExactModel signature :=
  { BinaryBow.model fairBits false with
    mechanism := fun child parents inputs =>
      let source := inputs BinaryBow.root rfl
      if atX : child.val = 0 then source x
      else
        have childY : child.val = 1 := by
          have size : child.val < 2 := child.isLt
          omega
        Bool.xor (source y) (flip && parents x (by simp [signature, x, childY])) }

private theorem pairedSingletons :
    ∀ action ∈ CausalAbstractionSynthesis.interventions signature,
      ∀ reference ∈ signature.assignmentEnumeration,
        QProb.Equiv ((pairedModel false).interventionalDist action.value
          |>.probVal (FiniteProbRecord.singletonEvent reference))
          ((pairedModel true).interventionalDist action.value
          |>.probVal (FiniteProbRecord.singletonEvent reference)) := by
  decide +kernel

theorem same_single_world_laws (action : HardIntervention signature)
    (event : Event signature.Assignment) :
    QProb.Equiv ((pairedModel false).interventionalValue action.value event)
      ((pairedModel true).interventionalValue action.value event) :=
  FiniteProbRecord.probVal_extensional_of_singletons _ _ signature.assignmentEnumeration
    signature.assignmentEnumeration_nodup signature.assignmentEnumeration_complete
    (fun reference => pairedSingletons action
      (CausalAbstractionSynthesis.interventions_complete signature action)
      reference (signature.assignmentEnumeration_complete reference)) event

private theorem pairedCoarseCells (flip : Bool) :
    ∀ pair ∈ fairWorlds.comparisons, ∀ reference ∈ compactSignature.assignmentEnumeration,
      QProb.Equiv (((pairedModel flip).interventionalDist pair.1.value).map
        outcomeAggregation.assignmentMap |>.probVal (FiniteProbRecord.singletonEvent reference))
        (pair.2.law.probVal (FiniteProbRecord.singletonEvent reference)) := by
  cases flip <;> decide +kernel

theorem paired_fits (flip : Bool) : fairWorlds.Fits (pairedModel flip) := by
  intro pair listed event
  let pushed := ((pairedModel flip).interventionalDist pair.1.value).map
    outcomeAggregation.assignmentMap
  exact QProb.equiv_trans (QProb.equiv_symm (FiniteProbRecord.map_probVal _ _ _))
    (FiniteProbRecord.probVal_extensional_of_singletons pushed pair.2.law
      compactSignature.assignmentEnumeration compactSignature.assignmentEnumeration_nodup
      compactSignature.assignmentEnumeration_complete (fun reference =>
        pairedCoarseCells flip pair listed reference
          (compactSignature.assignmentEnumeration_complete reference)) event)

theorem counterfactual_witnesses :
    QProb.Equiv (changesOutcome.value (pairedModel false)) QProb.zero ∧
    QProb.Equiv (changesOutcome.value (pairedModel true)) QProb.one := by
  decide +kernel

/-- The certified solver must report a range. This uses the two concrete
witnesses and checks the solver's semantic contract without reducing the
larger elimination trace inside the kernel. -/
theorem cross_world_range :
    (match fairWorlds.solveQuery changesOutcome with
    | .interval .. => True
    | _ => False) := by
  cases fairWorlds.solveQuery changesOutcome with
  | invalid invalid => exact invalid (by decide +kernel)
  | incompatible _ excluded => exact excluded ⟨pairedModel false, paired_fits false⟩
  | point _ sharp same =>
    have left := sharp.point same (pairedModel false) (paired_fits false)
    have right := sharp.point same (pairedModel true) (paired_fits true)
    have disagreement : QProb.Equiv (changesOutcome.value (pairedModel false))
        (changesOutcome.value (pairedModel true)) :=
      (QProb.toSignedRatio_equiv_iff _ _).mp
        (SignedRatio.equiv_trans left (SignedRatio.equiv_symm right))
    have impossible := QProb.equiv_trans (QProb.equiv_symm counterfactual_witnesses.1)
      (QProb.equiv_trans disagreement counterfactual_witnesses.2)
    exact (by decide : ¬ QProb.Equiv QProb.zero QProb.one) impossible
  | interval _ _ _ => exact True.intro

end Thesis.Examples.CausalAbstractionInverse
