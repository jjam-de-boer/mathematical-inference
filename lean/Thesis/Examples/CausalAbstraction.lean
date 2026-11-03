import Thesis.Causality.CausalAbstraction

namespace Thesis.Examples.CausalAbstraction
open Probability Causality

/-!
A three-observed-node micro SCM is merged into two Boolean macro nodes.
The AND case preserves the stated unique-preimage intervention. The OR case
has the same coarse observational cells as its macro CPT but fails under
the proposed double surgery. No claim is made for AND=false, all micro
representatives, an emergent node or a length-dependent scale theory.
-/

def microSignature : ObservedSignature where
  count := 3
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val < 2 ∧ child.val = 2)
  directed_earlier := by decide +kernel

def macroSignature : ObservedSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by decide +kernel

private def fair : FiniteProbRecord Bool := {
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl }

/-- Two independent private fair causes; the response has no additional
source. The product prior is part of the actual model record. -/
def microLatent : LatentExtension microSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident seed child := decide (seed.val = child.val)

def microModel : ExactModel microSignature where
  latent := microLatent
  factor _ := fair
  prior := FiniteProduct.record 2 (fun _ => Bool) (fun _ => fair)
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism child parents inputs :=
    if first : child.val = 0 then inputs (0 : Fin 2) (by simp [microLatent, first])
    else if second : child.val = 1 then inputs (1 : Fin 2) (by simp [microLatent, second])
    else
      have atResponse : child.val = 2 := by have bounded : child.val < 3 := child.isLt; omega
      (parents (0 : Fin 3) (by simp [microSignature, atResponse])) &&
        (parents (1 : Fin 3) (by simp [microSignature, atResponse]))

def responseParents (first second : Bool) : microSignature.ParentValues (2 : Fin 3) :=
  fun node _ => if node.val = 0 then first else second

/-- Literal mechanism invariance under exchanging its two cause inputs.
This is checked on the mechanism, not inferred from a data table. -/
theorem mechanism_swap (first second : Bool) (inputs : microModel.latent.Inputs (2 : Fin 3)) :
    microModel.mechanism (2 : Fin 3) (responseParents first second) inputs =
      microModel.mechanism (2 : Fin 3) (responseParents second first) inputs :=
  Bool.and_comm first second

private def andRoot : FiniteProbRecord Bool := {
  atoms := [(false, 3), (true, 1)]
  den := 4
  den_pos := by decide
  total_mass := rfl }

def andLatent : LatentExtension macroSignature where
  count := 1
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident _ child := decide (child.val = 0)

/-- X_M has the actual AND marginal and Y copies X_M. -/
def andMacro : ExactModel macroSignature where
  latent := andLatent
  factor _ := andRoot
  prior := FiniteProduct.record 1 (fun _ => Bool) (fun _ => andRoot)
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism child parents inputs :=
    if root : child.val = 0 then inputs (0 : Fin 1) (by simp [andLatent, root])
    else
      have response : child.val = 1 := by have bounded : child.val < 2 := child.isLt; omega
      parents (0 : Fin 2) (by simp [macroSignature, response])

private def orRoot : FiniteProbRecord Bool := {
  atoms := [(false, 1), (true, 3)]
  den := 4
  den_pos := by decide
  total_mass := rfl }
private def third : FiniteProbRecord Bool := {
  atoms := [(false, 2), (true, 1)]
  den := 3
  den_pos := by decide
  total_mass := rfl }

def orLatent : LatentExtension macroSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident seed child := decide (seed.val = child.val)

def orFactors (seed : Fin 2) : FiniteProbRecord Bool := if seed = 0 then orRoot else third

/-- An observational-CPT macro SCM: P(Y=true|X_M=true)=1/3 and
P(Y=true|X_M=false)=0, with independent noise. It is not a copy mechanism. -/
def orMacro : ExactModel macroSignature where
  latent := orLatent
  factor := orFactors
  prior := FiniteProduct.record 2 (fun _ => Bool) orFactors
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism child parents inputs :=
    if root : child.val = 0 then inputs (0 : Fin 2) (by simp [orLatent, root])
    else
      have response : child.val = 1 := by have bounded : child.val < 2 := child.isLt; omega
      (parents (0 : Fin 2) (by simp [macroSignature, response])) &&
        (inputs (1 : Fin 2) (by simp [orLatent, response]))

def mergeAssignment (combine : Bool → Bool → Bool) (assignment : microSignature.Assignment) : macroSignature.Assignment :=
  fun node => if node.val = 0 then combine (assignment (0 : Fin 3)) (assignment (1 : Fin 3))
    else assignment (2 : Fin 3)

def clusters (node : Fin macroSignature.count) : NodeSet microSignature :=
  fun member => if node.val = 0 then decide (member.val < 2) else decide (member.val = 2)

private theorem cluster_nonempty (node : Fin macroSignature.count) : ∃ member, clusters node member = true := by
  by_cases root : node.val = 0
  · exact ⟨(0 : Fin 3), by simp [clusters, root]⟩
  · exact ⟨(2 : Fin 3), by simp [clusters, root]⟩
private theorem cluster_disjoint : ∀ first second : Fin macroSignature.count, first ≠ second →
    NodeSet.Disjoint (clusters first) (clusters second) := by
  unfold NodeSet.Disjoint
  decide +kernel
private theorem merge_local (combine : Bool → Bool → Bool) (node : Fin macroSignature.count)
    (first second : microSignature.Assignment)
    (agree : ∀ member, clusters node member = true → first member = second member) :
    mergeAssignment combine first node = mergeAssignment combine second node := by
  by_cases root : node.val = 0
  · simp only [mergeAssignment, root, if_true]
    rw [agree (0 : Fin 3) (by simp [clusters, root]), agree (1 : Fin 3) (by simp [clusters, root])]
  · simp only [mergeAssignment, root, if_false]
    exact agree (2 : Fin 3) (by simp [clusters, root])

def macroDoTrue : HardIntervention macroSignature :=
  (HardIntervention.empty macroSignature).set (0 : Fin 2) true
def microDoubleTrue : HardIntervention microSignature :=
  ((HardIntervention.empty microSignature).set (0 : Fin 3) true).set (1 : Fin 3) true

private theorem representative_respects (combine : Bool → Bool → Bool) (ones : combine true true = true)
    (action : HardIntervention macroSignature) (admitted : action = macroDoTrue)
    (assignment : microSignature.Assignment) (realizes : microDoubleTrue.RealizedBy assignment) :
    action.RealizedBy (mergeAssignment combine assignment) := by
  subst action
  intro node value forced
  by_cases root : node = (0 : Fin 2)
  · subst node
    change some true = some value at forced
    cases Option.some.inj forced
    change combine (assignment (0 : Fin 3)) (assignment (1 : Fin 3)) = true
    rw [realizes (0 : Fin 3) true (by decide +kernel), realizes (1 : Fin 3) true (by decide +kernel)]
    exact ones
  · have absent := HardIntervention.set_away_from_target (HardIntervention.empty macroSignature) (0 : Fin 2) node true root
    change macroDoTrue.value node = none at absent
    rw [absent] at forced
    cases forced

def andCoarsening : FiniteCausalCoarseGraining microSignature macroSignature where
  microModel := microModel
  macroModel := andMacro
  cluster := clusters
  cluster_nonempty := cluster_nonempty
  cluster_disjoint := cluster_disjoint
  assignmentMap := mergeAssignment Bool.and
  coordinate_local := merge_local Bool.and
  admissible action := action = macroDoTrue
  representative _ _ := microDoubleTrue
  representative_respects := representative_respects Bool.and rfl

def orCoarsening : FiniteCausalCoarseGraining microSignature macroSignature where
  microModel := microModel
  macroModel := orMacro
  cluster := clusters
  cluster_nonempty := cluster_nonempty
  cluster_disjoint := cluster_disjoint
  assignmentMap := mergeAssignment Bool.or
  coordinate_local := merge_local Bool.or
  admissible action := action = macroDoTrue
  representative _ _ := microDoubleTrue
  representative_respects := representative_respects Bool.or rfl

def yTrue : Event macroSignature.Assignment := fun assignment => assignment (1 : Fin 2)
def macroTrue : Event macroSignature.Assignment := fun assignment => assignment (0 : Fin 2)

/-- This is a merge of two observed causes into one macro node, not
merely a relabelling of one observed variable's values. -/
theorem merged_cause_nodes : ∀ member : Fin 3,
    andCoarsening.microNodes (NodeSet.singleton (0 : Fin 2)) member = decide (member.val < 2) := by decide +kernel

/-- AND=true fixes both cause coordinates. No analogous assertion is made
for the three-preimage AND=false cell. -/
theorem and_true_unique_preimage (assignment : microSignature.Assignment) :
    andCoarsening.assignmentMap assignment (0 : Fin 2) = true ↔
      assignment (0 : Fin 3) = true ∧ assignment (1 : Fin 3) = true :=
  Bool.and_eq_true_iff

/-- Positive instance: at the declared unique-preimage intervention both
the actual macro event and the pushed-forward micro event have value one. -/
theorem and_merge_preserves :
    andCoarsening.PreservesEvent macroDoTrue rfl yTrue ∧
      QProb.Equiv (andMacro.interventionalValue macroDoTrue.value yTrue) QProb.one ∧
      QProb.Equiv ((andCoarsening.pushedInterventionalLaw macroDoTrue rfl).probVal yTrue) QProb.one := by
  unfold FiniteCausalCoarseGraining.PreservesEvent
  decide +kernel

/-- The OR macro model agrees on every coarse observational singleton. -/
theorem or_observational_cells : ∀ x y : Bool, QProb.Equiv
    (orMacro.observationalValue (fun assignment => (macroTrue assignment == x) && (yTrue assignment == y)))
    ((microModel.observationalDist.map (mergeAssignment Bool.or)).probVal
      (fun assignment => (macroTrue assignment == x) && (yTrue assignment == y))) := by decide +kernel

def coarseOrObservational : FiniteProbRecord macroSignature.Assignment :=
  microModel.observationalDist.map (mergeAssignment Bool.or)
private theorem or_evidence_positive : coarseOrObservational.EventPositive macroTrue := by decide +kernel

/-- The CPT value is computed from the actual coarse micro observational
record with a positive denominator: (1/4)/(3/4)=1/3. -/
theorem or_observational_conditional :
    QProb.Equiv (coarseOrObservational.probVal (fun assignment => macroTrue assignment && yTrue assignment)) ⟨1, 4, by decide⟩ ∧
    QProb.Equiv (coarseOrObservational.probVal macroTrue) ⟨3, 4, by decide⟩ ∧
    QProb.Equiv ((coarseOrObservational.conditionOn macroTrue or_evidence_positive).probVal yTrue) ⟨1, 3, by decide⟩ := by decide +kernel

/-- Negative instance: a valid forced-value representative and the correct
observational CPT still fail the interventional consistency obligation.
Double surgery has Y=true surely; the macro CPT intervention has value 1/3. -/
theorem or_merge_fails :
    QProb.Equiv ((orCoarsening.pushedInterventionalLaw macroDoTrue rfl).probVal yTrue) QProb.one ∧
      QProb.Equiv (orMacro.interventionalValue macroDoTrue.value yTrue) ⟨1, 3, by decide⟩ ∧
      ¬ orCoarsening.PreservesEvent macroDoTrue rfl yTrue := by
  unfold FiniteCausalCoarseGraining.PreservesEvent
  decide +kernel

end Thesis.Examples.CausalAbstraction
