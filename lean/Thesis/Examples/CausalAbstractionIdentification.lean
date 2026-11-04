import Thesis.Causality.CausalAbstractionQuery
import Thesis.CausalTransport.HedgeChannelCompleteness
import Thesis.CausalTransport.Hedge.WitnessSearch
import Thesis.Examples.CausalAbstractionRemainder

namespace Thesis.Examples.CausalAbstractionIdentification
open Probability Causality
open Thesis.Examples.CausalAbstraction

/-!
Model-level exactness does not imply graph-class identification monotonicity.
Fine graph: A ↔ Y, X → Y. Merge the block {A,X}, copying X as the
coarse value Z. Its declared quotient graph is the bow Z → Y, Z ↔ Y.
The fine do(A,X) query is identified; the coarse do(Z) query has a hedge.

The actual pair has Y = X xor positive private noise and has a shared input
that is incident but nonessential in Y's equation (and in the coarse
model). Both observed joints are strictly positive. The state map is exact
for EVERY micro hard intervention, with a total surjective ω and a section
for EVERY macro action. Thus neither missing action values nor unary or
unsupported observed labels explain the failure. Exactness of this pair
does not lift arbitrary models of the coarse bow class to the fine class.
No faithfulness or minimal-mechanism assumption is silently imposed.
-/

def fineSignature : ObservedSignature where
  count := 3
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val = 1 ∧ child.val = 2)
  directed_earlier := by decide +kernel

private def fair : FiniteProbRecord Bool := {
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl }
private def flipNoise : FiniteProbRecord Bool := {
  atoms := [(false, 3), (true, 1)]
  den := 4
  den_pos := by decide
  total_mass := rfl }

def factors (seed : Fin 3) : FiniteProbRecord Bool := if seed.val = 2 then flipNoise else fair

def fineLatent : LatentExtension fineSignature where
  count := 3
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident seed child := if seed.val = 0 then decide (child.val = 0 ∨ child.val = 2)
    else if seed.val = 1 then decide (child.val = 1) else decide (child.val = 2)

def fineModel : ExactModel fineSignature where
  latent := fineLatent
  factor := factors
  prior := FiniteProduct.record 3 (fun _ => Bool) factors
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism child parents inputs :=
    if atA : child.val = 0 then inputs (0 : Fin 3) (by simp [fineLatent, atA])
    else if atX : child.val = 1 then inputs (1 : Fin 3) (by simp [fineLatent, atX])
    else
      have atY : child.val = 2 := by have bound : child.val < 3 := child.isLt; omega
      Bool.xor (parents (1 : Fin 3) (by simp [fineSignature, atY]))
        (inputs (2 : Fin 3) (by simp [fineLatent, atY]))

def coarseLatent : LatentExtension macroSignature where
  count := 3
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident seed child := if seed.val = 0 then true
    else if seed.val = 1 then decide (child.val = 0) else decide (child.val = 1)

def coarseModel : ExactModel macroSignature where
  latent := coarseLatent
  factor := factors
  prior := FiniteProduct.record 3 (fun _ => Bool) factors
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism child parents inputs :=
    if atZ : child.val = 0 then inputs (1 : Fin 3) (by simp [coarseLatent, atZ])
    else
      have atY : child.val = 1 := by have bound : child.val < 2 := child.isLt; omega
      Bool.xor (parents (0 : Fin 2) (by simp [macroSignature, atY]))
        (inputs (2 : Fin 3) (by simp [coarseLatent, atY]))

def fineGraph : ObservedGraph fineSignature := fineModel.observedGraph

def coarseGraph : ObservedGraph macroSignature := coarseModel.observedGraph

def copyAssignment (state : fineSignature.Assignment) : macroSignature.Assignment :=
  fun node => if node.val = 0 then state (1 : Fin 3) else state (2 : Fin 3)

def fineAction3 (first second response : Option Bool) : HardIntervention fineSignature where
  value node := if node.val = 0 then first else if node.val = 1 then second else response

private theorem fineAction3_eta (action : HardIntervention fineSignature) :
    action = fineAction3 (action.value (0 : Fin 3)) (action.value (1 : Fin 3)) (action.value (2 : Fin 3)) := by
  apply HardIntervention.extensional
  intro node
  have bound : node.val < 3 := node.isLt
  by_cases first : node.val = 0
  · have equal : node = (0 : Fin 3) := Fin.ext first
    subst node; rfl
  · by_cases second : node.val = 1
    · have equal : node = (1 : Fin 3) := Fin.ext second
      subst node; rfl
    · have equal : node = (2 : Fin 3) := Fin.ext (by change node.val = 2; omega)
      subst node; rfl

/-- The extra fine coordinate A is ignored by the aggregate's copied value. -/
def copyOmega (intervention : HardIntervention fineSignature) : Option (HardIntervention macroSignature) :=
  some (coarseAction (intervention.value (1 : Fin 3)) (intervention.value (2 : Fin 3)))

def copyRepresentative (action : HardIntervention macroSignature) : HardIntervention fineSignature :=
  fineAction3 (if (action.value (0 : Fin 2)).isSome then some false else none)
    (action.value (0 : Fin 2)) (action.value (1 : Fin 2))

def copyMap : CausalInterventionMap fineSignature macroSignature where
  microModel := fineModel
  macroModel := coarseModel
  assignmentMap := copyAssignment
  omega := copyOmega
  respects := by
    intro intervention action defined state realizes
    cases Option.some.inj defined
    intro node value forced
    have bound : node.val < 2 := node.isLt
    by_cases root : node.val = 0
    · have equal : node = (0 : Fin 2) := Fin.ext root
      subst node
      exact realizes (1 : Fin 3) value forced
    · have equal : node = (1 : Fin 2) := Fin.ext (by change node.val = 1; omega)
      subst node
      exact realizes (2 : Fin 3) value forced

theorem copy_section : copyMap.IsSection (fun _ => True) (fun action _ => copyRepresentative action) := by
  intro action _
  change some (coarseAction (action.value (0 : Fin 2)) (action.value (1 : Fin 2))) = some action
  exact congrArg some (coarseAction_eta action).symm

def copyCoarsening : FiniteCausalCoarseGraining fineSignature macroSignature where
  microModel := fineModel
  macroModel := coarseModel
  cluster := clusters
  cluster_nonempty := andCoarsening.cluster_nonempty
  cluster_disjoint := andCoarsening.cluster_disjoint
  assignmentMap := copyAssignment
  coordinate_local := by
    intro node first second agree
    by_cases root : node.val = 0
    · simpa only [copyAssignment, root, if_true] using agree (1 : Fin 3) (by simp [clusters, root])
    · simpa only [copyAssignment, root, if_false] using agree (2 : Fin 3) (by simp [clusters, root])
  admissible _ := True
  representative action _ := copyRepresentative action
  representative_respects action admitted := copyMap.respects _ _ (copy_section action admitted)

private theorem optionBool_cases (value : Option Bool) :
    value = none ∨ value = some false ∨ value = some true := by
  cases value with
  | none => exact Or.inl rfl
  | some value => cases value with
    | false => exact Or.inr (Or.inl rfl)
    | true => exact Or.inr (Or.inr rfl)

private theorem copy_cells : ∀ (a x y : Option Bool) (z result : Bool), QProb.Equiv
    ((coarseModel.interventionalDist (coarseAction x y).value).probVal
      (FiniteProbRecord.singletonEvent (coarseState z result)))
    (((fineModel.interventionalDist (fineAction3 a x y).value).map copyAssignment).probVal
      (FiniteProbRecord.singletonEvent (coarseState z result))) := by
  intro a x y
  rcases optionBool_cases a with rfl | rfl | rfl <;>
    rcases optionBool_cases x with rfl | rfl | rfl <;>
    rcases optionBool_cases y with rfl | rfl | rfl <;> decide +kernel

/-- The representative intervenes on whole clusters, so action-node
locality is respected as well as forced values. No action-coverage gap is
used to obtain the identification obstruction below. -/
theorem copy_representative_targets (action : HardIntervention macroSignature) :
    (copyRepresentative action).targets = copyCoarsening.microNodes action.targets := by
  rw [coarseAction_eta action]
  rcases optionBool_cases (action.value (0 : Fin 2)) with root | root | root <;>
    rcases optionBool_cases (action.value (1 : Fin 2)) with response | response | response <;>
    rw [root, response] <;> apply funext <;> decide +kernel

theorem copy_omega_total (intervention : HardIntervention fineSignature) :
    ∃ action, copyMap.omega intervention = some action := ⟨_, rfl⟩

/-- Full-law exactness for all 27 fine interventions, not only a selected
value or an observational law. Every coarse intervention has a representative. -/
theorem copy_exact : copyMap.Exact := by
  intro intervention action defined event
  cases Option.some.inj defined
  have agreement : ∀ state, QProb.Equiv
      ((coarseModel.interventionalDist (coarseAction (intervention.value (1 : Fin 3))
        (intervention.value (2 : Fin 3))).value).probVal (FiniteProbRecord.singletonEvent state))
      (((fineModel.interventionalDist intervention.value).map copyAssignment).probVal (FiniteProbRecord.singletonEvent state)) := by
    intro state
    rw [fineAction3_eta intervention, coarseState_eta state]
    exact copy_cells _ _ _ _ _
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_extensional_of_singletons _ _ macroSignature.assignmentEnumeration
      macroSignature.assignmentEnumeration_nodup macroSignature.assignmentEnumeration_complete agreement event)
    (FiniteProbRecord.map_probVal _ _ _)

theorem copy_preservesAt (action : HardIntervention macroSignature) : copyCoarsening.PreservesAt action True.intro :=
  copyCoarsening.preservesAt_of_section copyMap rfl rfl rfl copy_section copy_exact action True.intro

def coarseQuery : JointKernelQuery macroSignature where
  outcome := NodeSet.singleton (1 : Fin 2)
  action := NodeSet.singleton (0 : Fin 2)
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def fineQuery : JointKernelQuery fineSignature := copyCoarsening.pullbackQuery coarseQuery

theorem query_is_cluster_local : copyCoarsening.PullsBackQuery fineQuery coarseQuery := ⟨rfl, rfl⟩

/-- The quotient's edges are the existential images of fine edges between
the declared blocks, not unrelated arrows attached to a graph label. -/
theorem quotient_edges : ∀ first second : Fin 2,
    (macroSignature.directed first second =
      finAny 3 (fun a => clusters first a && finAny 3 (fun b => clusters second b && fineSignature.directed a b))) ∧
    (coarseGraph.bidirected first second =
      (decide (first ≠ second) && finAny 3 (fun a => clusters first a &&
        finAny 3 (fun b => clusters second b && fineGraph.bidirected a b)))) := by decide +kernel

theorem fine_compatible : Compatible fineModel fineGraph := by
  constructor
  · unfold FiniteLatentSCM.IsCanonicalSemiMarkovian LatentExtension.CanonicalSemiMarkovian
    decide +kernel
  · intro first second; rfl

theorem coarse_compatible : Compatible coarseModel coarseGraph := by
  constructor
  · unfold FiniteLatentSCM.IsCanonicalSemiMarkovian LatentExtension.CanonicalSemiMarkovian
    decide +kernel
  · intro first second; rfl

private theorem fine_positive_cells : ∀ a x y : Bool,
    0 < (fineModel.observationalDist.probVal (FiniteProbRecord.singletonEvent (fineState a x y))).num := by decide +kernel

private theorem coarse_positive_cells : ∀ x y : Bool,
    0 < (coarseModel.observationalDist.probVal (FiniteProbRecord.singletonEvent (coarseState x y))).num := by decide +kernel

theorem fine_positive : ObservationallyPositive fineModel := by
  intro state
  rw [fineState_eta state]
  exact fine_positive_cells _ _ _

theorem coarse_positive : ObservationallyPositive coarseModel := by
  intro state
  rw [coarseState_eta state]
  exact coarse_positive_cells _ _

def fineRich : ObservedSignature.ValueRich fineSignature where
  first _ := false
  second _ := true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different _ := Bool.false_ne_true

def coarseRich : ObservedSignature.ValueRich macroSignature where
  first _ := false
  second _ := true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different _ := Bool.false_ne_true

/-- The fallback syntax is unreachable, as the next equation certifies. -/
def fineFormula : ProbabilityTerm fineSignature :=
  match identifyJointKernel fineGraph fineQuery with
  | .identified term => term
  | _ => .zero

theorem fine_id_succeeds : identifyJointKernel fineGraph fineQuery = .identified fineFormula := by rfl

theorem fine_identifiable : (GraphModelClass.positive fineGraph).identifiable fineQuery :=
  identifyJointKernel_identified_identifiable (C := GraphModelClass.positive fineGraph) fineGraph.dSeparationCorrectness
    (fun member => member.2) fineQuery fine_id_succeeds

def coarseHedgeSelection : HedgeSelection macroSignature where
  large := NodeSet.full
  small := NodeSet.singleton (1 : Fin 2)
  child node := if node.val = 0 then some (1 : Fin 2) else none

theorem coarse_hedge_tests : hedgeTestsHold coarseGraph coarseQuery coarseHedgeSelection = true := by decide +kernel

def coarseHedge : HedgeWitness coarseGraph coarseQuery :=
  hedgeWitness_of_sets coarseGraph coarseQuery coarseHedgeSelection coarse_hedge_tests

theorem coarse_id_fails :
    (match identifyJointKernel coarseGraph coarseQuery with
      | .failed _ => true
      | _ => false) = true := by decide +kernel

/-- Invoke the unchanged published positive, value-rich completeness API.
This gives actual compatible positive countermodels, not merely an ID flag. -/
noncomputable def coarseCounterexample : CounterexampleIn (GraphModelClass.positive coarseGraph) coarseQuery :=
  (coarseGraph.publishedCompleteness coarseRich).hedge_counterexample coarseQuery coarseHedge

theorem coarse_not_identifiable : ¬ (GraphModelClass.positive coarseGraph).identifiable coarseQuery :=
  coarseCounterexample.not_identifiable

theorem fine_has_no_hedge : ¬ Nonempty (HedgeWitness fineGraph fineQuery) := by
  intro ⟨witness⟩
  exact ((fineGraph.publishedCompleteness fineRich).hedge_counterexample fineQuery witness).not_identifiable fine_identifiable

/-- A precise obstruction to the proposed implication: total, surjective
model-level exactness and cluster-local queries do not transport ID from the
fine positive graph class to the entire coarse positive graph class. -/
theorem exact_copy_does_not_transport_graph_identification :
    copyMap.Exact ∧
    copyMap.IsSection (fun _ => True) (fun action _ => copyRepresentative action) ∧
    copyCoarsening.PullsBackQuery fineQuery coarseQuery ∧
    (GraphModelClass.positive fineGraph).Mem fineModel ∧
    (GraphModelClass.positive coarseGraph).Mem coarseModel ∧
    (GraphModelClass.positive fineGraph).identifiable fineQuery ∧
    ¬ (GraphModelClass.positive coarseGraph).identifiable coarseQuery :=
  ⟨copy_exact, copy_section, query_is_cluster_local, ⟨fine_compatible, fine_positive⟩,
    ⟨coarse_compatible, coarse_positive⟩, fine_identifiable, coarse_not_identifiable⟩

theorem no_exact_only_ID_transfer :
    ¬ (copyMap.Exact → copyCoarsening.PullsBackQuery fineQuery coarseQuery →
      (GraphModelClass.positive fineGraph).identifiable fineQuery →
      (GraphModelClass.positive coarseGraph).identifiable coarseQuery) := by
  intro transfer
  exact coarse_not_identifiable (transfer copy_exact query_is_cluster_local fine_identifiable)

/-! The older illegal OR aggregation gives a different phenomenon:
its fine query has a successful ID run, but substituting the observational
macro CPT's do value changes 1 to 1/3. Exactness is absent here. -/

def illegalORFineQuery : JointKernelQuery microSignature := orCoarsening.pullbackQuery coarseQuery

def illegalORFineFormula : ProbabilityTerm microSignature :=
  match identifyJointKernel microModel.observedGraph illegalORFineQuery with
  | .identified term => term
  | _ => .zero

theorem illegal_or_fine_id_succeeds :
    identifyJointKernel microModel.observedGraph illegalORFineQuery = .identified illegalORFineFormula := by rfl

theorem illegal_or_query_is_cluster_local : orCoarsening.PullsBackQuery illegalORFineQuery coarseQuery := ⟨rfl, rfl⟩

theorem illegal_or_CPT_disagrees :
    QProb.Equiv ((orCoarsening.pushedInterventionalLaw macroDoTrue rfl).probVal yTrue) QProb.one ∧
    QProb.Equiv (orMacro.interventionalValue macroDoTrue.value yTrue) ⟨1, 3, by decide⟩ ∧
    ¬ orCoarsening.PreservesEvent macroDoTrue rfl yTrue := or_merge_fails

end Thesis.Examples.CausalAbstractionIdentification

