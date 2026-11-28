import Thesis.Causality.CausalAbstraction
import Thesis.Probability.Construction

/-!
# Finite intervention protocols for causal abstraction

An assignment map and a partial intervention correspondence specify the
coarse interpretation of a fine experiment independently of either model.
The finite checks enforce observation, forced-value compatibility on all
assignments, and actual representatives for each required coarse action.
The same protocol supports forward abstraction and inference from coarse laws.
-/

namespace Thesis.Causality.CausalAbstractionSynthesis
open Probability

variable {micro coarse : ObservedSignature.{0}}

/-- Cluster and state-map data without a preselected macro model. The
nonempty, disjoint clusters retain the existing observed-node aggregation
discipline; a separate emergent-coordinate interface can be added later. -/
structure Aggregation (micro coarse : ObservedSignature.{0}) where
  cluster : Fin coarse.count → NodeSet micro
  cluster_nonempty : ∀ node, ∃ member, cluster node member = true
  cluster_disjoint : ∀ first second, first ≠ second →
    NodeSet.Disjoint (cluster first) (cluster second)
  assignmentMap : micro.Assignment → coarse.Assignment
  coordinate_local : ∀ node first second,
    (∀ member, cluster node member = true → first member = second member) →
      assignmentMap first node = assignmentMap second node

/-- Reuse an existing aggregation's structural data, discarding its proposed
macro model. Synthesis subsequently constructs its own model from the data. -/
def Aggregation.ofCoarseGraining (data : FiniteCausalCoarseGraining micro coarse) :
    Aggregation micro coarse :=
  ⟨data.cluster, data.cluster_nonempty, data.cluster_disjoint,
    data.assignmentMap, data.coordinate_local⟩

/-- Equality of dependent interventions is decided coordinatewise. This is
finite function comparison, not equality of arbitrary functions or choice. -/
instance interventionDecidableEq (S : ObservedSignature.{0}) :
    DecidableEq (HardIntervention S) := fun left right => by
  letI : DecidableEq ((i : Fin S.count) → Option (S.Value i)) :=
    FiniteProduct.assignmentDecidableEq S.count (fun i => Option (S.Value i))
      (fun _ => inferInstance)
  exact decidable_of_iff (left.value = right.value) ⟨
    fun same => HardIntervention.extensional (fun i => congrFun same i),
    fun same => congrArg HardIntervention.value same⟩

/-- Explicitly enumerate every hard intervention: at each coordinate choose
either no setting or one of the declared values. No action-size cutoff is used. -/
def interventions (S : ObservedSignature.{0}) : List (HardIntervention S) :=
  (FiniteProduct.enumeration S.count (fun i => Option (S.Value i))
    (fun i => none :: (S.valueEnumeration i).map some)).map HardIntervention.mk

theorem interventions_complete (S : ObservedSignature.{0}) (action : HardIntervention S) :
    action ∈ interventions S := by
  apply List.mem_map.mpr
  refine ⟨action.value, ?_, rfl⟩
  apply FiniteProduct.enumeration_complete
  intro node value
  cases value with
  | none => exact List.mem_cons_self
  | some value =>
    exact List.mem_cons_of_mem none
      (List.mem_map.mpr ⟨value, S.value_complete node value, rfl⟩)

/-- A finite check that an assignment realizes an intervention. Inspecting
only a forced coordinate avoids quantifying over every possible value there. -/
def realizes (action : HardIntervention micro) (state : micro.Assignment) : Bool :=
  finAll micro.count (fun node =>
    match action.value node with
    | none => true
    | some value => decide (state node = value))

theorem realizes_iff (action : HardIntervention micro) (state : micro.Assignment) :
    realizes action state = true ↔ action.RealizedBy state := by
  rw [realizes, finAll_eq_true_iff]
  constructor
  · intro checked node value forced
    have atNode := checked node
    rw [forced] at atNode
    exact of_decide_eq_true atNode
  · intro realized node
    cases forced : action.value node with
    | none => rfl
    | some value => exact decide_eq_true (realized node value forced)

instance realizesDecidable (action : HardIntervention micro) (state : micro.Assignment) :
    Decidable (action.RealizedBy state) :=
  decidable_of_iff (realizes action state = true) (realizes_iff action state)

/-- Structural data shared by the two directions of inference. The required
family can be a strict subset of the image of the supplied map. -/
structure Protocol (micro coarse : ObservedSignature.{0}) where
  aggregation : Aggregation micro coarse
  omega : HardIntervention micro → Option (HardIntervention coarse)
  required : List (HardIntervention coarse)

namespace Protocol

/-- Every defined correspondence, generated from the complete finite list
of micro interventions. The list describes the full domain of the partial map. -/
def comparisons (spec : Protocol micro coarse) :
    List (HardIntervention micro × HardIntervention coarse) :=
  (interventions micro).flatMap fun intervention =>
    match spec.omega intervention with
    | none => []
    | some action => [(intervention, action)]

theorem comparison_iff (spec : Protocol micro coarse)
    (intervention : HardIntervention micro) (action : HardIntervention coarse) :
    (intervention, action) ∈ spec.comparisons ↔ spec.omega intervention = some action := by
  constructor
  · intro member
    obtain ⟨source, _listed, belongs⟩ := List.mem_flatMap.mp member
    cases defined : spec.omega source with
    | none => simp [defined] at belongs
    | some target =>
      simp only [defined, List.mem_singleton] at belongs
      cases belongs
      exact defined
  · intro defined
    exact List.mem_flatMap.mpr ⟨intervention, interventions_complete micro intervention,
      by simp [defined]⟩

/-- All four protocol requirements are finite propositions. Requiring
observation explicitly excludes vacuous exactness on an empty action domain. -/
def Valid (spec : Protocol micro coarse) : Prop :=
  HardIntervention.empty coarse ∈ spec.required ∧
  spec.omega (HardIntervention.empty micro) = some (HardIntervention.empty coarse) ∧
  (∀ pair ∈ spec.comparisons, ∀ state ∈ micro.assignmentEnumeration,
    pair.1.RealizedBy state → pair.2.RealizedBy (spec.aggregation.assignmentMap state)) ∧
  (∀ action ∈ spec.required, ∃ pair ∈ spec.comparisons, pair.2 = action)

instance validDecidable (spec : Protocol micro coarse) : Decidable spec.Valid := by
  unfold Valid
  infer_instance

/-- Finite validation supplies the universal forced-value obligation needed
by the public intervention-map interface, including null assignments. -/
theorem respects (spec : Protocol micro coarse) (valid : spec.Valid)
    (intervention action) (defined : spec.omega intervention = some action)
    (state : micro.Assignment) (realized : intervention.RealizedBy state) :
    action.RealizedBy (spec.aggregation.assignmentMap state) :=
  valid.2.2.1 (intervention, action) ((spec.comparison_iff _ _).mpr defined)
    state (micro.assignmentEnumeration_complete state) realized

/-- Required actions have actual microscopic representatives. This is an
image-of-omega statement; numerical feasibility cannot manufacture coverage. -/
theorem covered (spec : Protocol micro coarse) (valid : spec.Valid)
    (action : HardIntervention coarse) (required : action ∈ spec.required) :
    ∃ intervention, spec.omega intervention = some action := by
  obtain ⟨pair, listed, same⟩ := valid.2.2.2 action required
  refine ⟨pair.1, ?_⟩
  rw [← same]
  exact (spec.comparison_iff pair.1 pair.2).mp listed

end Protocol
end Thesis.Causality.CausalAbstractionSynthesis
