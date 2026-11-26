import Thesis.Causality.CausalAbstraction
import Thesis.Causality.SharedResponseModel
import Thesis.Probability.Distros.PartialMomentBounds

/-!
# Constructing a finite causal abstraction, or refuting its specification

The modeller supplies the microscopic SCM, the target observed variables and
their acyclic directed graph, an aggregation of microscopic assignments, and a
partial correspondence between interventions. No macro SCM is supplied.

The unknown macro model is a rational probability law on the *complete* finite
carrier of deterministic response tables. Each accepted intervention and each
macro singleton contributes one exact linear moment equation. Thus the existing
constructive rational feasibility procedure either constructs all required
interventional laws simultaneously or excludes every finite SCM over the target
directed signature. Its single shared latent root allows arbitrary dependence
between response rows; the output makes no claim of sparse confounding or
independent node noise. The finite response carrier is derived from the target
signature, rather than imposed as an external hidden-alphabet bound.

This is a terminating finite decision procedure, not a practical-size promise:
the deterministic response carrier already grows rapidly with parent alphabets,
and exact linear elimination can increase the constraint count substantially.
Completeness concerns the fixed target variables, their allowed directed
parents, and the declared intervention map. It neither searches all aggregation
maps nor recovers a unique microscopic model from a coarse one.

The returned response law is one realization of the requested experimental
laws. Several feasible laws can encode different couplings between hypothetical
experiments; success therefore does not identify a unique counterfactual law,
select maximum entropy, or favor a complexity score. Such additional choices
would require their own declared criterion and proof.

Protocol validity is checked before numerical feasibility. In particular the
empty intervention must correspond to observation and must be among the
required macro actions. Every required action needs a microscopic representative,
and every accepted microscopic intervention must respect forced macro values on
*all* assignments, including assignments of probability zero. A protocol error
is therefore distinguishable from incompatible interventional probabilities.
-/

namespace Thesis.Causality.CausalAbstractionSynthesis
open Probability Probability.Distros

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

/-- Finite input data. `none` excludes a microscopic surgery rather than
silently interpreting it as observation. The required family states which
macro experiments the constructed abstraction must actually support. -/
structure Specification (micro coarse : ObservedSignature.{0}) where
  microModel : ExactModel micro
  aggregation : Aggregation micro coarse
  omega : HardIntervention micro → Option (HardIntervention coarse)
  required : List (HardIntervention coarse)

namespace Specification

/-- Every defined correspondence, generated from the complete finite list
of micro interventions. All of these pairs receive probability equations. -/
def comparisons (spec : Specification micro coarse) :
    List (HardIntervention micro × HardIntervention coarse) :=
  (interventions micro).flatMap fun intervention =>
    match spec.omega intervention with
    | none => []
    | some action => [(intervention, action)]

theorem comparison_iff (spec : Specification micro coarse)
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
def Valid (spec : Specification micro coarse) : Prop :=
  HardIntervention.empty coarse ∈ spec.required ∧
  spec.omega (HardIntervention.empty micro) = some (HardIntervention.empty coarse) ∧
  (∀ pair ∈ spec.comparisons, ∀ state ∈ micro.assignmentEnumeration,
    pair.1.RealizedBy state → pair.2.RealizedBy (spec.aggregation.assignmentMap state)) ∧
  (∀ action ∈ spec.required, ∃ pair ∈ spec.comparisons, pair.2 = action)

instance validDecidable (spec : Specification micro coarse) : Decidable spec.Valid := by
  unfold Valid
  infer_instance

/-- Finite validation supplies the universal forced-value obligation needed
by the public intervention-map interface, including null assignments. -/
theorem respects (spec : Specification micro coarse) (valid : spec.Valid)
    (intervention action) (defined : spec.omega intervention = some action)
    (state : micro.Assignment) (realized : intervention.RealizedBy state) :
    action.RealizedBy (spec.aggregation.assignmentMap state) :=
  valid.2.2.1 (intervention, action) ((spec.comparison_iff _ _).mpr defined)
    state (micro.assignmentEnumeration_complete state) realized

/-- Required actions have actual microscopic representatives. This is an
image-of-omega statement; numerical feasibility cannot manufacture coverage. -/
theorem covered (spec : Specification micro coarse) (valid : spec.Valid)
    (action : HardIntervention coarse) (required : action ∈ spec.required) :
    ∃ intervention, spec.omega intervention = some action := by
  obtain ⟨pair, listed, same⟩ := valid.2.2.2 action required
  refine ⟨pair.1, ?_⟩
  rw [← same]
  exact (spec.comparison_iff pair.1 pair.2).mp listed

/-- Pack a constructed target model with the already checked structural
map. Distributional exactness is proved independently below. -/
def interventionMap (spec : Specification micro coarse) (valid : spec.Valid)
    (macroModel : ExactModel coarse) : CausalInterventionMap micro coarse where
  microModel := spec.microModel
  macroModel := macroModel
  assignmentMap := spec.aggregation.assignmentMap
  omega := spec.omega
  respects := spec.respects valid

/-- The requested equality of complete interventional laws. The ambient
target class is every finite SCM on this directed signature, with arbitrary
finite latent alphabets and arbitrary rational source presentations. -/
def Fits (spec : Specification micro coarse) (macroModel : ExactModel coarse) : Prop :=
  ∀ intervention action, spec.omega intervention = some action → ∀ event,
    QProb.Equiv (macroModel.interventionalValue action.value event)
      (spec.microModel.interventionalValue intervention.value
        (fun state => event (spec.aggregation.assignmentMap state)))

/-- The same requirement at response-law level, before constructing the
single-root macro SCM. The response carrier is exhaustive, not sampled. -/
def ResponseFits (spec : Specification micro coarse)
    (law : FiniteProbRecord (SharedResponse.Table coarse)) : Prop :=
  ∀ pair ∈ spec.comparisons, ∀ event : Event coarse.Assignment,
    QProb.Equiv (law.probVal (fun table => event (SharedResponse.eval coarse pair.2.value table)))
      (spec.microModel.interventionalValue pair.1.value
        (fun state => event (spec.aggregation.assignmentMap state)))

/-- A single exact equation: the target table response reaches this macro
singleton with exactly the probability of its microscopic pullback. -/
def moment (spec : Specification micro coarse)
    (pair : HardIntervention micro × HardIntervention coarse)
    (reference : coarse.Assignment) : MomentInterval (SharedResponse.Table coarse) :=
  MomentInterval.exact
    (eventResponse (fun table => FiniteProbRecord.singletonEvent reference
      (SharedResponse.eval coarse pair.2.value table)))
    (spec.microModel.interventionalValue pair.1.value
      (fun state => FiniteProbRecord.singletonEvent reference
        (spec.aggregation.assignmentMap state))).toSignedRatio

/-- The complete finite system. Simplex rows, signed rational equality
encoding, exact feasible masses and infeasibility certificates are delegated
to the established constructive rational linear solver. -/
def problem (spec : Specification micro coarse) :
    PartialMomentProblem (SharedResponse.Table coarse) where
  cells := SharedResponse.enumeration coarse
  default := SharedResponse.defaultTable coarse
  nonempty := SharedResponse.enumeration_nonempty coarse
  distinct := SharedResponse.enumeration_nodup coarse
  intervals := spec.comparisons.flatMap fun pair =>
    coarse.assignmentEnumeration.map (spec.moment pair)

/-- An exact indicator expectation is precisely the probability of that
event. This elementary translation is checked independently of causal
soundness: the linear solver receives signed integer response coefficients
and rational bounds, while the model interface speaks in event probabilities. -/
private theorem eventMoment_iff (law : Distro A) (event : Event A) (value : QProb) :
    (MomentInterval.exact (eventResponse event) value.toSignedRatio).LawHolds law ↔
      QProb.Equiv (law.record.probVal event) value := by
  have indicator := eventResponse_expectation law event
  constructor
  · intro bounded
    have same := SignedRatio.equiv_of_le_of_le bounded.2 bounded.1
    exact (QProb.toSignedRatio_equiv_iff _ _).mp
      (SignedRatio.equiv_trans (SignedRatio.equiv_symm indicator) same)
  · intro same
    have mean := SignedRatio.equiv_trans indicator (QProb.toSignedRatio_congr same)
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) mean).mpr (SignedRatio.le_refl _),
      (SignedRatio.le_congr mean (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl _)⟩

/-- Singleton constraints imply equality for every event. This step is
essential: preserving selected coordinates or selected event masses alone
would not justify an exact causal abstraction. -/
theorem moments_iff_responseFits (spec : Specification micro coarse)
    (law : Distro (SharedResponse.Table coarse)) :
    (∀ constraint ∈ spec.problem.intervals, constraint.LawHolds law) ↔
      spec.ResponseFits law.record := by
  constructor
  · intro moments pair listed event
    let predicted := law.record.map (SharedResponse.eval coarse pair.2.value)
    let measured := (spec.microModel.interventionalDist pair.1.value).map
      spec.aggregation.assignmentMap
    have cells : ∀ reference, QProb.Equiv
        (predicted.probVal (FiniteProbRecord.singletonEvent reference))
        (measured.probVal (FiniteProbRecord.singletonEvent reference)) := by
      intro reference
      have equation := (eventMoment_iff law _ _).mp (moments (spec.moment pair reference)
        (List.mem_flatMap.mpr ⟨pair, listed,
          List.mem_map_of_mem (coarse.assignmentEnumeration_complete reference)⟩))
      exact QProb.equiv_trans (law.record.map_probVal _ _)
        (QProb.equiv_trans equation
          (QProb.equiv_symm (FiniteProbRecord.map_probVal _ _ _)))
    exact QProb.equiv_trans (QProb.equiv_symm (law.record.map_probVal _ _))
      (QProb.equiv_trans (FiniteProbRecord.probVal_extensional_of_singletons _ _
        coarse.assignmentEnumeration coarse.assignmentEnumeration_nodup
        coarse.assignmentEnumeration_complete cells event)
        (FiniteProbRecord.map_probVal _ _ _))
  · intro fitted constraint member
    obtain ⟨pair, listed, member⟩ := List.mem_flatMap.mp member
    obtain ⟨reference, _referenceListed, same⟩ := List.mem_map.mp member
    cases same
    exact (eventMoment_iff law _ _).mpr
      (fitted pair listed (FiniteProbRecord.singletonEvent reference))

/-- Every admissible response law yields a real macro SCM. This direction
does not require or assume a previously supplied macro construction. -/
theorem fits_of_responseFits (spec : Specification micro coarse)
    (law : FiniteProbRecord (SharedResponse.Table coarse))
    (fitted : spec.ResponseFits law) : spec.Fits (SharedResponse.model coarse law) := by
  intro intervention action defined event
  exact QProb.equiv_trans (SharedResponse.model_interventionalValue coarse law action.value event)
    (fitted (intervention, action) ((spec.comparison_iff _ _).mpr defined) event)

/-- Conversely, every finite target SCM has a response law satisfying the
same intervention equations. Its hidden alphabets and rational denominator
are unrestricted. This is the completeness bridge, not a search cutoff. -/
theorem responseFits_of_fits (spec : Specification micro coarse)
    (macroModel : ExactModel coarse) (fitted : spec.Fits macroModel) :
    spec.ResponseFits (SharedResponse.lawOf coarse macroModel) := by
  intro pair listed event
  exact QProb.equiv_trans
    (SharedResponse.lawOf_interventionalValue coarse macroModel pair.2.value event)
    (fitted pair.1 pair.2 ((spec.comparison_iff _ _).mp listed) event)

/-- A linear infeasibility certificate excludes every target SCM of the
declared signature, even those with hidden alphabets larger than the
response carrier used by the actual search. -/
theorem infeasible_not_exists (spec : Specification micro coarse)
    (certificate : RationalLinear.Infeasibility spec.problem.cells.length spec.problem.rows) :
    ¬ ∃ macroModel : ExactModel coarse, spec.Fits macroModel := by
  rintro ⟨macroModel, fitted⟩
  let law : Distro (SharedResponse.Table coarse) := ⟨SharedResponse.lawOf coarse macroModel⟩
  apply spec.problem.refutation_not_realizable certificate
  refine ⟨law, ?_, (spec.moments_iff_responseFits law).mpr
    (spec.responseFits_of_fits macroModel fitted)⟩
  intro atom _listed _positive
  exact SharedResponse.enumeration_complete coarse atom.1

/-- A success contains the solver's actual rational mass record and the
independently checked protocol. Derived accessors expose the constructed
SCM, its exact intervention map, and its required-action coverage. -/
structure Solution (spec : Specification micro coarse) where
  valid : spec.Valid
  responseLaw : spec.problem.CompatibleLaw

/-- Install the computed mass record as one shared source feeding the
target response tables. All mechanisms and latent-law normalization are
constructed by the existing response-table realization, not supplied by
the caller as an external macro-SCM witness. -/
def Solution.macroModel {spec : Specification micro coarse} (solution : spec.Solution) :
    ExactModel coarse :=
  SharedResponse.model coarse solution.responseLaw.distro.record

/-- Every admitted intervention preserves every target event under the
constructed model. Moment feasibility first gives singleton agreement;
finite extensionality in `moments_iff_responseFits` supplies the whole law. -/
theorem Solution.fits {spec : Specification micro coarse} (solution : spec.Solution) :
    spec.Fits solution.macroModel :=
  spec.fits_of_responseFits solution.responseLaw.distro.record
    ((spec.moments_iff_responseFits solution.responseLaw.distro).mp solution.responseLaw.moments)

/-- Package the computed model and the validated protocol as the public
partial intervention-map interface. The numerical exactness theorem stays
separate from the forced-value compatibility that justified this map. -/
def Solution.interventionMap {spec : Specification micro coarse} (solution : spec.Solution) :
    CausalInterventionMap micro coarse :=
  spec.interventionMap solution.valid solution.macroModel

/-- The synthesized map is exact on its entire declared domain, including
defined micro surgeries beyond the required macro representative family. -/
theorem Solution.exact {spec : Specification micro coarse} (solution : spec.Solution) :
    solution.interventionMap.Exact := solution.fits

/-- Every requested macro action really occurs in the intervention-map
image. The solver never enlarges omega's domain to repair missing coverage. -/
theorem Solution.covered {spec : Specification micro coarse} (solution : spec.Solution)
    (action : HardIntervention coarse) (required : action ∈ spec.required) :
    ∃ intervention, solution.interventionMap.omega intervention = some action :=
  spec.covered solution.valid action required

/-- The synthesized source may feed every observed coordinate. Its explicit
graph is consequently the fully bidirected graph; this construction must not
be advertised as preserving an input sparse confounding pattern. -/
theorem Solution.sharedGraph {spec : Specification micro coarse} (solution : spec.Solution)
    (first second : Fin coarse.count) :
    solution.macroModel.observedGraph.bidirected first second =
      (SharedResponse.graph coarse).bidirected first second :=
  SharedResponse.model_projectedGraph coarse solution.responseLaw.distro.record first second

/-- Observation is a required accepted comparison, not a default inserted
after solving the interventional constraints. -/
theorem Solution.observation {spec : Specification micro coarse} (solution : spec.Solution)
    (event : Event coarse.Assignment) :
    QProb.Equiv (solution.macroModel.observationalValue event)
      (spec.microModel.observationalValue
        (fun state => event (spec.aggregation.assignmentMap state))) :=
  solution.fits (HardIntervention.empty micro) (HardIntervention.empty coarse)
    solution.valid.2.1 event

/-- Three distinct outcomes: malformed intervention data, a constructed
macro model, or a numerical refutation for the valid declared protocol. -/
inductive Result (spec : Specification micro coarse) where
  | invalid (reason : ¬ spec.Valid)
  | feasible (solution : spec.Solution)
  | infeasible (valid : spec.Valid)
      (certificate : RationalLinear.Infeasibility spec.problem.cells.length spec.problem.rows)

/-- The success branch, stated through one named predicate so specialized
theorems share the very same dependent eliminator as their public contract. -/
def Result.IsFeasible {spec : Specification micro coarse} : spec.Result → Prop
  | .feasible _ => True
  | _ => False

/-- Numerical refutation of a valid protocol, separate from malformed input. -/
def Result.IsInfeasible {spec : Specification micro coarse} : spec.Result → Prop
  | .infeasible _ _ => True
  | _ => False

/-- Protocol rejection, before any conclusion about model realizability. -/
def Result.IsInvalid {spec : Specification micro coarse} : spec.Result → Prop
  | .invalid _ => True
  | _ => False

/-- Recognize success by inspecting the finite result constructor. This
lets checked reductions compute the actual solver branch directly. -/
instance Result.decidableIsFeasible {spec : Specification micro coarse}
    (result : spec.Result) : Decidable result.IsFeasible := by
  cases result <;> unfold Result.IsFeasible <;> infer_instance

/-- Protocol rejection is a decidable result tag, independently of the
proof object explaining why the protocol fails. -/
instance Result.decidableIsInvalid {spec : Specification micro coarse}
    (result : spec.Result) : Decidable result.IsInvalid := by
  cases result <;> unfold Result.IsInvalid <;> infer_instance

/-- Numerical infeasibility is likewise recognized by its constructor;
the certificate remains available separately for mathematical refutation. -/
instance Result.decidableIsInfeasible {spec : Specification micro coarse}
    (result : spec.Result) : Decidable result.IsInfeasible := by
  cases result <;> unfold Result.IsInfeasible <;> infer_instance

/-- Validate first and then run exact rational feasibility. No undefined
intervention, missing representative, or infeasible law is replaced by a
default distribution. -/
def solve (spec : Specification micro coarse) : spec.Result :=
  if valid : spec.Valid then
    match spec.problem.solve with
    | .feasible law => .feasible ⟨valid, law⟩
    | .infeasible certificate => .infeasible valid certificate
  else .invalid valid

/-- Success is equivalent to a valid protocol admitting some actual finite
target SCM. The converse quantifies over all such SCMs, rather than over a
bounded catalogue of latent alphabets or weighted examples. -/
theorem solve_success_iff (spec : Specification micro coarse) :
    spec.solve.IsFeasible ↔
      spec.Valid ∧ ∃ macroModel : ExactModel coarse, spec.Fits macroModel := by
  cases outcome : spec.solve with
  | invalid reason =>
    constructor
    · intro impossible; exact False.elim impossible
    · intro possible; exact False.elim (reason possible.1)
  | feasible solution =>
    constructor
    · intro _; exact ⟨solution.valid, solution.macroModel, solution.fits⟩
    · intro _; trivial
  | infeasible valid certificate =>
    constructor
    · intro impossible; exact False.elim impossible
    · intro possible; exact False.elim (spec.infeasible_not_exists certificate possible.2)

/-- Infeasibility is the complement of realizability *within a valid
protocol*. Invalid coverage data are intentionally not reported as a
mathematical impossibility of the proposed macro laws. -/
theorem solve_infeasible_iff (spec : Specification micro coarse) :
    spec.solve.IsInfeasible ↔
      spec.Valid ∧ ¬ ∃ macroModel : ExactModel coarse, spec.Fits macroModel := by
  cases outcome : spec.solve with
  | invalid reason =>
    constructor
    · intro impossible; exact False.elim impossible
    · intro impossible; exact False.elim (reason impossible.1)
  | feasible solution =>
    constructor
    · intro impossible; exact False.elim impossible
    · intro impossible
      exact False.elim (impossible.2 ⟨solution.macroModel, solution.fits⟩)
  | infeasible valid certificate =>
    constructor
    · intro _; exact ⟨valid, spec.infeasible_not_exists certificate⟩
    · intro _; trivial

/-- A malformed action domain is rejected before the rational solver is
inspected, even if its empty or incomplete equation list would be feasible. -/
theorem solve_invalid_iff (spec : Specification micro coarse) :
    spec.solve.IsInvalid ↔ ¬ spec.Valid := by
  cases outcome : spec.solve with
  | invalid reason => exact ⟨fun _ => reason, fun _ => trivial⟩
  | feasible solution =>
    exact ⟨fun impossible => False.elim impossible,
      fun invalid => False.elim (invalid solution.valid)⟩
  | infeasible valid certificate =>
    exact ⟨fun impossible => False.elim impossible,
      fun invalid => False.elim (invalid valid)⟩

end Specification
end Thesis.Causality.CausalAbstractionSynthesis
