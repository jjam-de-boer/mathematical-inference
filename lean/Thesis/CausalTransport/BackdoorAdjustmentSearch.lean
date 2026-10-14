import Thesis.CausalTransport.BackdoorAdjustment
import Thesis.Causality.NodeSetEnumeration

namespace Thesis
namespace Causality
namespace BackdoorAdjustmentSearch

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Automatic, certified search through the implemented adjustment criterion

The input is a graph and a joint query, not a manually supplied list of
covariate witnesses.  Every subset outside the action and outcome is listed
once and checked against the two graphical do-rule leaves interpreted by
`BackdoorAdjustmentWitness`.  The runtime output contains only literal
formula plans.  A separate offline catalogue supplies native soundness for
those exact plans; proof-bearing SCM interpretation functions never become
runtime search inputs.

Completeness here has a precise boundary: search succeeds if and only if
some set passing these two specified graphical conditions has an available
adjustment formula.  It is not completeness among all do-calculus formulas,
all generalized adjustment criteria, or all distribution-specific methods.
Failure of support is not an ID-failure or nonidentifiability certificate.

Rule 3 uses the incoming cut on the action.  Its empty conditioner makes
`Z(W)` equal the whole action, by the existing proved non-ancestor identity.
No outgoing-cut substitute, positivity assumption, or classical decision of
a semantic proposition is hidden in the executable checker.
-/

/-! ## Exact graphical tests and their constructive witness -/

/-- Covariates can use every observed node except action and outcome nodes.
Restricted-product enumeration avoids duplicates outside this region. -/
def eligibleNodes (query : JointKernelQuery S) : NodeSet S :=
  NodeSet.diff NodeSet.full (NodeSet.union query.action query.outcome)

/-- The allowed region is exactly the two required disjointnesses.  Only
individual Boolean membership bits are split, not arbitrary propositions. -/
theorem eligibleNodes_iff (query : JointKernelQuery S) (covariates : NodeSet S) :
    NodeSet.Subset covariates (eligibleNodes query) ↔
      NodeSet.Disjoint query.action covariates ∧ NodeSet.Disjoint query.outcome covariates := by
  constructor
  · intro contained
    constructor
    · intro node atAction
      cases atCovariate : covariates node with
      | false => rfl
      | true =>
          have allowed := contained node atCovariate
          simp only [eligibleNodes, NodeSet.diff, NodeSet.full, NodeSet.union,
            atAction, Bool.true_or, Bool.not_true, Bool.and_false] at allowed
          cases allowed
    · intro node atOutcome
      cases atCovariate : covariates node with
      | false => rfl
      | true =>
          have allowed := contained node atCovariate
          simp only [eligibleNodes, NodeSet.diff, NodeSet.full, NodeSet.union,
            atOutcome, Bool.or_true, Bool.not_true, Bool.and_false] at allowed
          cases allowed
  · rintro ⟨actionDisjoint, outcomeDisjoint⟩ node atCovariate
    have outsideAction : query.action node = false := by
      cases atAction : query.action node with
      | false => rfl
      | true =>
          exact False.elim
            (Bool.false_ne_true ((actionDisjoint node atAction).symm.trans atCovariate))
    have outsideOutcome : query.outcome node = false := by
      cases atOutcome : query.outcome node with
      | false => rfl
      | true =>
          exact False.elim
            (Bool.false_ne_true ((outcomeDisjoint node atOutcome).symm.trans atCovariate))
    simp only [eligibleNodes, NodeSet.diff, NodeSet.full, NodeSet.union,
      outsideAction, outsideOutcome, Bool.false_or, Bool.not_false, Bool.and_true]

/-- Rule 3 removes the action from the unconditional covariate marginal. -/
def removeActionSide (graph : ObservedGraph S) (query : JointKernelQuery S)
    (covariates : NodeSet S) : Bool :=
  graph.dSeparated (.bar query.action) covariates query.action NodeSet.empty

/-- Rule 2 exchanges the outcome action for observation given covariates. -/
def exchangeActionSide (graph : ObservedGraph S) (query : JointKernelQuery S)
    (covariates : NodeSet S) : Bool :=
  graph.dSeparated (.barUnderline NodeSet.empty query.action)
    query.outcome query.action covariates

/-- The exact implemented criterion, including both disjointness tests.
The named rule tests are finite graph computations, not semantic oracles. -/
def valid (graph : ObservedGraph S) (query : JointKernelQuery S)
    (covariates : NodeSet S) : Bool :=
  ((NodeSet.disjointBool query.action covariates &&
    NodeSet.disjointBool query.outcome covariates) &&
    removeActionSide graph query covariates) && exchangeActionSide graph query covariates

/-- Inspectable proof evidence for exactly the four tests above.  This
names the criterion independently of how the witness constructors encode
their probability-kernel endpoints. -/
structure GraphicalConditions (graph : ObservedGraph S) (query : JointKernelQuery S)
    (covariates : NodeSet S) : Prop where
  action_disjoint : NodeSet.Disjoint query.action covariates
  outcome_disjoint : NodeSet.Disjoint query.outcome covariates
  removeAction : removeActionSide graph query covariates = true
  exchangeAction : exchangeActionSide graph query covariates = true

/-- The checker neither omits nor adds a condition to this named criterion. -/
theorem valid_iff (graph : ObservedGraph S) (query : JointKernelQuery S)
    (covariates : NodeSet S) :
    valid graph query covariates = true ↔ GraphicalConditions graph query covariates := by
  constructor
  · intro accepted
    have parts := Bool.and_eq_true_iff.mp accepted
    have first := Bool.and_eq_true_iff.mp parts.1
    have disjoint := Bool.and_eq_true_iff.mp first.1
    exact ⟨(NodeSet.disjointBool_eq_true_iff _ _).mp disjoint.1,
      (NodeSet.disjointBool_eq_true_iff _ _).mp disjoint.2, first.2, parts.2⟩
  · intro conditions
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr
          ⟨(NodeSet.disjointBool_eq_true_iff _ _).mpr conditions.action_disjoint,
            (NodeSet.disjointBool_eq_true_iff _ _).mpr conditions.outcome_disjoint⟩,
          conditions.removeAction⟩, conditions.exchangeAction⟩

/-- A passing Boolean check constructs both genuine do-rule applications.
No separation theorem is assumed, and no witness is selected by choice.
The small orientation proofs use supplied disjointness plus Boolean bits. -/
def witnessOfValid (projection : FiniteLatentProjection S) (query : JointKernelQuery S)
    (covariates : NodeSet S) (accepted : valid projection.observedGraph query covariates = true) :
    BackdoorAdjustmentWitness projection query covariates := by
  let conditions := (valid_iff projection.observedGraph query covariates).mp accepted
  have covariatesAction : NodeSet.Disjoint covariates query.action := by
    intro node atCovariate
    cases atAction : query.action node with
    | false => rfl
    | true =>
        exact False.elim
          (Bool.false_ne_true ((conditions.action_disjoint node atAction).symm.trans atCovariate))
  have outcomeAction : NodeSet.Disjoint query.outcome query.action := by
    intro node atOutcome
    cases atAction : query.action node with
    | false => rfl
    | true =>
        exact False.elim
          (Bool.false_ne_true ((query.action_outcome_disjoint node atAction).symm.trans atOutcome))
  refine ⟨conditions.action_disjoint, conditions.outcome_disjoint,
    .rule3 NodeSet.empty covariates query.action NodeSet.empty
      (FourWayDisjoint.emptyAction _ _ _ covariatesAction
        (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _)) ?_,
    .rule2 NodeSet.empty query.outcome query.action covariates
      (FourWayDisjoint.emptyAction _ _ _ outcomeAction
        conditions.outcome_disjoint conditions.action_disjoint) ?_⟩
  · change projection.observedGraph.dSeparated
      { removeIncoming := NodeSet.union NodeSet.empty
          (projection.observedGraph.nonAncestorsOf (.bar NodeSet.empty) query.action NodeSet.empty),
        removeOutgoing := NodeSet.empty }
      covariates query.action (NodeSet.union NodeSet.empty NodeSet.empty) = true
    simpa only [ObservedGraph.nonAncestorsOf_empty_targets, NodeSet.union_empty_left,
      GraphMutilation.bar, removeActionSide] using conditions.removeAction
  · change projection.observedGraph.dSeparated (.barUnderline NodeSet.empty query.action)
      query.outcome query.action (NodeSet.union NodeSet.empty covariates) = true
    simpa only [NodeSet.union_empty_left, exchangeActionSide] using conditions.exchangeAction

/-! ## Complete generated covariates, runtime plans, and offline certificates -/

/-- Check every eligible subset, retaining precisely the valid ones. -/
def covariates (graph : ObservedGraph S) (query : JointKernelQuery S) : List (NodeSet S) :=
  (NodeSet.subsets (eligibleNodes query)).filter (valid graph query)

/-- Every set satisfying the implemented criterion is generated, and every
generated set satisfies it.  No caller-provided completeness list is needed. -/
theorem covariates_member_iff (graph : ObservedGraph S) (query : JointKernelQuery S)
    (selected : NodeSet S) : selected ∈ covariates graph query ↔ valid graph query selected = true := by
  constructor
  · intro member
    exact (List.mem_filter.mp member).2
  · intro accepted
    let conditions := (valid_iff graph query selected).mp accepted
    exact List.mem_filter.mpr
      ⟨(NodeSet.subsets_member_iff _ _).mpr
        ((eligibleNodes_iff query selected).mpr
          ⟨conditions.action_disjoint, conditions.outcome_disjoint⟩), accepted⟩

/-- Filtering preserves the subset enumerator's no-repetition guarantee. -/
theorem covariates_nodup (graph : ObservedGraph S) (query : JointKernelQuery S) :
    (covariates graph query).Nodup :=
  List.Pairwise.filter _ (NodeSet.subsets_nodup (eligibleNodes query))

/-- Literal formula data; the runtime does not need a witness or an SCM. -/
def plan (query : JointKernelQuery S) (selected : NodeSet S) : ObservationalFormulaPlan S :=
  ⟨BackdoorAdjustmentWitness.formula query selected, .always⟩

def plans (graph : ObservedGraph S) (query : JointKernelQuery S) : List (ObservationalFormulaPlan S) :=
  (covariates graph query).map (plan query)

/-- Attach already computed membership proofs to the generated sets, then
certify each by the existing universal native adjustment theorem.  This is
offline proof assembly, not an executable extraction from an existential. -/
noncomputable def catalogue (projection : FiniteLatentProjection S) (query : JointKernelQuery S) :
    List (GuardedObservationalFormula projection query.sourceTerm) :=
  (covariates projection.observedGraph query).attach.map (fun entry =>
    (witnessOfValid projection query entry.val
      ((covariates_member_iff _ _ _).mp entry.property)).candidate)

/-- The generated runtime list is exactly the projection of its certified
catalogue, with unchanged formula syntax, guards, order, and multiplicity. -/
theorem plans_certified (projection : FiniteLatentProjection S) (query : JointKernelQuery S) :
    plans projection.observedGraph query = (catalogue projection query).map GuardedObservationalFormula.plan := by
  unfold plans catalogue
  rw [List.map_map]
  change (covariates projection.observedGraph query).map (plan query) =
    (covariates projection.observedGraph query).attach.map (fun entry => plan query entry.val)
  exact List.attach_map_val.symm

/-! ## Exact search coverage and native soundness -/

/-- Automatic search depends only on the graph, query, observed record and
reference assignment.  Hidden mechanisms and semantic proofs are absent. -/
def select (graph : ObservedGraph S) (query : JointKernelQuery S)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    Option (ObservationalFormulaPlan S) :=
  ObservationalFormulaPlan.select record reference (plans graph query)

/-- Exact coverage: some supported formula passing the implemented
criterion exists if and only if the automatic runtime search succeeds. -/
theorem select_complete_iff (graph : ObservedGraph S) (query : JointKernelQuery S)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    (∃ chosen, select graph query record reference = some chosen) ↔
      ∃ selected, valid graph query selected = true ∧ (plan query selected).available record reference = true := by
  constructor
  · rintro ⟨chosen, found⟩
    have member := ObservationalFormulaPlan.select_mem record reference (plans graph query) chosen found
    rcases List.mem_map.mp member with ⟨selected, listed, same⟩
    exact ⟨selected, (covariates_member_iff _ _ _).mp listed,
      by
        rw [same]
        exact ObservationalFormulaPlan.select_available record reference (plans graph query) chosen found⟩
  · rintro ⟨selected, validSet, available⟩
    exact ObservationalFormulaPlan.select_complete record reference (plans graph query)
      ⟨plan query selected,
        List.mem_map_of_mem ((covariates_member_iff _ _ _).mpr validSet), available⟩

/-- No result means precisely that every valid adjustment formula is
unavailable.  It does not deny the existence of other identification methods. -/
theorem select_none_iff (graph : ObservedGraph S) (query : JointKernelQuery S)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    select graph query record reference = none ↔
      forall selected, valid graph query selected = true →
        (plan query selected).available record reference = false := by
  rw [select, ObservationalFormulaPlan.select_none_iff]
  constructor
  · intro unavailable selected validSet
    exact unavailable (plan query selected)
      (List.mem_map_of_mem ((covariates_member_iff _ _ _).mpr validSet))
  · intro unavailable chosen member
    rcases List.mem_map.mp member with ⟨selected, listed, same⟩
    rw [← same]
    exact unavailable selected ((covariates_member_iff _ _ _).mp listed)

/-- Every selected formula gives the actual native interventional target.
Joint source support is internally unconditional; only the literal selected
formula must be available.  Zero covariate weights retain their skip rule. -/
noncomputable def selected_soundAt (model : FiniteHiddenDAGSCM S P)
    (query : JointKernelQuery S) (reference : S.Assignment) (chosen : ObservationalFormulaPlan S)
    (found : select P.observedGraph query model.observationalDist reference = some chosen) :
    model.TermEquivalentAt query.sourceTerm chosen.formula reference :=
  GuardedObservationalFormula.select_plan_soundAt model reference (catalogue P query)
    (plans P.observedGraph query) (plans_certified P query) chosen found
    (model.kernelSupportedAt_unconditional query.outcome query.action reference)

/-- A caller can preserve an existing supported ID formula by putting its
literal plan first.  Unsupported ID output falls through to generated sets. -/
def selectWithPreferred (graph : ObservedGraph S) (query : JointKernelQuery S)
    (preferred : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) : Option (ObservationalFormulaPlan S) :=
  ObservationalFormulaPlan.select record reference (preferred :: plans graph query)

theorem selectWithPreferred_of_available (graph : ObservedGraph S) (query : JointKernelQuery S)
    (preferred : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) (accepted : preferred.available record reference = true) :
    selectWithPreferred graph query preferred record reference = some preferred := by
  simp only [selectWithPreferred, ObservationalFormulaPlan.select, accepted, if_true]

/-- The preferred plan must itself have a certificate.  Acceptance alone is
not a soundness proof for an arbitrary action-free expression. -/
noncomputable def selectedWithPreferred_soundAt (model : FiniteHiddenDAGSCM S P)
    (query : JointKernelQuery S) (preferred : GuardedObservationalFormula P query.sourceTerm)
    (reference : S.Assignment) (chosen : ObservationalFormulaPlan S)
    (found : selectWithPreferred P.observedGraph query preferred.plan model.observationalDist reference = some chosen) :
    model.TermEquivalentAt query.sourceTerm chosen.formula reference :=
  GuardedObservationalFormula.select_plan_soundAt model reference (preferred :: catalogue P query)
    (preferred.plan :: plans P.observedGraph query)
    (by rw [List.map_cons, plans_certified]) chosen found
    (model.kernelSupportedAt_unconditional query.outcome query.action reference)

end BackdoorAdjustmentSearch
end Causality
end Thesis
