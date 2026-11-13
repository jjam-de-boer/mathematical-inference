import Thesis.Causality.HedgeSelectionSearch
import Thesis.CausalTransport.HedgeCompensatedCounterexample

namespace Thesis
namespace Causality

open Probability

/-!
# Searching alternative hedges for positive original-query countermodels

The compensated countermodel construction already works whenever every
canonical readout vertex is small or outside the large forest.  An extracted
hedge need not have that property, and outcome-ancestral normalization need
not have a connected small set.  Neither failure excludes a different valid
hedge for the *same* query.

Here the geometric requirement is an exact finite Boolean test.  The search
from `HedgeSelectionSearch` tries alternative large sets, small sets, and
kept maps before stopping at a candidate that meets it.  A successful search
therefore supplies actual positive compatible SCMs with equal observational
laws and different original-query kernels, not merely promising forest data.

The final coverage boundary is deliberately structural.  If every input
hedge admits some route-ready selection, the finite scan turns that
propositional existence into countermodel data without choice.  However,
`Thesis.Examples.HedgeCarrierRouteObstruction` proves that this coverage is
not true for every graph: a valid hedge can have no route-ready alternative.
The compensated family therefore needs a further construction, rather than
an assumed universal success theorem for this search.  The search considers all
forest selections in its host, but still uses the existing canonical route
policy and compensated carrier family, not every conceivable countermodel.
-/

/-! ## An exact Boolean form of the compensated routing requirement -/

section Routing

variable {S : ObservedSignature} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- Check every observed coordinate: a routed coordinate must belong to the
small forest or lie outside the large forest.  The test includes internal
small vertices and does not require them to be kept sinks. -/
def HedgeWitness.carrierRoutesReady (w : HedgeWitness G q) : Bool :=
  finAll S.count (fun node =>
    if w.rootReadoutNodes node then w.small node || !w.large node else true)

/-- The executable test is exactly the hypothesis of the existing positive
compensated constructor.  Only finite Boolean cases are used. -/
theorem HedgeWitness.carrierRoutesReady_iff (w : HedgeWitness G q) :
    w.carrierRoutesReady = true ↔
      forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false := by
  constructor
  · intro ready node routed
    have atNode := (finAll_eq_true_iff _).mp ready node
    have alternatives : w.small node = true ∨ (!w.large node) = true := by
      apply Bool.or_eq_true_iff.mp
      simpa [routed] using atNode
    cases alternatives with
    | inl small => exact .inl small
    | inr outside =>
        apply Or.inr
        cases selected : w.large node with
        | false => rfl
        | true => simp [selected] at outside
  · intro allowed
    apply (finAll_eq_true_iff _).mpr
    intro node
    cases routed : w.rootReadoutNodes node with
    | false => simp
    | true =>
        cases allowed node routed with
        | inl small => simp [small]
        | inr outside => simp [outside]

/-- Invalid forest data is rejected before constructing a typed witness.
On valid data the route test is run on the very witness used by the
countermodel constructor, avoiding an unproved comparison of route policies. -/
def hedgeCarrierRoutesReady (G : ObservedGraph S) (q : JointKernelQuery S)
    (selection : HedgeSelection S) : Bool :=
  if valid : hedgeTestsHold G q selection = true then
    (hedgeWitness_of_sets G q selection valid).carrierRoutesReady
  else false

/-- On a checked selection, readiness supplies its actual canonical routing
hypothesis.  The proof of the hedge tests is irrelevant to the resulting
finite route computation. -/
theorem hedgeCarrierRoutesReady_iff
    (G : ObservedGraph S) (q : JointKernelQuery S) (selection : HedgeSelection S)
    (valid : hedgeTestsHold G q selection = true) :
    hedgeCarrierRoutesReady G q selection = true ↔
      forall node, (hedgeWitness_of_sets G q selection valid).rootReadoutNodes node = true ->
        selection.small node = true ∨ selection.large node = false := by
  simpa [hedgeCarrierRoutesReady, valid] using
    (hedgeWitness_of_sets G q selection valid).carrierRoutesReady_iff

/-! ## Distinguishing a route-policy failure from a geometric obstruction -/

/-- A more permissive check than inspecting the canonical readout: each
common root may use *any* directed path to *any* queried outcome, provided
that it never enters `large \ small` or the original action.  Extra incoming
cuts implement that avoidance in the finite reachability search.  For valid
hedge data, the common roots are already small and unintervened, so no
avoided starting vertex is admitted by a reflexive path.  The check does not
itself construct the current compensated readout plan, whose route
policy remains fixed; it is useful for detecting genuine geometric failures. -/
def hedgeCarrierRoutesPossible (q : JointKernelQuery S) (selection : HedgeSelection S) : Bool :=
  (NodeSet.members (keptSinks selection.large selection.child)).all (fun root =>
    (NodeSet.members q.outcome).any (fun outcome =>
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S (NodeSet.union q.action (NodeSet.diff selection.large selection.small)))
        S.count root outcome))

/-- Reflect the permissive check to arbitrary inductive paths in the
incoming-cut graph with outer-only vertices also cut.  The existential stays
in `Prop`; its reverse implication reflects each supplied path to finite
reachability and never chooses a route into `Type`. -/
theorem hedgeCarrierRoutesPossible_iff (q : JointKernelQuery S) (selection : HedgeSelection S) :
    hedgeCarrierRoutesPossible q selection = true ↔
      forall root, keptSinks selection.large selection.child root = true ->
        Exists fun outcome => q.outcome outcome = true ∧
          DirectedReachableBy S
            (fun parent child => mutilatedDirected S
              (NodeSet.union q.action (NodeSet.diff selection.large selection.small)) parent child = true)
            root outcome := by
  constructor
  · intro possible root selected
    have reaches := (List.all_eq_true.mp possible) root
      ((NodeSet.mem_members_iff _ root).mpr selected)
    rcases List.any_eq_true.mp reaches with ⟨outcome, member, path⟩
    exact ⟨outcome, (NodeSet.mem_members_iff q.outcome outcome).mp member,
      directedReachableBy_of_within _ path⟩
  · intro paths
    apply List.all_eq_true.mpr
    intro root member
    rcases paths root ((NodeSet.mem_members_iff _ root).mp member) with ⟨outcome, selected, path⟩
    exact List.any_eq_true.mpr ⟨outcome, (NodeSet.mem_members_iff q.outcome outcome).mpr selected,
      finiteWithin_of_directedReachableBy path⟩

/-- A checked hedge together with the exact compensated routing guarantee.
Its forest may differ completely from a witness that motivated the search;
the graph, action, and queried outcome remain unchanged. -/
structure CarrierRouteHedgeWitness (G : ObservedGraph S) (q : JointKernelQuery S) where
  witness : HedgeWitness G q
  routes_allowed : forall node, witness.rootReadoutNodes node = true ->
    witness.small node = true ∨ witness.large node = false

/-- Construct the typed package directly from successful finite tests. -/
def CarrierRouteHedgeWitness.ofSelection
    (G : ObservedGraph S) (q : JointKernelQuery S) (selection : HedgeSelection S)
    (valid : hedgeTestsHold G q selection = true)
    (ready : hedgeCarrierRoutesReady G q selection = true) : CarrierRouteHedgeWitness G q where
  witness := hedgeWitness_of_sets G q selection valid
  routes_allowed := (hedgeCarrierRoutesReady_iff G q selection valid).mp ready

/-- Search every hedge selection inside the supplied host, testing carrier
routing before accepting a leaf.  No original child map or small set is fixed. -/
def findCarrierRouteHedgeSelection (G : ObservedGraph S) (q : JointKernelQuery S)
    (host : NodeSet S) : Option (HedgeSelection S) :=
  findHedgeSelectionWhere G q host (hedgeCarrierRoutesReady G q)

/-- Every found selection is both a hedge and a usable compensated carrier
geometry.  Later alternatives are checked just as thoroughly as earlier ones. -/
theorem findCarrierRouteHedgeSelection_tests
    (G : ObservedGraph S) (q : JointKernelQuery S) (host : NodeSet S)
    {selection : HedgeSelection S}
    (result : findCarrierRouteHedgeSelection G q host = some selection) :
    hedgeTestsHold G q selection = true ∧ hedgeCarrierRoutesReady G q selection = true :=
  findHedgeSelectionWhere_tests G q host (hedgeCarrierRoutesReady G q) result

/-- Any supplied contained route-ready hedge guarantees a successful scan.
The scan is not required to return that particular candidate. -/
theorem findCarrierRouteHedgeSelection_eq_some_of_selection
    (G : ObservedGraph S) (q : JointKernelQuery S) (host : NodeSet S)
    (selection : HedgeSelection S) (contained : NodeSet.Subset selection.large host)
    (valid : hedgeTestsHold G q selection = true)
    (ready : hedgeCarrierRoutesReady G q selection = true) :
    Exists fun found => findCarrierRouteHedgeSelection G q host = some found :=
  findHedgeSelectionWhere_eq_some_of_selection G q host (hedgeCarrierRoutesReady G q)
    selection contained valid ready

/-- Executable typed extraction.  `none` means that no selection inside this
host passed the hedge and canonical-routing tests, not that the query is
identifiable or that every possible countermodel construction fails. -/
def carrierRouteHedgeWitness? (G : ObservedGraph S) (q : JointKernelQuery S)
    (host : NodeSet S) : Option (CarrierRouteHedgeWitness G q) :=
  match found : findCarrierRouteHedgeSelection G q host with
  | none => none
  | some selection =>
      let tests := findCarrierRouteHedgeSelection_tests G q host found
      some (CarrierRouteHedgeWitness.ofSelection G q selection tests.1 tests.2)

/-- Selection completeness also holds at the typed extraction boundary. -/
theorem carrierRouteHedgeWitness?_eq_some_of_selection
    (G : ObservedGraph S) (q : JointKernelQuery S) (host : NodeSet S)
    (selection : HedgeSelection S) (contained : NodeSet.Subset selection.large host)
    (valid : hedgeTestsHold G q selection = true)
    (ready : hedgeCarrierRoutesReady G q selection = true) :
    Exists fun found => carrierRouteHedgeWitness? G q host = some found := by
  rcases findCarrierRouteHedgeSelection_eq_some_of_selection G q host selection
    contained valid ready with ⟨found, result⟩
  refine ⟨CarrierRouteHedgeWitness.ofSelection G q found
    (findCarrierRouteHedgeSelection_tests G q host result).1
    (findCarrierRouteHedgeSelection_tests G q host result).2, ?_⟩
  unfold carrierRouteHedgeWitness?
  split
  · next absent => rw [result] at absent; cases absent
  · next candidate candidateResult =>
      have same : candidate = found := Option.some.inj (candidateResult.symm.trans result)
      subst candidate
      rfl

/-- Turn propositional structural existence into concrete forest data by
matching the finite search result.  The existential is eliminated only in
the impossible `none` branch, whose target is `False`; no witness is chosen
from a proposition into `Type`. -/
def carrierRouteHedgeWitnessOfSelectionExists
    (G : ObservedGraph S) (q : JointKernelQuery S) (host : NodeSet S)
    (coverage : Exists fun selection : HedgeSelection S =>
      NodeSet.Subset selection.large host ∧ hedgeTestsHold G q selection = true ∧
        hedgeCarrierRoutesReady G q selection = true) : CarrierRouteHedgeWitness G q :=
  match found : carrierRouteHedgeWitness? G q host with
  | some witness => witness
  | none => False.elim (by
      rcases coverage with ⟨selection, contained, valid, ready⟩
      rcases carrierRouteHedgeWitness?_eq_some_of_selection G q host selection
        contained valid ready with ⟨witness, result⟩
      rw [found] at result
      cases result)

end Routing

/-! ## Actual positive countermodels and the universal coverage boundary -/

section Countermodels

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- A successful geometric search supplies every semantic counterexample
field through the already proved compensated carrier theorem. -/
noncomputable def CarrierRouteHedgeWitness.positiveCounterexample
    (selected : CarrierRouteHedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  selected.witness.positiveCounterexampleOfSmallOrOutsideCarrierFlow rich selected.routes_allowed

/-- Sufficient finite structural coverage for the general positive hedge
leaf on a particular graph.  It is not an axiom and is not true for every
graph: the checked obstruction regression refutes it on a seven-node graph.
Success on one normalization or on selected examples is not enough. -/
def CarrierRouteHedgeCoverage (G : ObservedGraph S) : Prop :=
  forall query, HedgeWitness G query ->
    Exists fun selection : HedgeSelection S => hedgeTestsHold G query selection = true ∧
      hedgeCarrierRoutesReady G query selection = true

/-- A valid original-query hedge whose full-graph scan fails refutes this
particular coverage strategy.  The candidate-completeness theorem rules out
every alternative forest selection, not only the extracted witness.  This
does not assert that the query has no countermodel in another family. -/
theorem not_carrierRouteHedgeCoverage_of_search_none
    (G : ObservedGraph S) (query : JointKernelQuery S) (hedge : HedgeWitness G query)
    (absent : findCarrierRouteHedgeSelection G query NodeSet.full = none) :
    Not (CarrierRouteHedgeCoverage G) := by
  intro coverage
  rcases coverage query hedge with ⟨selection, valid, ready⟩
  rcases findCarrierRouteHedgeSelection_eq_some_of_selection G query NodeSet.full selection
    (fun _node _selected => rfl) valid ready with ⟨found, result⟩
  rw [absent] at result
  cases result

/-- Reduce the universal semantic hedge leaf to the explicit graph-only
coverage theorem.  Search is over the full observed graph, so the alternative
is not required to remain inside the original hedge's large set.  Positivity,
observational equality, and original-query separation are proved by the
countermodel constructor, not included in the coverage premise. -/
noncomputable def positiveHedgeCounterexampleOfCarrierRouteCoverage
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (coverage : CarrierRouteHedgeCoverage G) (query : JointKernelQuery S)
    (hedge : HedgeWitness G query) : CounterexampleIn (GraphModelClass.positive G) query :=
  (carrierRouteHedgeWitnessOfSelectionExists G query NodeSet.full (by
    rcases coverage query hedge with ⟨selection, valid, ready⟩
    exact ⟨selection, fun _node _selected => rfl, valid, ready⟩)).positiveCounterexample rich

end Countermodels

end Causality
end Thesis
