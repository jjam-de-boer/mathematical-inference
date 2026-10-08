import Thesis.CausalTransport.ConditionalReadoutCounterexample

namespace Thesis
namespace Causality

open Probability

/-!
# Conditional countermodels along arbitrary finite observed-arrow routes

`ConditionalReadoutCounterexample` carries a genuine conditional gap through
one declared arrow.  Repeating that adapter manually is not a proof for an
arbitrary path: every replacement must also leave the next mechanism ready.
This module supplies the finite induction and transports that invariant.

The route is explicit data in `Type`, not a path selected from an existence
proposition.  Its arrows already impose strict topological order.  Only the
initial pair must ignore the readout destinations; every intermediate pair's
non-influence proof follows from the earlier-replacement theorem.  At each
step finite cell search derives a fresh separated reference from the actual
current pair.  Different steps may therefore reserve different observed
labels, have different posterior denominators, and use different supported
biased private noise records.

The complete action and conditioner are retained throughout.  Destinations
must avoid both sets, and the last vertex must be an original queried outcome.
Additional outcomes are restored by the conditional marginal adapter.  The
empty route is included and uses the unchanged seed pair.  No bounded number
of arrows, Boolean observed alphabet, common denominator, or supplied final
kernel gap is assumed.

These are semantic directed-route constructors, not the universal terminal
countermodel theorem.  An arbitrary active path may also contain latent-pair
edges, activated colliders, or destinations that are not ignored by the seed
pair.  Those obligations are not disguised as consequences of this induction.
-/

variable {S : ObservedSignature.{0}}

namespace ConditionalReadout

/-! ## Actual one-step models retain later non-influence -/

/-- Both models returned by the real one-arrow adapter still ignore an
initially ignored later vertex.  The internally searched reference affects
the readout labels, but cannot create a backward parent edge.  This theorem
concerns the constructed models themselves, not an independently supplied
pair with the same conditional probabilities. -/
theorem ofIncomingParentWithNoise_otherMechanismsIgnore_of_earlier
    {graph : ObservedGraph S} (source target : ConditionalKernelQuery S)
    (counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) source)
    (rich : ObservedSignature.ValueRich S) (parent pivot : Fin S.count)
    (sourceOutcome : source.outcome = NodeSet.singleton parent)
    (targetSelected : target.outcome pivot = true)
    (action : source.action = target.action) (condition : source.condition = target.condition)
    (edge : S.directed parent pivot = true)
    (leftIgnored : counterexample.left.OtherMechanismsIgnore pivot)
    (rightIgnored : counterexample.right.OtherMechanismsIgnore pivot)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap)
    (later : Fin S.count) (leftLater : counterexample.left.OtherMechanismsIgnore later)
    (rightLater : counterexample.right.OtherMechanismsIgnore later)
    (earlier : pivot.val < later.val) :
    let routed := ofIncomingParentWithNoise source target counterexample rich parent pivot
      sourceOutcome targetSelected action condition edge leftIgnored rightIgnored
      noise noisePositive gap positiveGap bias
    routed.left.OtherMechanismsIgnore later ∧ routed.right.OtherMechanismsIgnore later := by
  constructor
  · exact counterexample.left.withHedgeReadout_otherMechanismsIgnore_of_earlier
      _ pivot later noise false _ leftLater earlier
  · exact counterexample.right.withHedgeReadout_otherMechanismsIgnore_of_earlier
      _ pivot later noise false _ rightLater earlier

/-! ## Finite route data and its inherited order -/

/-- An observed directed route, including its starting and final vertices.
Each nonempty constructor records one actual declared arrow.  There is no
separate ordered-list hypothesis: the signature orders every such arrow. -/
inductive Route (S : ObservedSignature.{0}) : Fin S.count -> Fin S.count -> Type
  | refl (node : Fin S.count) : Route S node node
  | step {parent pivot endpoint : Fin S.count}
      (edge : S.directed parent pivot = true) (tail : Route S pivot endpoint) :
      Route S parent endpoint

/-- Exactly the vertices whose mechanisms will be replaced.  The source is
not replaced solely for being the source, and an empty route replaces none. -/
def Route.destinations {parent endpoint : Fin S.count} : Route S parent endpoint -> List (Fin S.count)
  | .refl _ => []
  | .step (pivot := pivot) _ tail => pivot :: tail.destinations

/-- Every destination occurs strictly after the current source.  Applying
this to the tail is exactly the invariant needed after the first update. -/
theorem Route.source_lt_destination {parent endpoint : Fin S.count}
    (route : Route S parent endpoint) (node : Fin S.count)
    (listed : node ∈ route.destinations) : parent.val < node.val := by
  induction route with
  | refl => cases listed
  | @step parent pivot endpoint edge tail inductionHypothesis =>
      rcases List.mem_cons.mp listed with same | rest
      · subst node
        exact S.directed_earlier edge
      · exact Nat.lt_trans (S.directed_earlier edge) (inductionHypothesis rest)

/-- The singleton query at an intermediate vertex keeps the original full
action and conditioner.  Its exclusions are supplied by route readiness,
not inferred from the existence of a directed arrow. -/
private def singletonQuery (context : ConditionalKernelQuery S) (node : Fin S.count)
    (unacted : context.action node = false) (ungiven : context.condition node = false) :
    ConditionalKernelQuery S where
  outcome := NodeSet.singleton node
  action := context.action
  condition := context.condition
  action_outcome_disjoint := by
    intro other acted
    cases selected : NodeSet.singleton node other with
    | false => rfl
    | true =>
        have same := (NodeSet.singleton_eq_true_iff node other).mp selected
        subst other
        rw [unacted] at acted
        cases acted
  action_condition_disjoint := context.action_condition_disjoint
  outcome_condition_disjoint := by
    intro other selected
    rw [(NodeSet.singleton_eq_true_iff node other).mp selected]
    exact ungiven

/-! ## Constructive conditional transport at arbitrary route length -/

/-- Carry a genuine positive singleton-outcome countermodel through every
arrow of the explicit route.  Readiness is checked only on the seed models.
The induction installs actual private-noise mechanisms, derives each new
conditional gap by finite cell search, and preserves readiness for the tail.
The target may contain further outcomes, which are retained in the result.
Noise support and bias are required only at actual route destinations; unused
noise records are unrestricted, including for the empty route. -/
noncomputable def ofRouteWithNoise {graph : ObservedGraph S}
    (source target : ConditionalKernelQuery S)
    (counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) source)
    (rich : ObservedSignature.ValueRich S) {parent endpoint : Fin S.count}
    (route : Route S parent endpoint)
    (sourceOutcome : source.outcome = NodeSet.singleton parent)
    (targetSelected : target.outcome endpoint = true)
    (action : source.action = target.action) (condition : source.condition = target.condition)
    (unacted : forall node, node ∈ route.destinations -> target.action node = false)
    (ungiven : forall node, node ∈ route.destinations -> target.condition node = false)
    (leftIgnored : forall node, node ∈ route.destinations -> counterexample.left.OtherMechanismsIgnore node)
    (rightIgnored : forall node, node ∈ route.destinations -> counterexample.right.OtherMechanismsIgnore node)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (noisePositive : forall node, node ∈ route.destinations ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : (node : Fin S.count) -> Nat)
    (positiveGap : forall node, node ∈ route.destinations -> 0 < gap node)
    (bias : forall node, node ∈ route.destinations ->
      FiniteProbRecord.eventMass (noise node).atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass (noise node).atoms id + gap node) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) target := by
  induction route generalizing source with
  | refl node =>
      have subset : NodeSet.Subset (NodeSet.singleton node) target.outcome :=
        NodeSet.singleton_subset_of_mem targetSelected
      have same : source = target.restrictOutcome (NodeSet.singleton node) subset := by
        cases source
        cases target
        cases sourceOutcome
        cases action
        cases condition
        rfl
      exact ConditionalCounterexampleIn.ofRestrictedOutcome (C := GraphModelClass.positive graph)
        (fun member => member.2)
        target (NodeSet.singleton node) subset (same ▸ counterexample)
  | @step parent pivot endpoint edge tail inductionHypothesis =>
      let intermediate := singletonQuery target pivot
        (unacted pivot List.mem_cons_self) (ungiven pivot List.mem_cons_self)
      let routed := ofIncomingParentWithNoise source intermediate counterexample rich parent pivot
        sourceOutcome ((NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl) action condition edge
        (leftIgnored pivot List.mem_cons_self) (rightIgnored pivot List.mem_cons_self)
        (noise pivot) (noisePositive pivot List.mem_cons_self) (gap pivot)
        (positiveGap pivot List.mem_cons_self) (bias pivot List.mem_cons_self)
      have tailIgnored (node : Fin S.count) (listed : node ∈ tail.destinations) :
          routed.left.OtherMechanismsIgnore node ∧ routed.right.OtherMechanismsIgnore node :=
        ofIncomingParentWithNoise_otherMechanismsIgnore_of_earlier source intermediate counterexample
          rich parent pivot sourceOutcome ((NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl)
          action condition edge (leftIgnored pivot List.mem_cons_self) (rightIgnored pivot List.mem_cons_self)
          (noise pivot) (noisePositive pivot List.mem_cons_self) (gap pivot)
          (positiveGap pivot List.mem_cons_self) (bias pivot List.mem_cons_self) node
          (leftIgnored node (List.mem_cons_of_mem pivot listed))
          (rightIgnored node (List.mem_cons_of_mem pivot listed))
          (tail.source_lt_destination node listed)
      exact inductionHypothesis intermediate routed rfl targetSelected rfl rfl
        (fun node listed => unacted node (List.mem_cons_of_mem pivot listed))
        (fun node listed => ungiven node (List.mem_cons_of_mem pivot listed))
        (fun node listed => (tailIgnored node listed).1)
        (fun node listed => (tailIgnored node listed).2)
        (fun node listed => noisePositive node (List.mem_cons_of_mem pivot listed))
        (fun node listed => positiveGap node (List.mem_cons_of_mem pivot listed))
        (fun node listed => bias node (List.mem_cons_of_mem pivot listed))

/-- The arbitrary-length route with explicit supported `2:1` stay/flip
noise at each destination.  This convenience constructor retains the same
initial readiness hypotheses; it supplies neither a chosen route nor an
assumed final separation, and does not limit the observed value alphabets. -/
noncomputable def ofRoute {graph : ObservedGraph S}
    (source target : ConditionalKernelQuery S)
    (counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) source)
    (rich : ObservedSignature.ValueRich S) {parent endpoint : Fin S.count}
    (route : Route S parent endpoint)
    (sourceOutcome : source.outcome = NodeSet.singleton parent)
    (targetSelected : target.outcome endpoint = true)
    (action : source.action = target.action) (condition : source.condition = target.condition)
    (unacted : forall node, node ∈ route.destinations -> target.action node = false)
    (ungiven : forall node, node ∈ route.destinations -> target.condition node = false)
    (leftIgnored : forall node, node ∈ route.destinations -> counterexample.left.OtherMechanismsIgnore node)
    (rightIgnored : forall node, node ∈ route.destinations -> counterexample.right.OtherMechanismsIgnore node) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) target :=
  ofRouteWithNoise source target counterexample rich route sourceOutcome targetSelected action condition
    unacted ungiven leftIgnored rightIgnored (fun _ => FiniteProbRecord.biasedFlip 1 1 (by decide))
    (by intro node listed bit; dsimp only; cases bit <;> decide +kernel)
    (fun _ => 1) (by intro node listed; change 0 < 1; decide)
    (by intro node listed; dsimp only; decide +kernel)

end ConditionalReadout
end Causality
end Thesis
