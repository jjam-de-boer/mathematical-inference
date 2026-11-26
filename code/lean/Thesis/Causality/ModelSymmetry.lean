import Thesis.Causality.FiniteSymmetry
import Thesis.CausalTransport.HiddenDAGModel

namespace Thesis.Causality.FiniteSymmetry
open Probability

/-!
# Local structural transports imply interventional equivariance

The data below concern node and value names, primitive response functions,
and the exogenous probability law. Equality of observed or interventional
laws is a theorem, never a structure field. In particular, an intervention
is transported with the value labels: keeping its old setting while flipping
the outcome labels would describe a different, stronger experiment symmetry.

The node bijection can change the numerical topological order. The recursive
proof follows the *source* node order and uses only source parent edges;
there is no unjustified assumption that a renaming preserves index values.
-/

variable {S T : ObservedSignature.{0}}

/-- A structural isomorphism of two finite causal presentations. The
`mechanisms` field checks every local parent input and every exogenous state,
including configurations with observational mass zero. The only probability
premise, `prior`, concerns the exogenous draw before causal execution. -/
structure ModelTransport (left : ExactModel S) (right : ExactModel T) where
  nodes : ValueEquivalence (Fin S.count) (Fin T.count)
  values : (node : Fin S.count) →
    ValueEquivalence (S.Value node) (T.Value (nodes.forward node))
  assignments : ValueEquivalence S.Assignment T.Assignment
  assignment_at : ∀ state node,
    assignments.forward state (nodes.forward node) = (values node).forward (state node)
  interventions : ValueEquivalence (HardIntervention S) (HardIntervention T)
  forced : ∀ action node,
    (interventions.forward action).value (nodes.forward node) =
      (action.value node).map (values node).forward
  units : ValueEquivalence left.latent.Assignment right.latent.Assignment
  directed : ∀ parent child,
    T.directed (nodes.forward parent) (nodes.forward child) = S.directed parent child
  bidirected : ∀ first second,
    right.observedGraph.bidirected (nodes.forward first) (nodes.forward second) =
      left.observedGraph.bidirected first second
  prior : ∀ event,
    QProb.Equiv (right.prior.probVal event)
      (left.prior.probVal (fun unit => event (units.forward unit)))
  mechanisms : ∀ child (source : S.ParentValues child)
    (target : T.ParentValues (nodes.forward child)) (unit : left.latent.Assignment),
    (∀ parent (sourceEdge : S.directed parent child = true)
      (targetEdge : T.directed (nodes.forward parent) (nodes.forward child) = true),
      (values parent).forward (source parent sourceEdge) =
        target (nodes.forward parent) targetEdge) →
    (values child).forward
      (left.mechanism child source (fun root _ => unit root)) =
    right.mechanism (nodes.forward child) target
      (fun root _ => units.forward unit root)

namespace ModelTransport
variable {left : ExactModel S} {right : ExactModel T}

/-- Every transported execution agrees at the corresponding node. At an
intervened node this is precisely `forced`; at a responding node it follows
from the independently checked local mechanism relation and the already
transported parent responses. -/
theorem evalNode (transport : ModelTransport left right)
    (action : HardIntervention S) (unit : left.latent.Assignment)
    (child : Fin S.count) :
    (transport.values child).forward (left.evalNodeUnder action.value unit child) =
      right.evalNodeUnder (transport.interventions.forward action).value
        (transport.units.forward unit) (transport.nodes.forward child) := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  have forced := transport.forced action child
  cases selected : action.value child with
  | some value =>
      simp only [selected, Option.map_some] at forced
      simp only [FiniteLatentSCM.equationUnder, selected, forced]
  | none =>
      simp only [selected, Option.map_none] at forced
      simp only [FiniteLatentSCM.equationUnder, selected, forced]
      apply transport.mechanisms
      intro parent sourceEdge targetEdge
      exact transport.evalNode action unit parent
termination_by child.val
decreasing_by exact S.directed_earlier sourceEdge

/-- The coordinate theorem gives equality of complete assignments. The
surjectivity needed to visit every target coordinate comes from the explicit
node inverse, without choosing representatives from a finite existential. -/
theorem eval (transport : ModelTransport left right)
    (action : HardIntervention S) (unit : left.latent.Assignment) :
    transport.assignments.forward (left.evalUnder action.value unit) =
      right.evalUnder (transport.interventions.forward action).value
        (transport.units.forward unit) := by
  funext target
  have node := transport.nodes.forward_backward target
  rw [← node, transport.assignment_at]
  exact transport.evalNode action unit (transport.nodes.backward target)

/-- Full interventional equivariance, including all zero-mass events. Both
the action and event presentation are changed. No conditional probability is
completed and no graphical identification theorem is invoked. -/
theorem interventionalValue (transport : ModelTransport left right)
    (action : HardIntervention S) (event : Event T.Assignment) :
    QProb.Equiv
      (right.interventionalValue (transport.interventions.forward action).value event)
      (left.interventionalValue action.value
        (fun state => event (transport.assignments.forward state))) :=
  QProb.equiv_trans (right.interventionalValue_eq _ _)
    (QProb.equiv_trans (transport.prior _)
      (QProb.equiv_trans (left.prior.probVal_congr _ _ (fun unit =>
        congrArg event (transport.eval action unit).symm))
        (QProb.equiv_symm (left.interventionalValue_eq _ _))))

/-- A structural symmetry of one model fixes an experiment only when it
also fixes the complete hard setting. This is an additional local equation
on intervention labels, stronger than having a model isomorphism. -/
def FixesExperiment (symmetry : ModelTransport left left)
    (action : HardIntervention S) : Prop :=
  symmetry.interventions.forward action = action

/-- At a fixed experiment, full equivariance specializes to invariance of
that one interventional law. The hypothesis concerns the hard setting,
rather than assuming the resulting law equation that is to be proved. -/
theorem fixed_interventionalValue (symmetry : ModelTransport left left)
    (action : HardIntervention S) (fixed : symmetry.FixesExperiment action)
    (event : Event S.Assignment) :
    QProb.Equiv (left.interventionalValue action.value event)
      (left.interventionalValue action.value
        (fun state => event (symmetry.assignments.forward state))) := by
  have result := symmetry.interventionalValue action event
  rw [fixed] at result
  exact result

end ModelTransport

/-- A supplied finite group acts on hypotheses and on their experimental
interface. Local structural transports connect the actual mechanisms at
`h` and `g·h`; the action laws ensure that successive renamings of hypotheses,
assignments and interventions compose consistently. Different hypotheses may
have different latent domains and different projected confounding graphs. -/
structure ModelFamilyAction (G : Group) (H : Type) (S : ObservedSignature.{0}) where
  hypotheses : Action G H
  outcomes : Action G S.Assignment
  experiments : Action G (HardIntervention S)
  models : H → ExactModel S
  transport : ∀ g h, ModelTransport (models h) (models (hypotheses.act g h))
  outcomes_agree : ∀ g h state,
    (transport g h).assignments.forward state = outcomes.act g state
  experiments_agree : ∀ g h action,
    (transport g h).interventions.forward action = experiments.act g action

namespace ModelFamilyAction

/-- The family-level experimental law is derived from local transports.
The equation permits a symmetric prior on individually asymmetric models:
the renamed hypothesis on the left need not equal the original hypothesis. -/
theorem interventionalValue (family : ModelFamilyAction G H S)
    (g : G.Carrier) (h : H) (action : HardIntervention S)
    (event : Event S.Assignment) :
    QProb.Equiv
      ((family.models (family.hypotheses.act g h)).interventionalValue
        (family.experiments.act g action).value event)
      ((family.models h).interventionalValue action.value
        (fun state => event (family.outcomes.act g state))) := by
  have result := (family.transport g h).interventionalValue action event
  simpa only [family.experiments_agree, family.outcomes_agree] using result

/-- A concrete experimental observation has the same likelihood after its
hypothesis, intervention and event are all renamed. The event predicate uses
the inverse outcome action because it recognizes the image of the original
event. This is the generative ingredient needed by Bayesian data transport;
it is derived here from the local mechanisms and source law. -/
theorem eventLikelihood (family : ModelFamilyAction G H S)
    (g : G.Carrier) (h : H) (action : HardIntervention S)
    (event : Event S.Assignment) :
    QProb.Equiv
      ((family.models (family.hypotheses.act g h)).interventionalValue
        (family.experiments.act g action).value
        (fun state => event (family.outcomes.act (G.inv g) state)))
      ((family.models h).interventionalValue action.value event) := by
  have transported := family.interventionalValue g h action
    (fun state => event (family.outcomes.act (G.inv g) state))
  have predicate :
      (fun state => event (family.outcomes.act (G.inv g) (family.outcomes.act g state))) = event := by
    funext state
    rw [family.outcomes.inv_act]
  rw [predicate] at transported
  exact transported

end ModelFamilyAction

/-- A fully coherent family also records group actions on primitive node,
value and exogenous names. The packed exogenous carrier allows hypotheses
to have different latent domains: the group acts on `(hypothesis, unit)`
rather than pretending that all models have the same noise alphabet.

The underlying `ModelFamilyAction` already suffices for whole-law transport.
These extra equations are useful when composing symbolic model edits or
reusing a symmetry as a structural certificate: repeated relabellings now
agree on primitive names as well as on the experimental predictions. -/
structure CoherentModelFamilyAction (G : Group) (H : Type)
    (S : ObservedSignature.{0}) where
  family : ModelFamilyAction G H S
  signature : SignatureAction G S
  assignments : signature.AssignmentCompatible family.outcomes
  nodes_agree : ∀ g h node,
    (family.transport g h).nodes.forward node = signature.nodes.act g node
  values_agree : ∀ g h node value,
    signature.values.act g ⟨node, value⟩ =
      ⟨(family.transport g h).nodes.forward node,
        ((family.transport g h).values node).forward value⟩
  noise : Action G (Sigma fun h : H => (family.models h).latent.Assignment)
  noise_agree : ∀ g h unit,
    noise.act g ⟨h, unit⟩ =
      ⟨family.hypotheses.act g h, (family.transport g h).units.forward unit⟩

namespace CoherentModelFamilyAction

/-- The actual directed graph is transported by the declared node action.
The signature retains its chosen topological indexing; no graph with an
invalid numerical ordering is manufactured by a raw permutation. -/
theorem directed (coherent : CoherentModelFamilyAction G H S)
    (g : G.Carrier) (h : H) (parent child : Fin S.count) :
    S.directed (coherent.signature.nodes.act g parent)
      (coherent.signature.nodes.act g child) = S.directed parent child := by
  rw [← coherent.nodes_agree g h parent, ← coherent.nodes_agree g h child]
  exact (coherent.family.transport g h).directed parent child

/-- Hypotheses may have distinct confounding graphs. Group closure means
their adjacency tables are relabelled consistently, not that every atom is
individually invariant under the prior's symmetries. -/
theorem bidirected (coherent : CoherentModelFamilyAction G H S)
    (g : G.Carrier) (h : H) (first second : Fin S.count) :
    (coherent.family.models (coherent.family.hypotheses.act g h)).observedGraph.bidirected
      (coherent.signature.nodes.act g first) (coherent.signature.nodes.act g second) =
      (coherent.family.models h).observedGraph.bidirected first second := by
  rw [← coherent.nodes_agree g h first, ← coherent.nodes_agree g h second]
  exact (coherent.family.transport g h).bidirected first second

end CoherentModelFamilyAction
end Thesis.Causality.FiniteSymmetry
