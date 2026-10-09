import Thesis.Causality.ValueRefinement

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Encoding ordinary binary SCMs on supplied finite observed alphabets

The difficult countermodel argument may be carried out on Boolean observed
values.  This module transports that ordinary binary SCM to the supplied
signature without changing node indices, directed parents, latent incidence,
factor records, or prior.  The two distinguished labels encode the bits;
declared parents are decoded before the original mechanism is called.

The encoded model is generally not positive on the full alphabet.  What it
does satisfy automatically is the exact parent-bit invariant and positive
decoded support needed by `ValueRefinement`.  The latter module's actual
private sweep subsequently fills the extra labels.  Separating deterministic
encoding from support refinement keeps the original binary model visible
and does not smuggle in an enlarged observed domain or a shared switch.

Every intervention on the supplied signature is covered by the decoded
evaluation theorem, even one using a label outside the distinguished pair.
Full-value encoding is stated only for factual evaluation: an intervention
at a third label must retain that actual label, not replace it by `first`.
-/

namespace ObservedSignature

/-- The same directed observed graph, with Boolean values at every node. -/
def binary (S : ObservedSignature.{0}) : ObservedSignature where
  count := S.count
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> decide
  value_nodup := fun _ => by decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := S.directed
  directed_earlier := S.directed_earlier

end ObservedSignature

/-- The bidirected graph is reindexed trivially because the node count and
topological order have not changed. -/
def ObservedGraph.binary (graph : ObservedGraph S) : ObservedGraph S.binary where
  bidirected := graph.bidirected
  bidirected_symmetric := graph.bidirected_symmetric
  bidirected_irreflexive := graph.bidirected_irreflexive

/-- Interpret a conditional query on the same graph with Boolean labels.
The original node sets and all three disjointness certificates are retained;
this operation neither promotes a conditioner nor restricts the outcome. -/
def ConditionalKernelQuery.binary (query : ConditionalKernelQuery S) : ConditionalKernelQuery S.binary where
  outcome := query.outcome
  action := query.action
  condition := query.condition
  action_outcome_disjoint := query.action_outcome_disjoint
  action_condition_disjoint := query.action_condition_disjoint
  outcome_condition_disjoint := query.outcome_condition_disjoint

namespace BinaryEncoding

open ObservedValueRefinement

/-- The supplied constructive section of the bit decoder. -/
def value (rich : ObservedSignature.ValueRich S) (node : Fin S.count) (input : Bool) : S.Value node :=
  if input then rich.second node else rich.first node

theorem bit_value (rich : ObservedSignature.ValueRich S) (node : Fin S.count) (input : Bool) :
    bit rich node (value rich node input) = input := by
  cases input
  · exact decide_eq_false (rich.different node)
  · exact decide_eq_true rfl

/-- Pointwise encoding retains dependent output value types. -/
def assignment (rich : ObservedSignature.ValueRich S) (sample : S.binary.Assignment) : S.Assignment :=
  fun node => value rich node (sample node)

theorem bits_assignment (rich : ObservedSignature.ValueRich S) (sample : S.binary.Assignment) :
    bits rich (assignment rich sample) = sample :=
  funext (fun node => bit_value rich node (sample node))

/-- Decode the *actual* forced label, including nonbinary labels. -/
def intervention (rich : ObservedSignature.ValueRich S)
    (target : (node : Fin S.count) -> Option (S.Value node)) :
    (node : Fin S.binary.count) -> Option Bool :=
  fun node => (target node).map (bit rich node)

/-- The unchanged latent coordinate data, now indexed by the supplied
signature.  No root is added by deterministic encoding. -/
def latent (source : LatentExtension S.binary) : LatentExtension S where
  count := source.count
  Value := source.Value
  valueEnumeration := source.valueEnumeration
  value_complete := source.value_complete
  valueDecidableEq := source.valueDecidableEq
  incident := source.incident

/-- An ordinary binary mechanism reads the decoded declared parents.  Its
latent inputs and all probability records are retained literally. -/
def model (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary) : ExactModel S where
  latent := latent base.latent
  factor := base.factor
  prior := base.prior
  product_law := base.product_law
  mechanism := fun child parents inputs => value rich child
    (base.mechanism child (fun parent edge => bit rich parent (parents parent edge)) inputs)

/-- Encoding introduces no new dependence on labels within a bit class. -/
theorem respectsParentBits (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary) :
    RespectsParentBits (model rich base) rich := by
  intro child first second inputs agree
  have decoded : (fun parent edge => bit rich parent (first parent edge)) =
      (fun parent edge => bit rich parent (second parent edge)) := by
    funext parent edge
    exact agree parent edge
  exact congrArg (fun parents => value rich child (base.mechanism child parents inputs)) decoded

/-- Both parts of graph compatibility are inherited from the ordinary
binary model.  Encoding does not manufacture a projected edge. -/
theorem compatible (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    {graph : ObservedGraph S} (member : Compatible base graph.binary) :
    Compatible (model rich base) graph :=
  ⟨member.1, member.2⟩

/-- Exact decoded evaluation under every intervention.  Forced labels are
decoded at the action, and free mechanisms decode every responding parent
before using the original binary equation. -/
theorem evalNodeUnder_bit (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (unit : base.latent.Assignment) (child : Fin S.count) :
    bit rich child ((model rich base).evalNodeUnder target unit child) =
      base.evalNodeUnder (intervention rich target) unit child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  cases selected : target child with
  | some forced =>
      simp only [FiniteLatentSCM.equationUnder, selected, intervention, Option.map_some]
  | none =>
      simp only [FiniteLatentSCM.equationUnder, selected, intervention, Option.map_none,
        model, bit_value]
      congr 1
      funext parent edge
      exact evalNodeUnder_bit rich base target unit parent
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem evalUnder_bits (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (target : (node : Fin S.count) -> Option (S.Value node)) (unit : base.latent.Assignment) :
    bits rich ((model rich base).evalUnder target unit) =
      base.evalUnder (intervention rich target) unit :=
  funext (evalNodeUnder_bit rich base target unit)

/-- Factual full values are the explicit encoding of the original binary
assignment.  This is the stronger equality used for whole-law transport. -/
theorem eval_eq_assignment (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (unit : base.latent.Assignment) :
    (model rich base).eval unit = assignment rich (base.eval unit) := by
  funext child
  change (model rich base).evalNodeUnder (FiniteLatentSCM.noIntervention S) unit child = _
  rw [FiniteLatentSCM.evalNodeUnder]
  simp only [FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention, model, assignment]
  have parents :
      (fun parent (_edge : S.directed parent child = true) => bit rich parent
        ((model rich base).evalNodeUnder (FiniteLatentSCM.noIntervention S) unit parent)) =
      (fun parent (_edge : S.directed parent child = true) => base.evalNodeUnder
        (FiniteLatentSCM.noIntervention S.binary) unit parent) := by
    funext parent edge
    exact evalNodeUnder_bit rich base (FiniteLatentSCM.noIntervention S) unit parent
  exact (congrArg (fun parents => value rich child (base.mechanism child parents
    (fun root _selected => unit root))) parents).trans (by
      congr 1
      change base.mechanism child _ _ = base.evalNodeUnder (FiniteLatentSCM.noIntervention S.binary) unit child
      rw [FiniteLatentSCM.evalNodeUnder]
      rfl)

/-- Compare whole observed events through the deterministic value encoding.
The original latent prior is unchanged, including its rational denominator. -/
theorem observationalValue (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (event : Event S.Assignment) :
    QProb.Equiv ((model rich base).observationalValue event)
      (base.observationalValue (fun sample => event (assignment rich sample))) := by
  exact QProb.equiv_trans ((model rich base).observationalValue_eq event)
    (QProb.equiv_trans (base.prior.probVal_congr _ _
      (fun unit => congrArg event (eval_eq_assignment rich base unit)))
      (QProb.equiv_symm (base.observationalValue_eq _)))

theorem observationally_equivalent (rich : ObservedSignature.ValueRich S)
    (left right : ExactModel S.binary) (equivalent : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (model rich left) (model rich right) := by
  intro event
  exact QProb.equiv_trans (observationalValue rich left event)
    (QProb.equiv_trans (equivalent (fun sample => event (assignment rich sample)))
      (QProb.equiv_symm (observationalValue rich right event)))

/-- Binary positivity becomes positivity of every decoded atom, even
though additional full labels still have zero probability before refinement. -/
theorem bitsPositive (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (positive : ObservationallyPositive base) : BitsPositive (model rich base) rich := by
  intro target
  have decoded := observationalValue rich base
    (fun sample => decide (bits (S := S) rich sample = bits (S := S) rich target))
  have compared := base.observationalDist.probVal_congr
    (fun sample => decide (bits (S := S) rich (assignment rich sample) = bits (S := S) rich target))
    (FiniteProbRecord.singletonEvent (bits (S := S) rich target)) (by
      intro sample
      exact congrArg (fun input => decide (input = bits (S := S) rich target))
        (bits_assignment rich sample))
  exact (QProb.equiv_num_pos_iff (QProb.equiv_trans decoded compared)).mpr (positive (bits (S := S) rich target))

/-- Bit-dependent intervention probabilities are exactly those of the
ordinary binary model at the decoded intervention. -/
theorem interventionalBitsValue (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (event : Event S.binary.Assignment) :
    QProb.Equiv ((model rich base).interventionalValue target (fun sample => event (bits (S := S) rich sample)))
      (base.interventionalValue (intervention rich target) event) := by
  exact QProb.equiv_trans ((model rich base).interventionalValue_eq target _)
    (QProb.equiv_trans (base.prior.probVal_congr _ _
      (fun unit => congrArg event (evalUnder_bits rich base target unit)))
      (QProb.equiv_symm (base.interventionalValue_eq _ _)))

end BinaryEncoding
end Causality
end Thesis
