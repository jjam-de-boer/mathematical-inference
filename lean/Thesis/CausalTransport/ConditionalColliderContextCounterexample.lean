import Thesis.CausalTransport.ConditionalColliderCounterexample
import Thesis.CausalTransport.ConditionalMarginalization

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Incoming-parent collider countermodels with retained conditioning context

The earlier singleton kernel bridge observes only the modified child.  A
multi-root hedge needs the other roots fixed at the actual context selected
by conditional uniqueness.  The construction below therefore retains a full
observed-label cylinder on arbitrary nodes away from both pivots.

Each posterior is normalized by its own model's supported source context.
The installed kernel's numerator and denominator are proved to be those of
the real evaluated collider posterior before any quotient is compared.  The
true child readout is one distinguished full label even for nonbinary observed
alphabets; a false bit collecting several labels is never substituted for an
observed conditioning cell.

The final constructor also permits additional queried outcomes.  Conditional
marginalization restores the whole query after one parent's conditional cell
is separated.  Full observational equality, positivity, and the unchanged
action set belong to the same installed SCM pair throughout.  Non-influence
of the two base pivots is still a genuine structural hypothesis: this module
does not assert that an arbitrary active path supplies it.
-/

namespace ConditionalCollider

private theorem free_at (action : NodeSet S) (reference : S.Assignment)
    (node : Fin S.count) (inactive : action node = false) :
    (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference node = none := by
  simp only [Kernel.intervention, inactive, Bool.false_eq_true, if_false]

private theorem singleton_readout (rich : ObservedSignature.ValueRich S) (node : Fin S.count)
    (reference sample : S.Assignment) (second : reference node = rich.second node) :
    Kernel.agreesOn (NodeSet.singleton node) reference sample = hedgeIsSecond rich node (sample node) := by
  rw [Kernel.agreesOn_singleton, second]
  rfl

/-- Observe the child's second label and a full cylinder on the retained
context.  The source support is for the original model's actual evaluation,
not for an independently supplied probability table. -/
def contextPosterior (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (nodes : NodeSet S) (parentAway : nodes parent = false) (childAway : nodes child = false)
    (reference : S.Assignment)
    (supported : base.prior.EventPositive (fun old => Kernel.agreesOn nodes reference
      (base.evalUnder ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) old))) : FiniteProbRecord Bool :=
  posterior base rich parent child edge noise parentIgnored childIgnored
    ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference)
    (free_at action reference parent parentFree) (free_at action reference child childFree)
    nodes (Kernel.agreesOn nodes reference) (Kernel.agreesOn_dependsOnlyOn nodes reference)
    parentAway childAway supported true

/-- The context-aware posterior is one genuine cell of the original kernel.
Its evidence support is derived from the old context, while finite pushforward
and conditioning identities transport both masses on the real installed prior. -/
noncomputable def contextKernel_denote (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (nodes : NodeSet S) (parentAway : nodes parent = false) (childAway : nodes child = false)
    (reference : S.Assignment)
    (supported : base.prior.EventPositive (fun old => Kernel.agreesOn nodes reference
      (base.evalUnder ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) old)))
    (parentSecond : reference parent = rich.second parent) (childSecond : reference child = rich.second child) :
    ProbabilityResult.Equivalent
      ((Kernel.mk (NodeSet.singleton parent) action (NodeSet.union nodes (NodeSet.singleton child))).denote
        (model base rich parent child edge noise) reference)
      (some ((contextPosterior base rich parent child edge noise parentIgnored childIgnored
        action parentFree childFree nodes parentAway childAway reference supported).probVal id)) := by
  let actual := model base rich parent child edge noise
  let kernel : Kernel S := ⟨NodeSet.singleton parent, action, NodeSet.union nodes (NodeSet.singleton child)⟩
  let intervention := kernel.intervention reference
  let context := Kernel.agreesOn nodes reference
  let selectedEvidence := evidence base rich parent child edge noise intervention context true
  let parentEvent : Event actual.latent.Assignment := fun unit => hedgeIsSecond rich parent
    (actual.evalUnder intervention unit parent)
  have evidenceSupported : actual.prior.EventPositive selectedEvidence :=
    evidence_positive base rich parent child edge noise parentIgnored childIgnored intervention
      (free_at action reference parent parentFree) (free_at action reference child childFree)
      nodes context (Kernel.agreesOn_dependsOnlyOn nodes reference) parentAway childAway supported true
  have denominator := QProb.equiv_trans (Kernel.distribution_probVal actual kernel reference (kernel.conditionEvent reference))
    (actual.prior.probVal_congr _ selectedEvidence (fun unit => by
      dsimp only [kernel, Kernel.conditionEvent]
      rw [Kernel.agreesOn_union, singleton_readout rich child reference _ childSecond]
      change _ = (context (actual.evalUnder intervention unit) &&
        decide (hedgeIsSecond rich child (actual.evalUnder intervention unit child) = true))
      cases hedgeIsSecond rich child (actual.evalUnder intervention unit child) <;> rfl))
  have numerator := QProb.equiv_trans (Kernel.distribution_probVal actual kernel reference (kernel.numeratorEvent reference))
    (actual.prior.probVal_congr _ (fun unit => selectedEvidence unit && parentEvent unit) (fun unit => by
      dsimp only [kernel, Kernel.numeratorEvent]
      rw [Kernel.agreesOn_union, singleton_readout rich parent reference _ parentSecond,
        singleton_readout rich child reference _ childSecond]
      change (hedgeIsSecond rich parent (actual.evalUnder intervention unit parent) &&
        (context (actual.evalUnder intervention unit) && hedgeIsSecond rich child (actual.evalUnder intervention unit child))) =
        ((context (actual.evalUnder intervention unit) &&
        decide (hedgeIsSecond rich child (actual.evalUnder intervention unit child) = true)) &&
        hedgeIsSecond rich parent (actual.evalUnder intervention unit parent))
      cases context (actual.evalUnder intervention unit) <;>
        cases hedgeIsSecond rich child (actual.evalUnder intervention unit child) <;>
        cases hedgeIsSecond rich parent (actual.evalUnder intervention unit parent) <;> rfl))
  have kernelSupported := (QProb.equiv_num_pos_iff denominator).mpr evidenceSupported
  have kernelValue : ProbabilityResult.Equivalent (kernel.denote actual reference)
      (some (QProb.div ((kernel.distribution actual reference).probVal (kernel.numeratorEvent reference))
        ((kernel.distribution actual reference).probVal (kernel.conditionEvent reference)) kernelSupported)) := by
    unfold Kernel.denote
    rw [ProbabilityResult.divide, dif_pos kernelSupported]
    exact .value (QProb.equiv_refl _)
  have ratios := QProb.div_congr numerator denominator kernelSupported evidenceSupported
  have mapped := (actual.prior.conditionOn selectedEvidence evidenceSupported).map_probVal
    (fun unit => hedgeIsSecond rich parent (actual.evalUnder intervention unit parent)) id
  have posteriorRatio := actual.prior.conditionOn_probVal selectedEvidence parentEvent evidenceSupported
  exact ProbabilityResult.trans kernelValue (.value (QProb.equiv_trans ratios
    (QProb.equiv_symm (QProb.equiv_trans mapped posteriorRatio))))

/-- Biased collider noise reflects equality of the old child bit inside the
retained context.  Complementation at the true collider value is cancelled by
finite normalization on each conditioned prior separately, not by an assumed
equality of the conditioning masses. -/
theorem contextPosterior_probVal_equiv_iff_of_bias (left right : ExactModel S)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool)
    (leftParentIgnored : left.OtherMechanismsIgnore parent) (rightParentIgnored : right.OtherMechanismsIgnore parent)
    (leftChildIgnored : left.OtherMechanismsIgnore child) (rightChildIgnored : right.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (nodes : NodeSet S) (parentAway : nodes parent = false) (childAway : nodes child = false)
    (reference : S.Assignment)
    (leftSupported : left.prior.EventPositive (fun old => Kernel.agreesOn nodes reference
      (left.evalUnder ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) old)))
    (rightSupported : right.prior.EventPositive (fun old => Kernel.agreesOn nodes reference
      (right.evalUnder ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) old)))
    (gap : Nat) (positive : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    QProb.Equiv ((contextPosterior left rich parent child edge noise leftParentIgnored leftChildIgnored
      action parentFree childFree nodes parentAway childAway reference leftSupported).probVal id)
      ((contextPosterior right rich parent child edge noise rightParentIgnored rightChildIgnored
        action parentFree childFree nodes parentAway childAway reference rightSupported).probVal id) ↔
    QProb.Equiv
      ((left.prior.conditionOn (fun old => Kernel.agreesOn nodes reference
          (left.evalUnder ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) old)) leftSupported).probVal
        (signal left rich child ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference)))
      ((right.prior.conditionOn (fun old => Kernel.agreesOn nodes reference
          (right.evalUnder ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) old)) rightSupported).probVal
        (signal right rich child ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference))) := by
  let intervention := (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference
  have channel := posterior_probVal_equiv_iff_of_bias left right rich parent child edge noise
    leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored intervention
    (free_at action reference parent parentFree) (free_at action reference child childFree)
    nodes (Kernel.agreesOn nodes reference) (Kernel.agreesOn_dependsOnlyOn nodes reference)
    parentAway childAway leftSupported rightSupported true gap positive bias
  have complement := FiniteProbRecord.probVal_complement_equiv_iff
    (left.prior.conditionOn (fun old => Kernel.agreesOn nodes reference (left.evalUnder intervention old)) leftSupported)
    (signal left rich child intervention)
    (right.prior.conditionOn (fun old => Kernel.agreesOn nodes reference (right.evalUnder intervention old)) rightSupported)
    (signal right rich child intervention)
  simp only [Bool.xor_true] at channel
  exact channel.trans complement

/-- Construct a positive counterexample for the complete original query
from a supported contextual child-signal gap.  Only one outcome parent is
needed; additional outcomes are restored by conditional marginalization.
All remaining conditioners are retained as full labels, and the installed
models' kernel separation is proved rather than supplied as a premise. -/
noncomputable def contextCounterexample {graph : ObservedGraph S}
    (query : ConditionalKernelQuery S) (left right : ExactModel S)
    (leftCompatible : Compatible left graph) (rightCompatible : Compatible right graph)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (baseEqual : ObservationallyEquivalent left right) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (parentSelected : query.outcome parent = true) (childSelected : query.condition child = true)
    (leftParentIgnored : left.OtherMechanismsIgnore parent) (rightParentIgnored : right.OtherMechanismsIgnore parent)
    (leftChildIgnored : left.OtherMechanismsIgnore child) (rightChildIgnored : right.OtherMechanismsIgnore child)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap)
    (reference : S.Assignment) (parentSecond : reference parent = rich.second parent) (childSecond : reference child = rich.second child)
    (leftSupported : left.prior.EventPositive (fun old =>
      Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton child)) reference
        (left.evalUnder (query.operationKernel.intervention reference) old)))
    (rightSupported : right.prior.EventPositive (fun old =>
      Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton child)) reference
        (right.evalUnder (query.operationKernel.intervention reference) old)))
    (sourceGap : Not (QProb.Equiv
      ((left.prior.conditionOn (fun old => Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton child)) reference
          (left.evalUnder (query.operationKernel.intervention reference) old)) leftSupported).probVal
        (signal left rich child (query.operationKernel.intervention reference)))
      ((right.prior.conditionOn (fun old => Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton child)) reference
          (right.evalUnder (query.operationKernel.intervention reference) old)) rightSupported).probVal
        (signal right rich child (query.operationKernel.intervention reference))))) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  let nodes := NodeSet.diff query.condition (NodeSet.singleton child)
  have parentAway : nodes parent = false := by
    simp only [nodes, NodeSet.diff, query.outcome_condition_disjoint parent parentSelected, Bool.false_and]
  have childAway : nodes child = false := by
    simp only [nodes, NodeSet.diff, NodeSet.singleton, decide_true, Bool.not_true, Bool.and_false]
  have singletonSubset : NodeSet.Subset (NodeSet.singleton child) query.condition := by
    intro node selected
    have same := (NodeSet.singleton_eq_true_iff child node).mp selected
    rw [same]
    exact childSelected
  have conditionEq : query.condition = NodeSet.union nodes (NodeSet.singleton child) := (NodeSet.diff_union_eq singletonSubset).symm
  have parentSubset : NodeSet.Subset (NodeSet.singleton parent) query.outcome := by
    intro node selected
    have same := (NodeSet.singleton_eq_true_iff parent node).mp selected
    rw [same]
    exact parentSelected
  let restricted := query.restrictOutcome (NodeSet.singleton parent) parentSubset
  let leftModel := model left rich parent child edge noise
  let rightModel := model right rich parent child edge noise
  have parentFree := query.action_outcome_disjoint.symm parent parentSelected
  have childFree := query.action_condition_disjoint.symm child childSelected
  have leftMem : (GraphModelClass.positive graph).Mem leftModel :=
    ⟨compatible left leftCompatible rich parent child edge noise,
      ConditionalCollider.positive left leftPositive rich parent child edge noise noisePositive⟩
  have rightMem : (GraphModelClass.positive graph).Mem rightModel :=
    ⟨compatible right rightCompatible rich parent child edge noise,
      ConditionalCollider.positive right rightPositive rich parent child edge noise noisePositive⟩
  apply ConditionalCounterexampleIn.ofRestrictedOutcome (C := GraphModelClass.positive graph)
    (fun member => member.2) query (NodeSet.singleton parent) parentSubset
  refine ⟨leftModel, rightModel, leftMem, rightMem,
    observationally_equivalent left right baseEqual rich parent child edge
      leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored noise, ?_⟩
  intro equivalent
  rcases equivalent reference
    (leftMem.2.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported
    (rightMem.2.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported with ⟨between⟩
  have leftValue : ProbabilityResult.Equivalent (restricted.sourceTerm.denote leftModel reference)
      (some ((contextPosterior left rich parent child edge noise leftParentIgnored leftChildIgnored query.action
        parentFree childFree nodes parentAway childAway reference leftSupported).probVal id)) := by
    simpa only [restricted, ConditionalKernelQuery.restrictOutcome, ConditionalKernelQuery.sourceTerm, conditionEq] using
      contextKernel_denote left rich parent child edge noise leftParentIgnored leftChildIgnored query.action parentFree childFree
        nodes parentAway childAway reference leftSupported parentSecond childSecond
  have rightValue : ProbabilityResult.Equivalent (restricted.sourceTerm.denote rightModel reference)
      (some ((contextPosterior right rich parent child edge noise rightParentIgnored rightChildIgnored query.action
        parentFree childFree nodes parentAway childAway reference rightSupported).probVal id)) := by
    simpa only [restricted, ConditionalKernelQuery.restrictOutcome, ConditionalKernelQuery.sourceTerm, conditionEq] using
      contextKernel_denote right rich parent child edge noise rightParentIgnored rightChildIgnored query.action parentFree childFree
        nodes parentAway childAway reference rightSupported parentSecond childSecond
  have posteriors := ProbabilityResult.trans (ProbabilityResult.symm leftValue) (ProbabilityResult.trans between rightValue)
  cases posteriors with
  | value equal =>
      exact sourceGap ((contextPosterior_probVal_equiv_iff_of_bias left right rich parent child edge noise
        leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored query.action parentFree childFree
        nodes parentAway childAway reference leftSupported rightSupported gap positiveGap bias).mp equal)

end ConditionalCollider
end Causality
end Thesis
