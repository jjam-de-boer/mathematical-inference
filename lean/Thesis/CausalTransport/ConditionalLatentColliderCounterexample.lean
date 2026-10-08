import Thesis.CausalTransport.ConditionalLatentColliderProbability
import Thesis.CausalTransport.ConditionalMarginalization

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Original conditional kernels separated through an existing latent pair

The realized shared-latent channel must still be connected to a full observed
conditioning cell.  The true child bit is its distinguished second label;
other observed conditioner labels are retained as a complete cylinder away
from both pivots.  The actual kernel numerator and denominator are both
transported before the posterior gap is used.

The counterexample constructor installs two positive compatible SCMs on the
original graph and compares the original action and conditioning set.  Only
one queried parent cell is needed; conditional marginalization restores any
additional queried outcomes.  Its source gap is a supported conditional gap
in the old models, not an assumed gap of the already modified kernel.

An existing bidirected edge and non-influence of the two base pivots are
still explicit restrictions.  This is the shared-latent first-edge family,
not a proof that every arbitrary active back-door path has been composed.
-/

namespace ConditionalLatentCollider

private theorem free_at (action : NodeSet S) (reference : S.Assignment)
    (node : Fin S.count) (inactive : action node = false) :
    (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference node = none := by
  simp only [Kernel.intervention, inactive, Bool.false_eq_true, if_false]

/-- The realized actual posterior for a full observed context and true child
label.  The source context is pulled back through the original intervention. -/
def contextRealization (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (different : child ≠ parent) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (nodes : NodeSet S) (parentAway : nodes parent = false) (childAway : nodes child = false)
    (reference : S.Assignment) :=
  realization base rich parent child different noise parentIgnored childIgnored
    ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference)
    (free_at action reference parent parentFree) (free_at action reference child childFree)
    nodes (Kernel.agreesOn nodes reference) (Kernel.agreesOn_dependsOnlyOn nodes reference) parentAway childAway true

/-- One actual kernel cell equals the actual realized posterior.  This is
a full-value conditioning event even on nonbinary alphabets; the false child
readout is never substituted for one observed label. -/
noncomputable def contextKernel_denote (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (different : child ≠ parent) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (nodes : NodeSet S) (parentAway : nodes parent = false) (childAway : nodes child = false)
    (reference : S.Assignment)
    (supported : base.prior.EventPositive (fun old => Kernel.agreesOn nodes reference
      (base.evalUnder ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) old)))
    (parentSecond : reference parent = rich.second parent) (childSecond : reference child = rich.second child) :
    ProbabilityResult.Equivalent
      ((Kernel.mk (NodeSet.singleton parent) action (NodeSet.union nodes (NodeSet.singleton child))).denote
        (model base rich parent child noise) reference)
      (some (((contextRealization base rich parent child different noise parentIgnored childIgnored
        action parentFree childFree nodes parentAway childAway reference).posterior supported).probVal id)) := by
  let actual := model base rich parent child noise
  let kernel : Kernel S := ⟨NodeSet.singleton parent, action, NodeSet.union nodes (NodeSet.singleton child)⟩
  let intervention := kernel.intervention reference
  let context := Kernel.agreesOn nodes reference
  let selectedEvidence := evidence base rich parent child noise intervention context true
  let parentEvent : Event actual.latent.Assignment := fun unit => hedgeIsSecond rich parent (actual.evalUnder intervention unit parent)
  let realized := contextRealization base rich parent child different noise parentIgnored childIgnored
    action parentFree childFree nodes parentAway childAway reference
  have evidenceSupported : actual.prior.EventPositive selectedEvidence := realized.evidence_positive supported
  have denominator := QProb.equiv_trans (Kernel.distribution_probVal actual kernel reference (kernel.conditionEvent reference))
    (actual.prior.probVal_congr _ selectedEvidence (fun unit => by
      dsimp only [kernel, Kernel.conditionEvent]
      rw [Kernel.agreesOn_union, Kernel.agreesOn_singleton, childSecond]
      change (context (actual.evalUnder intervention unit) &&
        hedgeIsSecond rich child (actual.evalUnder intervention unit child)) =
        (context (actual.evalUnder intervention unit) &&
        decide (hedgeIsSecond rich child (actual.evalUnder intervention unit child) = true))
      cases hedgeIsSecond rich child (actual.evalUnder intervention unit child) <;> rfl))
  have numerator := QProb.equiv_trans (Kernel.distribution_probVal actual kernel reference (kernel.numeratorEvent reference))
    (actual.prior.probVal_congr _ (fun unit => selectedEvidence unit && parentEvent unit) (fun unit => by
      dsimp only [kernel, Kernel.numeratorEvent]
      rw [Kernel.agreesOn_union, Kernel.agreesOn_singleton, Kernel.agreesOn_singleton, parentSecond, childSecond]
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

/-- A supported old source gap produces a positive counterexample for the
full original conditional query through an already declared bidirected edge.
No observed incoming arrow between the pivots is required. -/
noncomputable def contextCounterexample {graph : ObservedGraph S}
    (query : ConditionalKernelQuery S) (left right : ExactModel S)
    (leftCompatible : Compatible left graph) (rightCompatible : Compatible right graph)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (baseEqual : ObservationallyEquivalent left right) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : graph.bidirected parent child = true)
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
  have different : child ≠ parent := by
    intro same
    rw [same, query.outcome_condition_disjoint parent parentSelected] at childSelected
    cases childSelected
  have singletonSubset : NodeSet.Subset (NodeSet.singleton child) query.condition := by
    intro node selected
    rw [(NodeSet.singleton_eq_true_iff child node).mp selected]
    exact childSelected
  have conditionEq : query.condition = NodeSet.union nodes (NodeSet.singleton child) := (NodeSet.diff_union_eq singletonSubset).symm
  have parentSubset : NodeSet.Subset (NodeSet.singleton parent) query.outcome := by
    intro node selected
    rw [(NodeSet.singleton_eq_true_iff parent node).mp selected]
    exact parentSelected
  let restricted := query.restrictOutcome (NodeSet.singleton parent) parentSubset
  let leftModel := model left rich parent child noise
  let rightModel := model right rich parent child noise
  have parentFree := query.action_outcome_disjoint.symm parent parentSelected
  have childFree := query.action_condition_disjoint.symm child childSelected
  have leftMem : (GraphModelClass.positive graph).Mem leftModel :=
    ⟨compatible left leftCompatible rich parent child edge noise,
      positive left leftPositive rich parent child leftParentIgnored leftChildIgnored noise noisePositive⟩
  have rightMem : (GraphModelClass.positive graph).Mem rightModel :=
    ⟨compatible right rightCompatible rich parent child edge noise,
      positive right rightPositive rich parent child rightParentIgnored rightChildIgnored noise noisePositive⟩
  apply ConditionalCounterexampleIn.ofRestrictedOutcome (C := GraphModelClass.positive graph)
    (fun member => member.2) query (NodeSet.singleton parent) parentSubset
  refine ⟨leftModel, rightModel, leftMem, rightMem,
    observationally_equivalent left right baseEqual rich parent child
      leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored noise, ?_⟩
  intro equivalent
  rcases equivalent reference
    (leftMem.2.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported
    (rightMem.2.kernelPositiveSupportedValue restricted.operationKernel reference).toSupported with ⟨between⟩
  let leftRealized := contextRealization left rich parent child different noise leftParentIgnored leftChildIgnored
    query.action parentFree childFree nodes parentAway childAway reference
  let rightRealized := contextRealization right rich parent child different noise rightParentIgnored rightChildIgnored
    query.action parentFree childFree nodes parentAway childAway reference
  have leftValue : ProbabilityResult.Equivalent (restricted.sourceTerm.denote leftModel reference)
      (some ((leftRealized.posterior leftSupported).probVal id)) := by
    simpa only [restricted, ConditionalKernelQuery.restrictOutcome, ConditionalKernelQuery.sourceTerm, conditionEq] using
      contextKernel_denote left rich parent child different noise leftParentIgnored leftChildIgnored query.action parentFree childFree
        nodes parentAway childAway reference leftSupported parentSecond childSecond
  have rightValue : ProbabilityResult.Equivalent (restricted.sourceTerm.denote rightModel reference)
      (some ((rightRealized.posterior rightSupported).probVal id)) := by
    simpa only [restricted, ConditionalKernelQuery.restrictOutcome, ConditionalKernelQuery.sourceTerm, conditionEq] using
      contextKernel_denote right rich parent child different noise rightParentIgnored rightChildIgnored query.action parentFree childFree
        nodes parentAway childAway reference rightSupported parentSecond childSecond
  have posteriors := ProbabilityResult.trans (ProbabilityResult.symm leftValue) (ProbabilityResult.trans between rightValue)
  cases posteriors with
  | value equal =>
      have complements := (leftRealized.posterior_probVal_equiv_iff_of_bias rightRealized leftSupported rightSupported
        gap positiveGap bias).mp equal
      simp only [Bool.xor_true] at complements
      exact sourceGap ((FiniteProbRecord.probVal_complement_equiv_iff
        (left.prior.conditionOn _ leftSupported) (signal left rich child (query.operationKernel.intervention reference))
        (right.prior.conditionOn _ rightSupported) (signal right rich child (query.operationKernel.intervention reference))).mp complements)

end ConditionalLatentCollider
end Causality
end Thesis
