import Thesis.CausalTransport.ConditionalColliderProbability

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Kernel counterexamples from the installed incoming-parent collider

The posterior calculation alone is not a kernel counterexample: a Boolean
readout event could combine several observed conditioning values.  Here the
collider is conditioned to its distinguished second value, whose readout is
true, and the queried parent is tested at its own second value.  Thus every
posterior probability used below is one actual cell of the original kernel,
also for observed alphabets with more than two labels.

The generic constructor transports a base child-signal gap, rather than
assuming separation of the new kernel.  The hedge specialization constructs
that gap internally when the conditioner is the only common root and its
queried incoming parent lies outside the large forest.  Its positive models
and their full observational equality are the real installed SCMs.  This
closes a conditional family with an outcome outside the confounded forest;
it is not coverage of arbitrary irreducible conditional failures or paths.
-/

namespace ConditionalCollider

private theorem top_positive (source : FiniteProbRecord Ω) : source.EventPositive topEvent := by
  change 0 < FiniteProbRecord.eventMass source.atoms topEvent
  rw [FiniteProbRecord.eventMass_top, source.total_mass]
  exact source.den_pos

private theorem free_at (action : NodeSet S) (reference : S.Assignment)
    (node : Fin S.count) (inactive : action node = false) :
    (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference node = none := by
  simp only [Kernel.intervention, inactive, Bool.false_eq_true, if_false]

/-- The actual parent posterior after observing the collider's second label,
with no additional context.  The intervention still carries the whole
original action set; only the two readout pivots must be outside that set. -/
def singletonPosterior (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (reference : S.Assignment) : FiniteProbRecord Bool :=
  posterior base rich parent child edge noise parentIgnored childIgnored
    ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference)
    (free_at action reference parent parentFree) (free_at action reference child childFree)
    NodeSet.empty topEvent (fun _ _ _ => rfl) rfl rfl (top_positive base.prior) true

private theorem kernel_distribution_probVal (base : ExactModel S) (kernel : Kernel S)
    (reference : S.Assignment) (event : Event S.Assignment) :
    QProb.Equiv ((kernel.distribution base reference).probVal event)
      (base.prior.probVal (fun unit => event (base.evalUnder (kernel.intervention reference) unit))) := by
  cases active : kernel.hasAction with
  | true =>
      simpa only [Kernel.distribution, active, if_true, FiniteLatentSCM.interventionalDist] using
        base.prior.map_probVal (base.evalUnder (kernel.intervention reference)) event
  | false =>
      have empty : kernel.intervention reference = FiniteLatentSCM.noIntervention S := by
        funext node
        have inactive := (finAny_eq_false_iff kernel.action).mp active node
        simp only [Kernel.intervention, inactive, Bool.false_eq_true, if_false, FiniteLatentSCM.noIntervention]
      simpa only [Kernel.distribution, active, Bool.false_eq_true, if_false, empty,
        FiniteLatentSCM.observationalDist, FiniteLatentSCM.eval] using
        base.prior.map_probVal (base.evalUnder (FiniteLatentSCM.noIntervention S)) event

private theorem singleton_readout (rich : ObservedSignature.ValueRich S) (node : Fin S.count)
    (reference sample : S.Assignment) (second : reference node = rich.second node) :
    Kernel.agreesOn (NodeSet.singleton node) reference sample = hedgeIsSecond rich node (sample node) := by
  rw [agreesOn_of_unique_node (NodeSet.singleton node) reference sample
    (by simp only [NodeSet.singleton, decide_true])
    (fun i selected => (NodeSet.singleton_eq_true_iff node i).mp selected), second]
  rfl

/-- One actual kernel cell is the evaluated collider posterior.  The proof
derives common support from the installed evidence and transports numerator
and denominator separately before identifying the two ratios. -/
noncomputable def singletonKernel_denote (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (reference : S.Assignment) (parentSecond : reference parent = rich.second parent)
    (childSecond : reference child = rich.second child) :
    ProbabilityResult.Equivalent
      ((Kernel.mk (NodeSet.singleton parent) action (NodeSet.singleton child)).denote
        (model base rich parent child edge noise) reference)
      (some ((singletonPosterior base rich parent child edge noise parentIgnored childIgnored
        action parentFree childFree reference).probVal id)) := by
  let actual := model base rich parent child edge noise
  let kernel : Kernel S := ⟨NodeSet.singleton parent, action, NodeSet.singleton child⟩
  let intervention := kernel.intervention reference
  let selectedEvidence := evidence base rich parent child edge noise intervention topEvent true
  let parentEvent : Event actual.latent.Assignment := fun unit => hedgeIsSecond rich parent
    (actual.evalUnder intervention unit parent)
  have supported : actual.prior.EventPositive selectedEvidence :=
    evidence_positive base rich parent child edge noise parentIgnored childIgnored intervention
      (free_at action reference parent parentFree) (free_at action reference child childFree)
      NodeSet.empty topEvent (fun _ _ _ => rfl) rfl rfl (top_positive base.prior) true
  have denominator := QProb.equiv_trans (kernel_distribution_probVal actual kernel reference (kernel.conditionEvent reference))
    (actual.prior.probVal_congr _ selectedEvidence (fun unit => by
      dsimp only [kernel, Kernel.conditionEvent]
      rw [singleton_readout rich child reference _ childSecond]
      change _ = (true && decide (hedgeIsSecond rich child (actual.evalUnder intervention unit child) = true))
      cases hedgeIsSecond rich child (actual.evalUnder intervention unit child) <;> rfl))
  have numerator := QProb.equiv_trans (kernel_distribution_probVal actual kernel reference (kernel.numeratorEvent reference))
    (actual.prior.probVal_congr _ (fun unit => selectedEvidence unit && parentEvent unit) (fun unit => by
      dsimp only [kernel, Kernel.numeratorEvent]
      rw [singleton_readout rich parent reference _ parentSecond, singleton_readout rich child reference _ childSecond]
      change _ = ((true && decide (hedgeIsSecond rich child (actual.evalUnder intervention unit child) = true)) &&
        hedgeIsSecond rich parent (actual.evalUnder intervention unit parent))
      cases hedgeIsSecond rich child (actual.evalUnder intervention unit child) <;>
        cases hedgeIsSecond rich parent (actual.evalUnder intervention unit parent) <;> rfl))
  have kernelSupported := (QProb.equiv_num_pos_iff denominator).mpr supported
  have kernelValue : ProbabilityResult.Equivalent (kernel.denote actual reference)
      (some (QProb.div ((kernel.distribution actual reference).probVal (kernel.numeratorEvent reference))
        ((kernel.distribution actual reference).probVal (kernel.conditionEvent reference)) kernelSupported)) := by
    unfold Kernel.denote
    rw [ProbabilityResult.divide, dif_pos kernelSupported]
    exact .value (QProb.equiv_refl _)
  have ratios := QProb.div_congr numerator denominator kernelSupported supported
  have mapped := (actual.prior.conditionOn selectedEvidence supported).map_probVal
    (fun unit => hedgeIsSecond rich parent (actual.evalUnder intervention unit parent)) id
  have posteriorRatio := actual.prior.conditionOn_probVal selectedEvidence parentEvent supported
  exact ProbabilityResult.trans kernelValue (.value (QProb.equiv_trans ratios
    (QProb.equiv_symm (QProb.equiv_trans mapped posteriorRatio))))

private theorem conditionOn_top_probVal (source : FiniteProbRecord Ω) (event : Event Ω) :
    QProb.Equiv ((source.conditionOn topEvent (top_positive source)).probVal event)
      (source.probVal event) := by
  change FiniteProbRecord.eventMass (source.atoms.filter (fun atom => topEvent atom.1)) event * source.den =
    FiniteProbRecord.eventMass source.atoms event * FiniteProbRecord.eventMass source.atoms topEvent
  rw [FiniteProbRecord.eventMass_filter_event, FiniteProbRecord.eventMass_top, source.total_mass]
  have same := FiniteProbRecord.eventMass_congr source.atoms (fun value => topEvent value && event value) event
    (fun _ => Bool.true_and _)
  rw [same]

private theorem probVal_complement_equiv_iff (left : FiniteProbRecord Ω) (leftEvent : Event Ω)
    (right : FiniteProbRecord X) (rightEvent : Event X) :
    QProb.Equiv (left.probVal (fun value => !leftEvent value)) (right.probVal (fun value => !rightEvent value)) ↔
      QProb.Equiv (left.probVal leftEvent) (right.probVal rightEvent) := by
  have leftTotal := congrArg (fun mass => mass * right.den)
    ((FiniteProbRecord.eventMass_add_complement left.atoms leftEvent).trans left.total_mass)
  have rightTotal := congrArg (fun mass => mass * left.den)
    ((FiniteProbRecord.eventMass_add_complement right.atoms rightEvent).trans right.total_mass)
  simp only [Nat.add_mul] at leftTotal rightTotal
  have common : left.den * right.den = right.den * left.den := Nat.mul_comm _ _
  constructor
  · intro equal
    change FiniteProbRecord.eventMass left.atoms (fun value => !leftEvent value) * right.den =
      FiniteProbRecord.eventMass right.atoms (fun value => !rightEvent value) * left.den at equal
    change FiniteProbRecord.eventMass left.atoms leftEvent * right.den =
      FiniteProbRecord.eventMass right.atoms rightEvent * left.den
    omega
  · intro equal
    change FiniteProbRecord.eventMass left.atoms leftEvent * right.den =
      FiniteProbRecord.eventMass right.atoms rightEvent * left.den at equal
    change FiniteProbRecord.eventMass left.atoms (fun value => !leftEvent value) * right.den =
      FiniteProbRecord.eventMass right.atoms (fun value => !rightEvent value) * left.den
    omega

/-- A kernel-ready posterior gap is exactly the old child's interventional
bit gap when the private noise is biased.  Conditioning on the true collider
complements the source bit; finite normalization proves that complementation
preserves and reflects rational equality even for different latent priors. -/
theorem singletonPosterior_probVal_equiv_iff_of_bias (left right : ExactModel S)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool)
    (leftParentIgnored : left.OtherMechanismsIgnore parent) (rightParentIgnored : right.OtherMechanismsIgnore parent)
    (leftChildIgnored : left.OtherMechanismsIgnore child) (rightChildIgnored : right.OtherMechanismsIgnore child)
    (action : NodeSet S) (parentFree : action parent = false) (childFree : action child = false)
    (reference : S.Assignment) (gap : Nat) (positive : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    QProb.Equiv ((singletonPosterior left rich parent child edge noise leftParentIgnored leftChildIgnored
        action parentFree childFree reference).probVal id)
      ((singletonPosterior right rich parent child edge noise rightParentIgnored rightChildIgnored
        action parentFree childFree reference).probVal id) ↔
      QProb.Equiv (left.prior.probVal (signal left rich child
        ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference)))
        (right.prior.probVal (signal right rich child
          ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference))) := by
  let intervention := (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference
  have channel := posterior_probVal_equiv_iff_of_bias left right rich parent child edge noise
    leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored intervention
    (free_at action reference parent parentFree) (free_at action reference child childFree)
    NodeSet.empty topEvent (fun _ _ _ => rfl) rfl rfl (top_positive left.prior) (top_positive right.prior)
    true gap positive bias
  have leftLaw := conditionOn_top_probVal left.prior (fun old => !(signal left rich child intervention old))
  have rightLaw := conditionOn_top_probVal right.prior (fun old => !(signal right rich child intervention old))
  have complement := probVal_complement_equiv_iff left.prior (signal left rich child intervention)
    right.prior (signal right rich child intervention)
  simp only [Bool.xor_true] at channel
  constructor
  · intro equal
    exact complement.mp (QProb.equiv_trans (QProb.equiv_symm leftLaw)
      (QProb.equiv_trans (channel.mp equal) rightLaw))
  · intro equal
    exact channel.mpr (QProb.equiv_trans leftLaw
      (QProb.equiv_trans (complement.mpr equal) (QProb.equiv_symm rightLaw)))

/-- Construct a positive counterexample for the original singleton parent /
singleton collider query from an existing interventional child-bit gap.
The new query gap is proved, not supplied.  Positivity and full observational
equality refer to the same two installed collider models in every field. -/
noncomputable def conditionalCounterexample {graph : ObservedGraph S}
    (query : ConditionalKernelQuery S) (left right : ExactModel S)
    (leftCompatible : Compatible left graph) (rightCompatible : Compatible right graph)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (baseEqual : ObservationallyEquivalent left right) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (outcome : query.outcome = NodeSet.singleton parent) (condition : query.condition = NodeSet.singleton child)
    (leftParentIgnored : left.OtherMechanismsIgnore parent) (rightParentIgnored : right.OtherMechanismsIgnore parent)
    (leftChildIgnored : left.OtherMechanismsIgnore child) (rightChildIgnored : right.OtherMechanismsIgnore child)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap)
    (reference : S.Assignment) (parentSecond : reference parent = rich.second parent)
    (childSecond : reference child = rich.second child)
    (sourceGap : Not (QProb.Equiv
      (left.prior.probVal (signal left rich child (query.operationKernel.intervention reference)))
      (right.prior.probVal (signal right rich child (query.operationKernel.intervention reference))))) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  have parentSelected : query.outcome parent = true := by rw [outcome]; simp only [NodeSet.singleton, decide_true]
  have childSelected : query.condition child = true := by rw [condition]; simp only [NodeSet.singleton, decide_true]
  have parentFree := query.action_outcome_disjoint.symm parent parentSelected
  have childFree := query.action_condition_disjoint.symm child childSelected
  let leftModel := model left rich parent child edge noise
  let rightModel := model right rich parent child edge noise
  have leftMem : (GraphModelClass.positive graph).Mem leftModel :=
    ⟨compatible left leftCompatible rich parent child edge noise,
      ConditionalCollider.positive left leftPositive rich parent child edge noise noisePositive⟩
  have rightMem : (GraphModelClass.positive graph).Mem rightModel :=
    ⟨compatible right rightCompatible rich parent child edge noise,
      ConditionalCollider.positive right rightPositive rich parent child edge noise noisePositive⟩
  refine ⟨leftModel, rightModel, leftMem, rightMem,
    observationally_equivalent left right baseEqual rich parent child edge
      leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored noise, ?_⟩
  intro equivalent
  rcases equivalent reference
    (leftMem.2.kernelPositiveSupportedValue query.operationKernel reference).toSupported
    (rightMem.2.kernelPositiveSupportedValue query.operationKernel reference).toSupported with ⟨between⟩
  have leftValue : ProbabilityResult.Equivalent (query.sourceTerm.denote leftModel reference)
      (some ((singletonPosterior left rich parent child edge noise leftParentIgnored leftChildIgnored
        query.action parentFree childFree reference).probVal id)) := by
    simpa only [ConditionalKernelQuery.sourceTerm, outcome, condition] using
      singletonKernel_denote left rich parent child edge noise leftParentIgnored leftChildIgnored
        query.action parentFree childFree reference parentSecond childSecond
  have rightValue : ProbabilityResult.Equivalent (query.sourceTerm.denote rightModel reference)
      (some ((singletonPosterior right rich parent child edge noise rightParentIgnored rightChildIgnored
        query.action parentFree childFree reference).probVal id)) := by
    simpa only [ConditionalKernelQuery.sourceTerm, outcome, condition] using
      singletonKernel_denote right rich parent child edge noise rightParentIgnored rightChildIgnored
        query.action parentFree childFree reference parentSecond childSecond
  have posteriors := ProbabilityResult.trans (ProbabilityResult.symm leftValue)
    (ProbabilityResult.trans between rightValue)
  cases posteriors with
  | value equal =>
      exact sourceGap ((singletonPosterior_probVal_equiv_iff_of_bias left right rich parent child edge noise
        leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored query.action parentFree childFree
        reference gap positiveGap bias).mp equal)

end ConditionalCollider

private theorem hedgeRootParityEvent_singleton (rich : ObservedSignature.ValueRich S)
    (root : Fin S.count) (sample : S.Assignment) :
    hedgeRootParityEvent rich (NodeSet.singleton root) sample = hedgeIsSecond rich root (sample root) := by
  unfold hedgeRootParityEvent hedgeNodeXor NodeSet.members
  rw [List.foldl_filter]
  have response :
      (fun total node => if (NodeSet.singleton root) node then Bool.xor total (hedgeIsSecond rich node (sample node)) else total) =
        (fun total node => if node = root then Bool.xor total (hedgeIsSecond rich root (sample root)) else total) := by
    funext total node
    by_cases same : node = root
    · subst node
      simp only [NodeSet.singleton, decide_true, if_true]
    · simp only [NodeSet.singleton, same, decide_false, Bool.false_eq_true, if_false]
  rw [response]
  exact foldl_xor_bit_of_mem_nodup (NodeSet.enumerated S) (NodeSet.mem_enumerated S root)
    (NodeSet.nodup_enumerated S) (hedgeIsSecond rich root (sample root))

/-- Construct a positive conditional countermodel when the sole common hedge
root is the conditioner and a queried incoming parent is outside the large
forest.  The original action set is unrestricted, subject only to the query's
own disjointness conditions.

The old root-parity theorem supplies the source gap internally.  The fair
parent makes the collider's conditioning mass supported, and biased private
noise transfers that gap to the parent's actual conditional kernel cell.
This is not the older denominator-preservation argument: the conditioned
root itself is modified, and its posterior, rather than a joint numerator
substituted for the conditional query, is what separates the two models.
Only the displayed singleton geometry remains a restriction; observed value
types, graph size, other directed edges, and latent spaces are not specialized. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfSingletonRootColliderWithNoise
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (outcome : query.outcome = NodeSet.singleton parent) (condition : query.condition = NodeSet.singleton child)
    (roots : w.roots = NodeSet.singleton child) (outside : w.large parent = false)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  have rootSelected : w.roots child = true := by rw [roots]; simp only [NodeSet.singleton, decide_true]
  have parentNone := w.large_forest.child_off_set parent outside
  have childNone := ((w.large_forest.roots_exact child).mp rootSelected).2
  let left := w.largeCarrierDefectParityModel rich
  let right := w.smallCarrierDefectParityModel rich
  have leftSignal : forall old, hedgeRootParityEvent rich w.roots
      (left.evalUnder (hedgeDoSecond rich query.action) old) =
        ConditionalCollider.signal left rich child (query.operationKernel.intervention rich.second) old := by
    intro old
    rw [roots, hedgeRootParityEvent_singleton]
    rfl
  have rightSignal : forall old, hedgeRootParityEvent rich w.roots
      (right.evalUnder (hedgeDoSecond rich query.action) old) =
        ConditionalCollider.signal right rich child (query.operationKernel.intervention rich.second) old := by
    intro old
    rw [roots, hedgeRootParityEvent_singleton]
    rfl
  have sourceGap : Not (QProb.Equiv
      (left.prior.probVal (ConditionalCollider.signal left rich child (query.operationKernel.intervention rich.second)))
      (right.prior.probVal (ConditionalCollider.signal right rich child (query.operationKernel.intervention rich.second)))) := by
    intro equal
    have leftLaw := QProb.equiv_trans (left.interventionalValue_eq (hedgeDoSecond rich query.action)
      (hedgeRootParityEvent rich w.roots)) (left.prior.probVal_congr _ _ leftSignal)
    have rightLaw := QProb.equiv_trans (right.interventionalValue_eq (hedgeDoSecond rich query.action)
      (hedgeRootParityEvent rich w.roots)) (right.prior.probVal_congr _ _ rightSignal)
    exact w.carrierDefectParityModels_rootParity_not_equiv_doSecond rich
      (QProb.equiv_trans leftLaw (QProb.equiv_trans equal (QProb.equiv_symm rightLaw)))
  exact ConditionalCollider.conditionalCounterexample query left right
    (w.largeCarrierDefectParityModel_compatible rich) (w.smallCarrierDefectParityModel_compatible rich)
    (w.largeCarrierDefectParityModel_positive rich) (w.smallCarrierDefectParityModel_positive rich)
    (w.carrierDefectParityModels_observationally_equivalent rich) rich parent child edge outcome condition
    (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich parent parentNone)
    (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich parent parentNone)
    (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich child childNone)
    (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich child childNone)
    noise noisePositive gap positiveGap bias rich.second rfl rfl sourceGap

/-- The same conditional family with the explicit supported stay/flip weights
`2:1`.  No noise existence statement or selected positive epsilon is needed. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfSingletonRootCollider
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (outcome : query.outcome = NodeSet.singleton parent) (condition : query.condition = NodeSet.singleton child)
    (roots : w.roots = NodeSet.singleton child) (outside : w.large parent = false) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfSingletonRootColliderWithNoise rich parent child edge outcome condition roots outside
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel)

end Causality
end Thesis
