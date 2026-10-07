import Thesis.CausalTransport.ConditionalCollider
import Thesis.Probability.FiniteProductReindex

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Conditional probabilities of the actual collider-updated SCM

`ConditionalCollider` installs a fair observed parent and a noisy child in a
real finite SCM.  This module connects that model's evaluated, conditioned
latent prior to `Probability.ColliderChannel`.  The connection retains the
actual intervention and an arbitrary supported context on the other observed
nodes.  Its probability statements are not assumptions about detached bits.

Two non-influence hypotheses ensure that replacing the pivots leaves the
context and the old child signal unchanged.  These are genuine restrictions
on the construction, not consequences asserted for arbitrary active paths.
The full-event posterior identity below proves both its normalizing evidence
and its numerator from evaluation of the installed SCM.  Different base
models may have different latent spaces and different context probabilities.

The collider observation here is a Boolean readout event.  For a general
observed alphabet, the false readout can collect several labels; it must not
be silently identified with a single observed conditioning value.  The true
readout is the distinguished second label.  Passing to a particular
`ConditionalKernelQuery`, and composing gadgets along arbitrary active paths,
remain separate obligations of general conditional completeness.
-/

namespace ConditionalCollider

/-- The original child bit under the actual intervention.  It is sampled
from the old model's prior, before either fresh private input is installed. -/
def signal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (intervention : (node : Fin S.count) -> Option (S.Value node)) :
    Event base.latent.Assignment :=
  fun old => hedgeIsSecond rich child (base.evalUnder intervention old child)

/-- Evidence in the installed SCM, rather than in an independently supplied
Boolean distribution.  The same observation event is evaluated after the
intervention at every actual extended latent assignment. -/
def evidence (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (context : Event S.Assignment) (value : Bool) :
    Event (model base rich parent child edge noise).latent.Assignment :=
  fun unit => context ((model base rich parent child edge noise).evalUnder intervention unit) &&
    decide (hedgeIsSecond rich child
      ((model base rich parent child edge noise).evalUnder intervention unit child) = value)

/-! ## Source-first encoding, context preservation, and the actual evidence -/

/-- Reorder the actual installed prior for every event.  The proof uses
finite Fubini, not a rectangular-independence shortcut or a selected coupling. -/
theorem prior_probVal_sourceFirst (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool)
    (event : Event (model base rich parent child edge noise).latent.Assignment) :
    QProb.Equiv ((model base rich parent child edge noise).prior.probVal event)
      ((ColliderChannel.prior base.prior noise).probVal
        (fun input => event (assignment base rich parent child edge noise input.2 input.1.2 input.1.1))) :=
  QProb.equiv_trans (prior_probVal base rich parent child edge noise event)
    (base.prior.product_cycle_probVal noise ColliderChannel.fairMask
      (fun input => event (assignment base rich parent child edge noise input.2 input.1.2 input.1.1)))

/-- A context genuinely local to nodes away from the two pivots retains its
original value.  The structural non-influence hypotheses justify this for
the whole assignment, including all possible descendants in the context. -/
theorem context_assignment (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false)
    (old : base.latent.Assignment) (maskBit noiseBit : Bool) :
    context ((model base rich parent child edge noise).evalUnder intervention
      (assignment base rich parent child edge noise maskBit noiseBit old)) =
      context (base.evalUnder intervention old) := by
  apply localContext
  intro node selected
  have notParent : node ≠ parent := by
    intro same
    rw [same, parentAway] at selected
    cases selected
  have notChild : node ≠ child := by
    intro same
    rw [same, childAway] at selected
    cases selected
  exact evalUnder_of_away base rich parent child edge noise parentIgnored childIgnored
    intervention old maskBit noiseBit node notParent notChild

/-- Pointwise identification of the installed evidence with the channel's
evidence, retaining the original context and child signal. -/
theorem evidence_assignment (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false)
    (value : Bool) (input : ColliderChannel.Input base.latent.Assignment) :
    evidence base rich parent child edge noise intervention context value
        (assignment base rich parent child edge noise input.2 input.1.2 input.1.1) =
      ColliderChannel.evidence (signal base rich child intervention)
        (fun old => context (base.evalUnder intervention old)) value input := by
  unfold evidence
  rw [context_assignment base rich parent child edge noise parentIgnored childIgnored
    intervention nodes context localContext parentAway childAway]
  rw [(bit_equations base rich parent child edge noise parentIgnored intervention
    parentFree childFree input.1.1 input.2 input.1.2).2]
  change _ = (context (base.evalUnder intervention input.1.1) &&
    decide (Bool.xor (Bool.xor (signal base rich child intervention input.1.1) input.1.2) input.2 = value))
  have commute :
      Bool.xor (Bool.xor (signal base rich child intervention input.1.1) input.2) input.1.2 =
        Bool.xor (Bool.xor (signal base rich child intervention input.1.1) input.1.2) input.2 := by
    cases signal base rich child intervention input.1.1 <;> cases input.2 <;> cases input.1.2 <;> rfl
  rw [show hedgeIsSecond rich child (base.evalUnder intervention input.1.1 child) =
    signal base rich child intervention input.1.1 from rfl, commute]

/-- The actual SCM evidence has the channel probability, for arbitrary
supported or unsupported source contexts.  Support is derived separately. -/
theorem evidence_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false) (value : Bool) :
    QProb.Equiv ((model base rich parent child edge noise).prior.probVal
      (evidence base rich parent child edge noise intervention context value))
      ((ColliderChannel.prior base.prior noise).probVal
        (ColliderChannel.evidence (signal base rich child intervention)
          (fun old => context (base.evalUnder intervention old)) value)) := by
  have encoded := prior_probVal_sourceFirst base rich parent child edge noise
    (evidence base rich parent child edge noise intervention context value)
  have same := (ColliderChannel.prior base.prior noise).probVal_congr _ _
    (evidence_assignment base rich parent child edge noise parentIgnored childIgnored
      intervention parentFree childFree nodes context localContext parentAway childAway value)
  exact QProb.equiv_trans encoded same

/-- The corresponding actual joint numerator, for every Boolean parent event.
No equality of denominators or positive source-signal atom is assumed. -/
theorem joint_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false) (value : Bool) (event : Event Bool) :
    QProb.Equiv ((model base rich parent child edge noise).prior.probVal
      (fun unit => evidence base rich parent child edge noise intervention context value unit &&
        event (hedgeIsSecond rich parent
          ((model base rich parent child edge noise).evalUnder intervention unit parent))))
      ((ColliderChannel.prior base.prior noise).probVal
        (fun input => ColliderChannel.evidence (signal base rich child intervention)
          (fun old => context (base.evalUnder intervention old)) value input && event input.2)) := by
  let actualEvent : Event (model base rich parent child edge noise).latent.Assignment :=
    fun unit => evidence base rich parent child edge noise intervention context value unit &&
      event (hedgeIsSecond rich parent
        ((model base rich parent child edge noise).evalUnder intervention unit parent))
  let encodedEvent : Event (ColliderChannel.Input base.latent.Assignment) :=
    fun input => actualEvent (assignment base rich parent child edge noise input.2 input.1.2 input.1.1)
  let channelEvent : Event (ColliderChannel.Input base.latent.Assignment) :=
    fun input => ColliderChannel.evidence (signal base rich child intervention)
      (fun old => context (base.evalUnder intervention old)) value input && event input.2
  have encoded := prior_probVal_sourceFirst base rich parent child edge noise actualEvent
  have same := (ColliderChannel.prior base.prior noise).probVal_congr encodedEvent channelEvent
    (fun input => by
      change actualEvent _ = channelEvent input
      dsimp only [actualEvent, channelEvent]
      rw [evidence_assignment base rich parent child edge noise parentIgnored childIgnored
        intervention parentFree childFree nodes context localContext parentAway childAway value input,
        (bit_equations base rich parent child edge noise parentIgnored intervention
          parentFree childFree input.1.1 input.2 input.1.2).1])
  exact QProb.equiv_trans encoded same

/-- A supported old context makes the actual collider evidence positive.
This remains true for deterministic signals and deterministic noise; the fair
parent, rather than an assumed joint support property, supplies the evidence. -/
theorem evidence_positive (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false)
    (supported : base.prior.EventPositive (fun old => context (base.evalUnder intervention old))) (value : Bool) :
    (model base rich parent child edge noise).prior.EventPositive
      (evidence base rich parent child edge noise intervention context value) :=
  (QProb.equiv_num_pos_iff (evidence_probVal base rich parent child edge noise
    parentIgnored childIgnored intervention parentFree childFree nodes context localContext
    parentAway childAway value)).mpr
    (ColliderChannel.evidence_positive base.prior (signal base rich child intervention)
      (fun old => context (base.evalUnder intervention old)) supported noise value)

/-! ## The evaluated posterior is the channel posterior -/

/-- Condition the real extended latent prior and read the real evaluated
parent bit.  Its support proof is constructed from the old supported context. -/
def posterior (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false)
    (supported : base.prior.EventPositive (fun old => context (base.evalUnder intervention old))) (value : Bool) :
    FiniteProbRecord Bool :=
  ((model base rich parent child edge noise).prior.conditionOn
    (evidence base rich parent child edge noise intervention context value)
    (evidence_positive base rich parent child edge noise parentIgnored childIgnored
      intervention parentFree childFree nodes context localContext parentAway childAway supported value)).map
    (fun unit => hedgeIsSecond rich parent
      ((model base rich parent child edge noise).evalUnder intervention unit parent))

/-- Full-event equality of the actual evaluated posterior and the probability
channel posterior.  Both the joint numerator and the conditioning denominator
are transported before division; no matched-denominator premise is inserted. -/
theorem posterior_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false)
    (supported : base.prior.EventPositive (fun old => context (base.evalUnder intervention old)))
    (value : Bool) (event : Event Bool) :
    QProb.Equiv
      ((posterior base rich parent child edge noise parentIgnored childIgnored intervention
        parentFree childFree nodes context localContext parentAway childAway supported value).probVal event)
      ((ColliderChannel.posterior base.prior (signal base rich child intervention)
        (fun old => context (base.evalUnder intervention old)) supported noise value).probVal event) := by
  let actual := model base rich parent child edge noise
  let actualEvidence := evidence base rich parent child edge noise intervention context value
  let actualPositive := evidence_positive base rich parent child edge noise parentIgnored childIgnored
    intervention parentFree childFree nodes context localContext parentAway childAway supported value
  let parentEvent : Event actual.latent.Assignment := fun unit => event (hedgeIsSecond rich parent
    (actual.evalUnder intervention unit parent))
  let channel := ColliderChannel.prior base.prior noise
  let channelEvidence := ColliderChannel.evidence (signal base rich child intervention)
    (fun old => context (base.evalUnder intervention old)) value
  let channelPositive := ColliderChannel.evidence_positive base.prior (signal base rich child intervention)
    (fun old => context (base.evalUnder intervention old)) supported noise value
  have actualMap := (actual.prior.conditionOn actualEvidence actualPositive).map_probVal
    (fun unit => hedgeIsSecond rich parent (actual.evalUnder intervention unit parent)) event
  have actualRatio := actual.prior.conditionOn_probVal actualEvidence parentEvent actualPositive
  have channelMap := (channel.conditionOn channelEvidence channelPositive).map_probVal (fun input => input.2) event
  have channelRatio := channel.conditionOn_probVal channelEvidence (fun input => event input.2) channelPositive
  have ratios := QProb.div_congr
    (joint_probVal base rich parent child edge noise parentIgnored childIgnored intervention
      parentFree childFree nodes context localContext parentAway childAway value event)
    (evidence_probVal base rich parent child edge noise parentIgnored childIgnored intervention
      parentFree childFree nodes context localContext parentAway childAway value)
    actualPositive channelPositive
  exact QProb.equiv_trans actualMap (QProb.equiv_trans actualRatio
    (QProb.equiv_trans ratios (QProb.equiv_symm (QProb.equiv_trans channelMap channelRatio))))

/-- Fully supported private noise gives both actual posterior parent bits,
even when the old child signal is deterministic inside the context. -/
theorem posterior_positive (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false)
    (supported : base.prior.EventPositive (fun old => context (base.evalUnder intervention old)))
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit)) (value bit : Bool) :
    (posterior base rich parent child edge noise parentIgnored childIgnored intervention
      parentFree childFree nodes context localContext parentAway childAway supported value).EventPositive
        (FiniteProbRecord.singletonEvent bit) :=
  (QProb.equiv_num_pos_iff (posterior_probVal base rich parent child edge noise parentIgnored childIgnored
    intervention parentFree childFree nodes context localContext parentAway childAway supported value
      (FiniteProbRecord.singletonEvent bit))).mpr
    (ColliderChannel.posterior_positive base.prior (signal base rich child intervention)
      (fun old => context (base.evalUnder intervention old)) supported noise noisePositive value bit)

/-- The installed collider preserves and reflects the old conditional bit
gap through biased private noise.  This is a theorem about the two actual
SCM posteriors.  Neither equality of the two prior denominators nor equality
of their context probabilities is a hypothesis.

The context is common as an observed event, but may induce different latent
events and masses in the two base models.  Every structural hypothesis used
to retain that context is explicit; no unproved path-composition claim is
hidden in the source-to-SCM probability transport. -/
theorem posterior_probVal_equiv_iff_of_bias (left right : ExactModel S)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool)
    (leftParentIgnored : left.OtherMechanismsIgnore parent) (rightParentIgnored : right.OtherMechanismsIgnore parent)
    (leftChildIgnored : left.OtherMechanismsIgnore child) (rightChildIgnored : right.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false)
    (leftSupported : left.prior.EventPositive (fun old => context (left.evalUnder intervention old)))
    (rightSupported : right.prior.EventPositive (fun old => context (right.evalUnder intervention old)))
    (value : Bool) (gap : Nat) (positive : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    QProb.Equiv
      ((posterior left rich parent child edge noise leftParentIgnored leftChildIgnored intervention
        parentFree childFree nodes context localContext parentAway childAway leftSupported value).probVal id)
      ((posterior right rich parent child edge noise rightParentIgnored rightChildIgnored intervention
        parentFree childFree nodes context localContext parentAway childAway rightSupported value).probVal id) ↔
      QProb.Equiv
        ((left.prior.conditionOn (fun old => context (left.evalUnder intervention old)) leftSupported).probVal
          (fun old => Bool.xor (signal left rich child intervention old) value))
        ((right.prior.conditionOn (fun old => context (right.evalUnder intervention old)) rightSupported).probVal
          (fun old => Bool.xor (signal right rich child intervention old) value)) := by
  have leftLaw := posterior_probVal left rich parent child edge noise leftParentIgnored leftChildIgnored
    intervention parentFree childFree nodes context localContext parentAway childAway leftSupported value id
  have rightLaw := posterior_probVal right rich parent child edge noise rightParentIgnored rightChildIgnored
    intervention parentFree childFree nodes context localContext parentAway childAway rightSupported value id
  have channel := ColliderChannel.posterior_probVal_equiv_iff_of_bias
    left.prior (signal left rich child intervention) (fun old => context (left.evalUnder intervention old)) leftSupported
    right.prior (signal right rich child intervention) (fun old => context (right.evalUnder intervention old)) rightSupported
    noise value gap positive bias
  constructor
  · intro equal
    exact channel.mp (QProb.equiv_trans (QProb.equiv_symm leftLaw) (QProb.equiv_trans equal rightLaw))
  · intro equal
    exact QProb.equiv_trans leftLaw (QProb.equiv_trans (channel.mpr equal) (QProb.equiv_symm rightLaw))

end ConditionalCollider
end Causality
end Thesis
