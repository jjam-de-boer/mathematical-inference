import Thesis.CausalTransport.HedgeReadout
import Thesis.Probability.ColliderChannel

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Structural realization of the incoming-parent collider channel

The probability construction `ColliderChannel` needs an independent fair
parent and a private noisy collider, not merely arbitrary random variables
with suitable marginal laws.  This module installs those two mechanisms in
an actual SCM on the original observed signature and projected graph.

First the supplied parent gets a fresh private fair bit.  Then a declared
child injects its old signal, XORs the new parent's bit, and adds its own
private noise.  The exact interventional equations identify the two new bits
with the collider construction.  The encoded prior theorem retains the real
independent factors, including their product order and all old latent values.

When both pivots are ignored by other base mechanisms, applying this same
construction to an observationally equal pair preserves the complete observed
laws.  In a hedge carrier this non-influence holds at a kept root and at a
parent outside the large forest.  It is not assumed for every active-path
vertex.  Supported noise separately preserves full observed-alphabet positivity.

These are semantic construction and evaluation theorems.  General conditional
completeness still needs to choose and compose the appropriate path gadgets,
and to connect their conditional probabilities to the original query.  In
particular, the mere presence of a declared incoming parent is not asserted
to be a universal conditional countermodel theorem.
-/

namespace ConditionalCollider

/-- Only the declared parent's actual value is read by the child. -/
def parentSignal (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count)
    (edge : S.directed parent child = true) : S.ParentValues child -> Bool :=
  fun parents => hedgeIsSecond rich parent (parents parent edge)

/-- The fair input is a real fresh private latent source, not a replacement
of the old model's joint prior by a hypothesized independent distribution. -/
def maskModel (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent : Fin S.count) : ExactModel S :=
  base.withHedgeReadout rich parent ColliderChannel.fairMask false (fun _ => false)

/-- Install the collider after the earlier parent.  All other local
mechanisms, shared incidences, and original observed value types are retained. -/
def model (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) : ExactModel S :=
  (maskModel base rich parent).withHedgeReadout rich child noise true
    (parentSignal rich parent child edge)

/-- Explicitly encode both independent private inputs in the real extended
latent assignment.  The mask is installed first and the collider noise last. -/
def assignment (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (maskBit noiseBit : Bool) (old : base.latent.Assignment) :
    (model base rich parent child edge noise).latent.Assignment :=
  PrivateBooleanNoise.assignment (maskModel base rich parent).latent noiseBit
    (PrivateBooleanNoise.assignment base.latent maskBit old)

theorem compatible (base : ExactModel S) {graph : ObservedGraph S}
    (baseCompatible : Compatible base graph) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) : Compatible (model base rich parent child edge noise) graph :=
  FiniteLatentSCM.withHedgeReadout_compatible _
    (base.withHedgeReadout_compatible baseCompatible rich parent ColliderChannel.fairMask false (fun _ => false))
    rich child noise true (parentSignal rich parent child edge)

/-- The fair parent update cannot introduce a dependence on its later
child.  This is acyclicity of the declared edge, not a new independence axiom. -/
theorem maskModel_ignores_child (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (ignored : base.OtherMechanismsIgnore child) :
    (maskModel base rich parent).OtherMechanismsIgnore child :=
  base.withPrivateBooleanNoise_otherMechanismsIgnore_of_earlier parent child
    ColliderChannel.fairMask
    (fun parents inputs bit => hedgeNoisyReadout rich parent false (fun _ => false)
      parents (base.mechanism parent parents inputs) bit) ignored (S.directed_earlier edge)

/-- Both fresh factors have explicitly supported bit values.  The restoring
argument preserves every old observed label, not only two parity labels. -/
theorem positive (base : ExactModel S) (basePositive : ObservationallyPositive base)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count)
    (edge : S.directed parent child = true) (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit)) :
    ObservationallyPositive (model base rich parent child edge noise) := by
  have fairPositive : forall bit, ColliderChannel.fairMask.EventPositive
      (FiniteProbRecord.singletonEvent bit) := by
    intro bit
    cases bit <;> decide +kernel
  exact FiniteLatentSCM.withHedgeReadout_positive _
    (base.withHedgeReadout_positive basePositive rich parent ColliderChannel.fairMask
      fairPositive false (fun _ => false)) rich child noise noisePositive true
    (parentSignal rich parent child edge)

/-- The same two-step observable update preserves the full observational
equality of the base pair.  This does not assume equality of the new tables. -/
theorem observationally_equivalent (left right : ExactModel S)
    (baseEqual : ObservationallyEquivalent left right) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (leftParentIgnored : left.OtherMechanismsIgnore parent)
    (rightParentIgnored : right.OtherMechanismsIgnore parent)
    (leftChildIgnored : left.OtherMechanismsIgnore child)
    (rightChildIgnored : right.OtherMechanismsIgnore child) (noise : FiniteProbRecord Bool) :
    ObservationallyEquivalent (model left rich parent child edge noise)
      (model right rich parent child edge noise) := by
  have maskedEqual := FiniteLatentSCM.withPrivateReadout_observationally_equivalent left right
    baseEqual parent ColliderChannel.fairMask (hedgeNoisyReadout rich parent false (fun _ => false))
    leftParentIgnored rightParentIgnored
  exact FiniteLatentSCM.withPrivateReadout_observationally_equivalent
    (maskModel left rich parent) (maskModel right rich parent) maskedEqual child noise
    (hedgeNoisyReadout rich child true (parentSignal rich parent child edge))
    (maskModel_ignores_child left rich parent child edge leftChildIgnored)
    (maskModel_ignores_child right rich parent child edge rightChildIgnored)

/-! ## Exact interventional bit equations and preserved context values -/

private theorem maskModel_bit (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent : Fin S.count) (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : intervention parent = none) (old : base.latent.Assignment) (bit : Bool) :
    hedgeIsSecond rich parent ((maskModel base rich parent).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent bit old) parent) = bit := by
  change hedgeIsSecond rich parent ((base.withPrivateReadout parent ColliderChannel.fairMask
    (hedgeNoisyReadout rich parent false (fun _ => false))).evalNodeUnder intervention
      (PrivateBooleanNoise.assignment base.latent bit old) parent) = bit
  rw [base.withPrivateReadout_evalNodeUnder_pivot parent ColliderChannel.fairMask
    (hedgeNoisyReadout rich parent false (fun _ => false)) intervention free old bit]
  simp only [hedgeNoisyReadout, hedgeIsSecond_parityCarrierValue, Bool.false_eq_true,
    ↓reduceIte, Bool.false_xor]

/-- At the two free pivots the actual SCM has exactly the fair-input and
noisy-collider equations.  The old child signal is independent of the mask
because every old mechanism other than the parent ignores that parent. -/
theorem bit_equations (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (ignored : base.OtherMechanismsIgnore parent)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (old : base.latent.Assignment) (maskBit noiseBit : Bool) :
    hedgeIsSecond rich parent ((model base rich parent child edge noise).evalUnder intervention
      (assignment base rich parent child edge noise maskBit noiseBit old) parent) = maskBit ∧
    hedgeIsSecond rich child ((model base rich parent child edge noise).evalUnder intervention
      (assignment base rich parent child edge noise maskBit noiseBit old) child) =
      Bool.xor (Bool.xor (hedgeIsSecond rich child (base.evalUnder intervention old child)) maskBit) noiseBit := by
  let masked := maskModel base rich parent
  let maskedUnit := PrivateBooleanNoise.assignment base.latent maskBit old
  have earlier := S.directed_earlier edge
  have different : child ≠ parent := by
    intro same
    rw [same] at earlier
    exact Nat.lt_irrefl _ earlier
  constructor
  · change hedgeIsSecond rich parent ((masked.withPrivateReadout child noise
      (hedgeNoisyReadout rich child true (parentSignal rich parent child edge))).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment masked.latent noiseBit maskedUnit) parent) = maskBit
    have unchanged := masked.withPrivateBooleanNoise_evalNodeUnder_eq_of_before child noise
      (fun parents inputs bit => hedgeNoisyReadout rich child true (parentSignal rich parent child edge)
        parents (masked.mechanism child parents inputs) bit)
      intervention maskedUnit noiseBit parent earlier
    exact (congrArg (hedgeIsSecond rich parent) unchanged).trans
      (maskModel_bit base rich parent intervention parentFree old maskBit)
  · change hedgeIsSecond rich child ((masked.withPrivateReadout child noise
      (hedgeNoisyReadout rich child true (parentSignal rich parent child edge))).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment masked.latent noiseBit maskedUnit) child) = _
    rw [masked.withPrivateReadout_evalNodeUnder_pivot child noise
      (hedgeNoisyReadout rich child true (parentSignal rich parent child edge))
      intervention childFree maskedUnit noiseBit]
    simp only [hedgeNoisyReadout, hedgeIsSecond_parityCarrierValue, if_true, parentSignal]
    have childUnchanged := base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne parent
      ColliderChannel.fairMask
      (fun parents inputs bit => hedgeNoisyReadout rich parent false (fun _ => false)
        parents (base.mechanism parent parents inputs) bit)
      ignored intervention old maskBit child different
    change (maskModel base rich parent).evalUnder intervention maskedUnit child =
      base.evalUnder intervention old child at childUnchanged
    have childBit := congrArg (hedgeIsSecond rich child) childUnchanged
    have parentBit := maskModel_bit base rich parent intervention parentFree old maskBit
    have inputs :
        (hedgeIsSecond rich child (masked.evalUnder intervention maskedUnit child),
          hedgeIsSecond rich parent (masked.evalUnder intervention maskedUnit parent)) =
        (hedgeIsSecond rich child (base.evalUnder intervention old child), maskBit) :=
      Prod.ext childBit parentBit
    exact congrArg (fun pair : Bool × Bool => Bool.xor (Bool.xor pair.1 pair.2) noiseBit)
      inputs

/-- Every other observed coordinate is unchanged at the encoded inputs
under the two non-influence hypotheses.  Arbitrary context events supported
away from these pivots can therefore use the original source context. -/
theorem evalUnder_of_away (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool) (parentIgnored : base.OtherMechanismsIgnore parent)
    (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (maskBit noiseBit : Bool) (node : Fin S.count)
    (notParent : node ≠ parent) (notChild : node ≠ child) :
    (model base rich parent child edge noise).evalUnder intervention
      (assignment base rich parent child edge noise maskBit noiseBit old) node =
      base.evalUnder intervention old node := by
  exact (FiniteLatentSCM.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne
    (maskModel base rich parent) child noise
    (fun parents inputs bit => hedgeNoisyReadout rich child true (parentSignal rich parent child edge)
      parents ((maskModel base rich parent).mechanism child parents inputs) bit)
    (maskModel_ignores_child base rich parent child edge childIgnored) intervention
    (PrivateBooleanNoise.assignment base.latent maskBit old) noiseBit node notChild).trans
      (base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne parent ColliderChannel.fairMask
        (fun parents inputs bit => hedgeNoisyReadout rich parent false (fun _ => false)
          parents (base.mechanism parent parents inputs) bit)
        parentIgnored intervention old maskBit node notParent)

/-- The whole extended prior is the encoded independent product, including
all mixed events.  Its noise-first order is the actual installation order,
not an informal identification with a detached signal distribution. -/
theorem prior_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool)
    (event : Event (model base rich parent child edge noise).latent.Assignment) :
    QProb.Equiv ((model base rich parent child edge noise).prior.probVal event)
      ((noise.product (ColliderChannel.fairMask.product base.prior)).probVal
        (fun triple => event (assignment base rich parent child edge noise triple.2.1 triple.1 triple.2.2))) := by
  let masked := maskModel base rich parent
  let encodedEvent : Event (Bool × masked.latent.Assignment) := fun pair =>
    event (PrivateBooleanNoise.assignment masked.latent pair.1 pair.2)
  have pushed := (noise.product masked.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment masked.latent pair.1 pair.2) event
  have first := noise.product_map_right_probVal (ColliderChannel.fairMask.product base.prior)
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2) encodedEvent
  exact QProb.equiv_trans pushed first

end ConditionalCollider

/-- A kept hedge root and an incoming parent outside the large forest
supply the two non-influence hypotheses internally.  The resulting actual
SCMs have equal complete observational laws, without a supplied equality
of modified tables or an assumed conditional counterexample. -/
theorem HedgeWitness.carrierConditionalColliderModels_observationally_equivalent
    {graph : ObservedGraph S} {query : JointKernelQuery S}
    (w : HedgeWitness graph query) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (outside : w.large parent = false) (root : w.roots child = true)
    (noise : FiniteProbRecord Bool) :
    ObservationallyEquivalent
      (ConditionalCollider.model (w.largeCarrierDefectParityModel rich) rich parent child edge noise)
      (ConditionalCollider.model (w.smallCarrierDefectParityModel rich) rich parent child edge noise) := by
  have parentNone := w.large_forest.child_off_set parent outside
  have childNone := ((w.large_forest.roots_exact child).mp root).2
  exact ConditionalCollider.observationally_equivalent _ _
    (w.carrierDefectParityModels_observationally_equivalent rich) rich parent child edge
    (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich parent parentNone)
    (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich parent parentNone)
    (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich child childNone)
    (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich child childNone) noise

/-- Both collider-updated carrier models belong to the original positive
graph class.  Positivity is independent of the geometric sink hypotheses
used for observational replay; here only the declared parent edge is needed. -/
theorem HedgeWitness.carrierConditionalColliderModels_mem
    {graph : ObservedGraph S} {query : JointKernelQuery S}
    (w : HedgeWitness graph query) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : S.directed parent child = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit)) :
    (GraphModelClass.positive graph).Mem
        (ConditionalCollider.model (w.largeCarrierDefectParityModel rich) rich parent child edge noise) ∧
      (GraphModelClass.positive graph).Mem
        (ConditionalCollider.model (w.smallCarrierDefectParityModel rich) rich parent child edge noise) :=
  ⟨⟨ConditionalCollider.compatible _ (w.largeCarrierDefectParityModel_compatible rich)
      rich parent child edge noise,
    ConditionalCollider.positive _ (w.largeCarrierDefectParityModel_positive rich)
      rich parent child edge noise noisePositive⟩,
    ⟨ConditionalCollider.compatible _ (w.smallCarrierDefectParityModel_compatible rich)
      rich parent child edge noise,
    ConditionalCollider.positive _ (w.smallCarrierDefectParityModel_positive rich)
      rich parent child edge noise noisePositive⟩⟩

end Causality
end Thesis
