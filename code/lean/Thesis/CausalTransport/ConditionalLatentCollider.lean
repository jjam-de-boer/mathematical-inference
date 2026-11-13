import Thesis.Causality.SharedNoiseSemantics
import Thesis.Causality.PrivateNoiseResponse
import Thesis.CausalTransport.HedgeReadout
import Thesis.Probability.ColliderChannel

namespace Thesis
namespace Causality

open Probability

/-!
# A full-alphabet collider readout through a shared latent parent

The observed incoming-parent construction reads its parent's value through a
declared directed arrow.  An active back-door path may instead start at a
latent pair.  Here a fair mask is an actual fresh source incident to both
displayed observed coordinates; the conditioned child's mechanism reads that
mask through its declared latent input, not an undeclared observed arrow.

The fair-mask step modifies only the queried parent.  The child is left at
its original full value.  Its later private-noise replacement combines that
old value, the incident shared mask, and independent noise in a single
carrier emission.  This order matters on nonbinary alphabets: emitting a
masked child value first could discard a third background label irreversibly.

The module proves compatibility on an existing bidirected edge, full observed
positivity, and preservation of the complete observed law.  The local latent
response is proved to be a common observable response before invoking the
probability bridge.  These are real SCMs, not abstract Boolean channels.
Their conditional kernel gap still needs the separate posterior argument;
no universal conditional countermodel is asserted by importing this module.
-/

variable {S : ObservedSignature.{0}}

namespace ConditionalLatentCollider

/-- Only the queried parent emits the fair bit; the other incident child
keeps its original observed value until mask and private noise are combined. -/
def maskReadout (rich : ObservedSignature.ValueRich S) (parent : Fin S.count)
    (node : Fin S.count) (old : S.Value node) (bit : Bool) : S.Value node :=
  if node = parent then hedgeParityCarrierValue rich node bit old else old

def maskModel (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) : ExactModel S :=
  base.withSharedReadout parent child ColliderChannel.fairMask (maskReadout rich parent)

/-- The actual appended source value in any latent unit of the mask model.
No latent unit is chosen from an existence or support proposition. -/
def maskValue (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (unit : (maskModel base rich parent child).latent.Assignment) : Bool :=
  cast (PrivateBooleanNoise.value_last base.latent) (unit (Fin.last base.latent.count))

def maskInput (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (inputs : (maskModel base rich parent child).latent.Inputs child) : Bool :=
  SharedBooleanNoise.bit base.latent parent child child
    (by simp only [SharedBooleanNoise.membership, decide_true, Bool.or_true]) inputs

theorem maskInput_value (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (unit : (maskModel base rich parent child).latent.Assignment) :
    maskInput base rich parent child (fun root _selected => unit root) = maskValue base rich parent child unit := rfl

/-- Combine all three bits before emitting the old full-value background.
The replacement's shared mask comes from an incident latent input. -/
def replacement (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) : S.ParentValues child -> (maskModel base rich parent child).latent.Inputs child -> Bool -> S.Value child :=
  fun parents inputs noise =>
    let old := (maskModel base rich parent child).mechanism child parents inputs
    hedgeParityCarrierValue rich child
      (Bool.xor (Bool.xor (hedgeIsSecond rich child old) (maskInput base rich parent child inputs)) noise) old

def model (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (noise : FiniteProbRecord Bool) : ExactModel S :=
  (maskModel base rich parent child).withPrivateBooleanNoise child noise (replacement base rich parent child)

/-- Encode both actual independent inputs.  The source shared by the pair
is installed before the child's private noise, matching the literal prior. -/
def assignment (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (noise : FiniteProbRecord Bool)
    (maskBit noiseBit : Bool) (old : base.latent.Assignment) :
    (model base rich parent child noise).latent.Assignment :=
  PrivateBooleanNoise.assignment (maskModel base rich parent child).latent noiseBit
    (PrivateBooleanNoise.assignment base.latent maskBit old)

/-- The shared source uses an already declared bidirected edge; the child
noise is private.  Neither step changes any projected observed edge. -/
theorem compatible (base : ExactModel S) {graph : ObservedGraph S}
    (baseCompatible : Compatible base graph) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (edge : graph.bidirected parent child = true) (noise : FiniteProbRecord Bool) :
    Compatible (model base rich parent child noise) graph :=
  (maskModel base rich parent child).withPrivateBooleanNoise_compatible
    (base.withSharedReadout_compatible baseCompatible parent child edge ColliderChannel.fairMask (maskReadout rich parent))
    child noise (replacement base rich parent child)

/-! ## The shared bit is a proved observable parent response -/

private theorem evaluation_mechanism (base : ExactModel S) (unit : base.latent.Assignment) (child : Fin S.count) :
    base.mechanism child (fun parent _edge => base.eval unit parent) (fun root _selected => unit root) = base.eval unit child := by
  change _ = base.evalNodeUnder (FiniteLatentSCM.noIntervention S) unit child
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rfl

/-- The parent's bit equals the actual shared mask at every latent unit,
not merely at the explicitly encoded positive product atoms. -/
theorem maskModel_parent_bit (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (unit : (maskModel base rich parent child).latent.Assignment) :
    hedgeIsSecond rich parent ((maskModel base rich parent child).eval unit parent) = maskValue base rich parent child unit := by
  rw [← evaluation_mechanism]
  simp only [maskModel, FiniteLatentSCM.withSharedReadout, SharedBooleanNoise.membership,
    decide_true, Bool.true_or, dif_pos, maskReadout, if_true]
  rw [hedgeIsSecond_parityCarrierValue]
  rfl

/-- Cancelling the shared bit by the private bit restores the original full
value, including every nonbinary background label. -/
theorem replacement_restore (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (parents : S.ParentValues child)
    (inputs : (maskModel base rich parent child).latent.Inputs child) :
    replacement base rich parent child parents inputs (maskInput base rich parent child inputs) =
      (maskModel base rich parent child).mechanism child parents inputs := by
  dsimp only [replacement]
  have cancel (old mask : Bool) : Bool.xor (Bool.xor old mask) mask = old := by cases old <;> cases mask <;> rfl
  rw [cancel]
  exact hedgeParityCarrierValue_reconstruct rich child _

def response (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count)
    (sample : S.Assignment) (noise : Bool) : S.Value child :=
  hedgeParityCarrierValue rich child
    (Bool.xor (Bool.xor (hedgeIsSecond rich child (sample child)) (hedgeIsSecond rich parent (sample parent))) noise)
    (sample child)

theorem replacement_response (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (unit : (maskModel base rich parent child).latent.Assignment) (noise : Bool) :
    replacement base rich parent child (fun node _edge => (maskModel base rich parent child).eval unit node)
      (fun root _selected => unit root) noise = response rich parent child ((maskModel base rich parent child).eval unit) noise := by
  unfold replacement response
  rw [evaluation_mechanism, maskInput_value, ← maskModel_parent_bit]

/-! ## Positivity and full observed-law preservation -/

theorem maskModel_positive (base : ExactModel S) (basePositive : ObservationallyPositive base)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child) :
    ObservationallyPositive (maskModel base rich parent child) := by
  apply base.withSharedReadout_positive basePositive parent child ColliderChannel.fairMask
    (by intro bit; cases bit <;> decide +kernel) (maskReadout rich parent) parentIgnored childIgnored
    (fun target => hedgeIsSecond rich parent (target parent))
  intro target node _selected
  by_cases same : node = parent
  · subst node
    simp only [maskReadout, if_true]
    exact hedgeParityCarrierValue_reconstruct rich parent _
  · simp only [maskReadout, same, if_false]

theorem positive (base : ExactModel S) (basePositive : ObservationallyPositive base)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit)) :
    ObservationallyPositive (model base rich parent child noise) := by
  apply (maskModel base rich parent child).withPrivateBooleanNoise_positive_of_restores
    (maskModel_positive base basePositive rich parent child parentIgnored childIgnored) child noise noisePositive
    (replacement base rich parent child) (fun target => hedgeIsSecond rich parent (target parent))
  intro target unit oldTarget
  have sharedBit : maskInput base rich parent child (fun root _selected => unit root) = hedgeIsSecond rich parent (target parent) :=
    (maskInput_value base rich parent child unit).trans
      ((maskModel_parent_bit base rich parent child unit).symm.trans
        (congrArg (hedgeIsSecond rich parent) (congrFun oldTarget parent)))
  rw [← sharedBit, replacement_restore, ← oldTarget]
  exact evaluation_mechanism _ unit child

/-- First compare the common shared-mask observable update, then the proved
latent-dependent child response.  The complete observed law is preserved;
no equality of modified tables or kernels is supplied by the caller. -/
theorem observationally_equivalent (left right : ExactModel S)
    (baseEqual : ObservationallyEquivalent left right) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count)
    (leftParentIgnored : left.OtherMechanismsIgnore parent) (rightParentIgnored : right.OtherMechanismsIgnore parent)
    (leftChildIgnored : left.OtherMechanismsIgnore child) (rightChildIgnored : right.OtherMechanismsIgnore child)
    (noise : FiniteProbRecord Bool) :
    ObservationallyEquivalent (model left rich parent child noise) (model right rich parent child noise) := by
  have maskedEqual := left.withSharedReadout_observationally_equivalent right baseEqual parent child
    ColliderChannel.fairMask (maskReadout rich parent) leftParentIgnored rightParentIgnored leftChildIgnored rightChildIgnored
  exact (maskModel left rich parent child).withPrivateBooleanNoise_observationally_equivalent_of_response
    (maskModel right rich parent child) maskedEqual child noise
    (replacement left rich parent child) (replacement right rich parent child)
    (left.withSharedReadout_otherMechanismsIgnore parent child child ColliderChannel.fairMask (maskReadout rich parent) leftChildIgnored)
    (right.withSharedReadout_otherMechanismsIgnore parent child child ColliderChannel.fairMask (maskReadout rich parent) rightChildIgnored)
    (response rich parent child) (replacement_response left rich parent child) (replacement_response right rich parent child)

/-! ## Actual interventional bit equations and unchanged context coordinates -/

private theorem maskModel_child (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (different : child ≠ parent)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (childFree : intervention child = none)
    (old : base.latent.Assignment) (bit : Bool) :
    (maskModel base rich parent child).evalUnder intervention (PrivateBooleanNoise.assignment base.latent bit old) child =
      base.evalUnder intervention old child := by
  change (base.withSharedReadout parent child ColliderChannel.fairMask (maskReadout rich parent)).evalNodeUnder
    intervention (PrivateBooleanNoise.assignment base.latent bit old) child = base.evalNodeUnder intervention old child
  rw [base.withSharedReadout_evalNodeUnder parent child ColliderChannel.fairMask (maskReadout rich parent)
    parentIgnored childIgnored intervention old bit child]
  simp only [ObservedSignature.sharedReadoutAssignment, SharedBooleanNoise.membership, decide_true, Bool.or_true,
    if_true, childFree, maskReadout, different, if_false]
  rfl

private theorem maskModel_parent (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (parentFree : intervention parent = none)
    (old : base.latent.Assignment) (bit : Bool) :
    hedgeIsSecond rich parent ((maskModel base rich parent child).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent bit old) parent) = bit := by
  change hedgeIsSecond rich parent ((base.withSharedReadout parent child ColliderChannel.fairMask
    (maskReadout rich parent)).evalNodeUnder intervention (PrivateBooleanNoise.assignment base.latent bit old) parent) = bit
  rw [base.withSharedReadout_evalNodeUnder parent child ColliderChannel.fairMask (maskReadout rich parent)
    parentIgnored childIgnored intervention old bit parent]
  simp only [ObservedSignature.sharedReadoutAssignment, SharedBooleanNoise.membership, decide_true, Bool.true_or,
    if_true, parentFree, maskReadout, hedgeIsSecond_parityCarrierValue]

/-- The actual shared-latent collider has the same bit equations as the
independent probability channel, without needing an observed arrow between
the displayed coordinates.  Each pivot is free under the original action. -/
theorem bit_equations (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (different : child ≠ parent) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (old : base.latent.Assignment) (maskBit noiseBit : Bool) :
    hedgeIsSecond rich parent ((model base rich parent child noise).evalUnder intervention
      (assignment base rich parent child noise maskBit noiseBit old) parent) = maskBit ∧
    hedgeIsSecond rich child ((model base rich parent child noise).evalUnder intervention
      (assignment base rich parent child noise maskBit noiseBit old) child) =
      Bool.xor (Bool.xor (hedgeIsSecond rich child (base.evalUnder intervention old child)) maskBit) noiseBit := by
  let masked := maskModel base rich parent child
  let maskedUnit := PrivateBooleanNoise.assignment base.latent maskBit old
  have maskedIgnored := base.withSharedReadout_otherMechanismsIgnore parent child child ColliderChannel.fairMask
    (maskReadout rich parent) childIgnored
  constructor
  · have unchanged := masked.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne child noise (replacement base rich parent child)
      maskedIgnored intervention maskedUnit noiseBit parent (Ne.symm different)
    exact (congrArg (hedgeIsSecond rich parent) unchanged).trans
      (maskModel_parent base rich parent child parentIgnored childIgnored intervention parentFree old maskBit)
  · change hedgeIsSecond rich child ((masked.withPrivateBooleanNoise child noise (replacement base rich parent child)).evalNodeUnder
      intervention (PrivateBooleanNoise.assignment masked.latent noiseBit maskedUnit) child) = _
    rw [masked.withPrivateBooleanNoise_evalNodeUnder_pivot child noise (replacement base rich parent child)
      intervention childFree maskedUnit noiseBit]
    dsimp only [replacement]
    rw [hedgeIsSecond_parityCarrierValue]
    have oldEquation : (maskModel base rich parent child).mechanism child
        (fun node _edge => masked.evalNodeUnder intervention maskedUnit node)
        (fun root _selected => maskedUnit root) = masked.evalNodeUnder intervention maskedUnit child := by
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder
      rw [childFree]
    have freshMask : maskInput base rich parent child (fun root _selected => maskedUnit root) = maskBit := by
      rw [maskInput_value]
      exact PrivateBooleanNoise.assignment_last base.latent maskBit old
    have childBit : hedgeIsSecond rich child (masked.evalNodeUnder intervention maskedUnit child) =
        hedgeIsSecond rich child (base.evalUnder intervention old child) :=
      congrArg (hedgeIsSecond rich child) (maskModel_child base rich parent child different parentIgnored childIgnored
        intervention childFree old maskBit)
    rw [oldEquation, freshMask, childBit]

/-- Arbitrary full-label contexts away from both displayed coordinates are
unchanged under every intervention.  This is pointwise preservation on the
real encoded product units, not an assumed equality of context probabilities. -/
theorem evalUnder_of_away (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (maskBit noiseBit : Bool) (node : Fin S.count)
    (notParent : node ≠ parent) (notChild : node ≠ child) :
    (model base rich parent child noise).evalUnder intervention
      (assignment base rich parent child noise maskBit noiseBit old) node = base.evalUnder intervention old node := by
  have unchanged := (maskModel base rich parent child).withPrivateBooleanNoise_evalNodeUnder_eq_of_ne child noise
    (replacement base rich parent child)
    (base.withSharedReadout_otherMechanismsIgnore parent child child ColliderChannel.fairMask (maskReadout rich parent) childIgnored)
    intervention (PrivateBooleanNoise.assignment base.latent maskBit old) noiseBit node notChild
  have off : SharedBooleanNoise.membership parent child node = false := by
    simp only [SharedBooleanNoise.membership, notParent, notChild, decide_false, Bool.false_or]
  exact unchanged.trans (by
    unfold maskModel
    rw [base.withSharedReadout_evalNodeUnder parent child ColliderChannel.fairMask (maskReadout rich parent)
      parentIgnored childIgnored intervention old maskBit node]
    simp only [ObservedSignature.sharedReadoutAssignment, off, Bool.false_eq_true, if_false])

/-- The actual augmented prior is the literal independently encoded product
for every mixed event, not only for rectangular events. -/
theorem prior_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (noise : FiniteProbRecord Bool)
    (event : Event (model base rich parent child noise).latent.Assignment) :
    QProb.Equiv ((model base rich parent child noise).prior.probVal event)
      ((noise.product (ColliderChannel.fairMask.product base.prior)).probVal
        (fun triple => event (assignment base rich parent child noise triple.2.1 triple.1 triple.2.2))) := by
  let masked := maskModel base rich parent child
  let encodedEvent : Event (Bool × masked.latent.Assignment) := fun pair =>
    event (PrivateBooleanNoise.assignment masked.latent pair.1 pair.2)
  have pushed := (noise.product masked.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment masked.latent pair.1 pair.2) event
  have first := noise.product_map_right_probVal (ColliderChannel.fairMask.product base.prior)
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2) encodedEvent
  exact QProb.equiv_trans pushed first

end ConditionalLatentCollider
end Causality
end Thesis
