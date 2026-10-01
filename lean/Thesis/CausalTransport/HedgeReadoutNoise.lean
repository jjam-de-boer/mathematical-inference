import Thesis.CausalTransport.HedgeReadoutEvaluation
import Thesis.Probability.BooleanNoise

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Integrating the actual independent factors of a finite readout plan

A pointwise readout identity is not by itself a probability identity.  Each
instruction appends an actual private Boolean to the previous SCM's latent
assignment, and its prior is the literal pushforward of `noise × old prior`.
The argument here eliminates those real factors one at a time, using the
finite biased-XOR cancellation theorem.  It does not postulate a coupling,
an independent signal record, or equal denominators for the two base models.

The final Boolean signals may be arbitrary functions of their respective
latent spaces.  The supplied pointwise identities must identify them with
the old signals XOR the parity of every installed fresh input.  Distinct
pivots ensure that a node-indexed bit family represents every independent
coordinate: unlike repeated-pivot plans, it never forces two fresh factors
to share the same represented input.  Order, graph shape, and mechanism
non-influence are irrelevant at this prior-integration boundary.

Every instruction may have its own finite weighted noise record and positive
bias gap.  Full support is a separate condition needed by countermodels;
neither support nor a binary observed alphabet is assumed by this theorem.

The slice-comparison theorem below has a different purpose: it integrates
equality proved separately at each fixed fresh-input family.  Its events need
not be parity signals, and it requires neither bias nor support.  This is the
probability boundary for full-alphabet denominator comparisons obtained from
partial-incidence counting; a Boolean signal identity alone would not justify
those comparisons.
-/

/-- Parity of all represented private inputs in an explicit readout plan.
It counts instructions, not changed observed coordinates.  Probability
integration below requires distinct pivots when using this node-indexed
representation of independent inputs. -/
def hedgeReadoutFreshParity (steps : List (HedgeReadoutStep S)) (bits : Fin S.count -> Bool) : Bool :=
  steps.foldl (fun total step => Bool.xor total (bits step.pivot)) false

namespace HedgeReadoutNoise

variable {rich : ObservedSignature.ValueRich S}

/-- The existing coordinates of an augmented latent unit, recovered with
their original dependent types.  No support point is selected. -/
private def oldAssignment (base : ExactModel S) (step : HedgeReadoutStep S)
    (unit : (step.apply rich base).latent.Assignment) : base.latent.Assignment :=
  fun root => cast (PrivateBooleanNoise.value_castSucc base.latent root) (unit root.castSucc)

private def freshBit (base : ExactModel S) (step : HedgeReadoutStep S)
    (unit : (step.apply rich base).latent.Assignment) : Bool :=
  cast (PrivateBooleanNoise.value_last base.latent) (unit (Fin.last base.latent.count))

private theorem oldAssignment_encoded (base : ExactModel S) (step : HedgeReadoutStep S)
    (rich : ObservedSignature.ValueRich S) (bit : Bool) (unit : base.latent.Assignment) :
    oldAssignment base step (rich := rich) (PrivateBooleanNoise.assignment base.latent bit unit) = unit := by
  funext root
  exact PrivateBooleanNoise.assignment_castSucc base.latent bit unit root

private theorem freshBit_encoded (base : ExactModel S) (step : HedgeReadoutStep S)
    (rich : ObservedSignature.ValueRich S) (bit : Bool) (unit : base.latent.Assignment) :
    freshBit base step (rich := rich) (PrivateBooleanNoise.assignment base.latent bit unit) = bit :=
  PrivateBooleanNoise.assignment_last base.latent bit unit

/-- Every augmented unit is represented, including units outside prior
support.  Constructive last/initial cases avoid the choice-dependent standard
`Fin.lastCases_castSucc` reduction lemma. -/
private theorem assignment_eta (base : ExactModel S) (step : HedgeReadoutStep S)
    (rich : ObservedSignature.ValueRich S) (unit : (step.apply rich base).latent.Assignment) :
    PrivateBooleanNoise.assignment base.latent (freshBit base step unit) (oldAssignment base step unit) = unit := by
  funext root
  refine FiniteProduct.snocCases (motive := fun root =>
    PrivateBooleanNoise.assignment base.latent (freshBit base step unit) (oldAssignment base step unit) root = unit root)
    ?_ (fun initial => ?_) root
  · simp only [PrivateBooleanNoise.assignment, freshBit, FiniteProduct.extend_last, cast_cast, cast_eq]
  · simp only [PrivateBooleanNoise.assignment, oldAssignment, FiniteProduct.extend_castSucc, cast_cast, cast_eq]

private def overwrite (pivot : Fin S.count) (value : Bool) (bits : Fin S.count -> Bool) : Fin S.count -> Bool :=
  fun node => if node = pivot then value else bits node

private theorem parity_cons (step : HedgeReadoutStep S) (rest : List (HedgeReadoutStep S))
    (bits : Fin S.count -> Bool) :
    hedgeReadoutFreshParity (step :: rest) bits = Bool.xor (bits step.pivot) (hedgeReadoutFreshParity rest bits) := by
  unfold hedgeReadoutFreshParity
  rw [List.foldl_cons, Bool.false_xor, foldl_xor_init]

private theorem parity_congr (steps : List (HedgeReadoutStep S)) (left right : Fin S.count -> Bool)
    (same : forall step, step ∈ steps -> left step.pivot = right step.pivot) :
    hedgeReadoutFreshParity steps left = hedgeReadoutFreshParity steps right := by
  unfold hedgeReadoutFreshParity
  apply foldl_congr_of_mem
  intro total step listed
  exact congrArg (Bool.xor total) (same step listed)

private theorem assignment_congr (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) (left right : Fin S.count -> Bool) (unit : base.latent.Assignment)
    (same : forall step, step ∈ steps -> left step.pivot = right step.pivot) :
    base.hedgeReadoutAssignment rich left steps unit = base.hedgeReadoutAssignment rich right steps unit := by
  induction steps generalizing base with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      change (step.apply rich base).hedgeReadoutAssignment rich left rest
          (PrivateBooleanNoise.assignment base.latent (left step.pivot) unit) =
        (step.apply rich base).hedgeReadoutAssignment rich right rest
          (PrivateBooleanNoise.assignment base.latent (right step.pivot) unit)
      rw [same step List.mem_cons_self]
      exact inductionHypothesis _ _ (fun next listed => same next (List.mem_cons_of_mem _ listed))

/-- The signal after installing the first real factor, before installing
the tail.  Its definition decodes the factor rather than treating the new
Boolean as an external random variable detached from the SCM. -/
private def headSignal (base : ExactModel S) (rich : ObservedSignature.ValueRich S) (step : HedgeReadoutStep S)
    (source : base.latent.Assignment -> Bool) : (step.apply rich base).latent.Assignment -> Bool :=
  fun unit => Bool.xor (source (oldAssignment base step unit)) (freshBit base step unit)

/-- Peel off the first input in a pointwise whole-plan identity.  Its
coordinate is overwritten only in the supplied representation, not in the
actual SCM: distinctness proves that none of the remaining independent
coordinates has been changed by that overwrite. -/
private theorem tail_equation (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (step : HedgeReadoutStep S) (rest : List (HedgeReadoutStep S))
    (distinct : forall next, next ∈ rest -> step.pivot ≠ next.pivot)
    (source : base.latent.Assignment -> Bool)
    (signal : (base.withHedgeReadouts rich (step :: rest)).latent.Assignment -> Bool)
    (equation : forall bits unit, signal (base.hedgeReadoutAssignment rich bits (step :: rest) unit) =
      Bool.xor (source unit) (hedgeReadoutFreshParity (step :: rest) bits)) :
    forall bits unit, signal ((step.apply rich base).hedgeReadoutAssignment rich bits rest unit) =
      Bool.xor (headSignal base rich step source unit) (hedgeReadoutFreshParity rest bits) := by
  intro bits unit
  let amended := overwrite step.pivot (freshBit base step unit) bits
  have headBit : amended step.pivot = freshBit base step unit := by simp only [amended, overwrite, ite_true]
  have tailBits : forall next, next ∈ rest -> amended next.pivot = bits next.pivot := by
    intro next listed
    exact if_neg (Ne.symm (distinct next listed))
  have whole := equation amended (oldAssignment base step unit)
  change signal ((step.apply rich base).hedgeReadoutAssignment rich amended rest
      (PrivateBooleanNoise.assignment base.latent (amended step.pivot) (oldAssignment base step unit))) =
    Bool.xor (source (oldAssignment base step unit)) (hedgeReadoutFreshParity (step :: rest) amended) at whole
  rw [headBit, assignment_eta base step rich unit,
    assignment_congr (step.apply rich base) rich rest amended bits unit tailBits,
    parity_cons, headBit, parity_congr rest amended bits tailBits] at whole
  exact whole.trans (Bool.xor_assoc _ _ _).symm

/-- The head signal's real prior is the independent XOR channel.  This
uses the actual encoded product prior, including all old weighted atoms. -/
private theorem headSignal_probVal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (step : HedgeReadoutStep S) (source : base.latent.Assignment -> Bool) :
    QProb.Equiv ((step.apply rich base).prior.probVal (headSignal base rich step source))
      ((base.prior.xorChannel source step.noise).probVal id) := by
  have pushed := (step.noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2) (headSignal base rich step source)
  have decoded := (step.noise.product base.prior).probVal_congr
    (fun pair => headSignal base rich step source (PrivateBooleanNoise.assignment base.latent pair.1 pair.2))
    (fun pair => Bool.xor (source pair.2) pair.1) (by
      intro pair
      simp only [headSignal, oldAssignment_encoded, freshBit_encoded])
  exact QProb.equiv_trans pushed (QProb.equiv_trans decoded
    (FiniteProbRecord.xorChannel_noise_first_probVal base.prior source step.noise))

end HedgeReadoutNoise

/-! ## Integrating full-event comparisons at fixed fresh inputs -/

/-- Equality on every encoded fresh-input slice gives equality under the
actual augmented priors.  Events may inspect complete observed labels, and
the old latent spaces, weights, and denominators may differ.

Each induction step uses the literal pushforward of `noise × old prior`.
Fixing that factor overwrites just the head's entry in the represented bit
family; distinct pivots prove that no independent tail entry was changed.
Thus no probability law or independence assumption is inferred merely from
a node-indexed encoding.  Ordering, graph conditions, support, and bias are
not needed.  Repeated pivots are deliberately excluded from this particular
encoding theorem: they need an instruction-indexed slice representation. -/
theorem FiniteLatentSCM.withHedgeReadouts_prior_equiv_of_encodedSlices
    (left right : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (distinct : steps.Pairwise (fun first second => first.pivot ≠ second.pivot))
    (leftEvent : Event (left.withHedgeReadouts rich steps).latent.Assignment)
    (rightEvent : Event (right.withHedgeReadouts rich steps).latent.Assignment)
    (slices : forall bits : Fin S.count -> Bool,
      QProb.Equiv
        (left.prior.probVal (fun unit => leftEvent (left.hedgeReadoutAssignment rich bits steps unit)))
        (right.prior.probVal (fun unit => rightEvent (right.hedgeReadoutAssignment rich bits steps unit)))) :
    QProb.Equiv ((left.withHedgeReadouts rich steps).prior.probVal leftEvent)
      ((right.withHedgeReadouts rich steps).prior.probVal rightEvent) := by
  induction steps generalizing left right with
  | nil => exact slices (fun _node => false)
  | cons step rest inductionHypothesis =>
      have different := (List.pairwise_cons.mp distinct).1
      apply inductionHypothesis (step.apply rich left) (step.apply rich right)
        (List.pairwise_cons.mp distinct).2 leftEvent rightEvent
      intro bits
      let leftSlice : Event (step.apply rich left).latent.Assignment :=
        fun unit => leftEvent ((step.apply rich left).hedgeReadoutAssignment rich bits rest unit)
      let rightSlice : Event (step.apply rich right).latent.Assignment :=
        fun unit => rightEvent ((step.apply rich right).hedgeReadoutAssignment rich bits rest unit)
      let leftProduct : Event (Bool × left.latent.Assignment) :=
        fun pair => leftSlice (PrivateBooleanNoise.assignment left.latent pair.1 pair.2)
      let rightProduct : Event (Bool × right.latent.Assignment) :=
        fun pair => rightSlice (PrivateBooleanNoise.assignment right.latent pair.1 pair.2)
      have productEqual := step.noise.product_probVal_equiv_of_slices
        left.prior right.prior leftProduct rightProduct (by
          intro bit
          let amended := HedgeReadoutNoise.overwrite step.pivot bit bits
          have headBit : amended step.pivot = bit := by
            simp only [amended, HedgeReadoutNoise.overwrite, ite_true]
          have tailBits : forall next, next ∈ rest -> bits next.pivot = amended next.pivot := by
            intro next listed
            exact (if_neg (Ne.symm (different next listed))).symm
          have leftEncoded (unit : left.latent.Assignment) : leftProduct (bit, unit) =
              leftEvent (left.hedgeReadoutAssignment rich amended (step :: rest) unit) := by
            change leftEvent ((step.apply rich left).hedgeReadoutAssignment rich bits rest
              (PrivateBooleanNoise.assignment left.latent bit unit)) =
              leftEvent ((step.apply rich left).hedgeReadoutAssignment rich amended rest
                (PrivateBooleanNoise.assignment left.latent (amended step.pivot) unit))
            rw [headBit]
            exact congrArg leftEvent
              (HedgeReadoutNoise.assignment_congr (step.apply rich left) rich rest bits amended _ tailBits)
          have rightEncoded (unit : right.latent.Assignment) : rightProduct (bit, unit) =
              rightEvent (right.hedgeReadoutAssignment rich amended (step :: rest) unit) := by
            change rightEvent ((step.apply rich right).hedgeReadoutAssignment rich bits rest
              (PrivateBooleanNoise.assignment right.latent bit unit)) =
              rightEvent ((step.apply rich right).hedgeReadoutAssignment rich amended rest
                (PrivateBooleanNoise.assignment right.latent (amended step.pivot) unit))
            rw [headBit]
            exact congrArg rightEvent
              (HedgeReadoutNoise.assignment_congr (step.apply rich right) rich rest bits amended _ tailBits)
          exact QProb.equiv_trans (left.prior.probVal_congr _ _ leftEncoded)
            (QProb.equiv_trans (slices amended)
              (QProb.equiv_symm (right.prior.probVal_congr _ _ rightEncoded))))
      have leftPushed := (step.noise.product left.prior).map_probVal
        (fun pair => PrivateBooleanNoise.assignment left.latent pair.1 pair.2) leftSlice
      have rightPushed := (step.noise.product right.prior).map_probVal
        (fun pair => PrivateBooleanNoise.assignment right.latent pair.1 pair.2) rightSlice
      exact QProb.equiv_trans leftPushed
        (QProb.equiv_trans productEqual (QProb.equiv_symm rightPushed))

/-! ## Finite-plan preservation and reflection of signal separation -/

/-- Integrating the actual fresh factors preserves and reflects equality
of the two original Boolean signal probabilities.  Both final signal
identities must hold on every encoded old unit and fresh input.  The priors
may have different dependent latent spaces, denominators, and atom weights.

Distinct pivots make the node-indexed representation exhaustive for all
independent inputs; bias cancellation then removes one genuine factor at a
time.  No graph, ordering, non-influence, support, or observed-alphabet
hypothesis is hidden in this probability boundary. -/
theorem FiniteLatentSCM.withHedgeReadouts_prior_parity_equiv_iff
    (left right : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (distinct : steps.Pairwise (fun first second => first.pivot ≠ second.pivot))
    (gap : Fin S.count -> Nat) (gapPositive : forall step, step ∈ steps -> 0 < gap step.pivot)
    (bias : forall step, step ∈ steps -> FiniteProbRecord.eventMass step.noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass step.noise.atoms id + gap step.pivot)
    (leftSource : left.latent.Assignment -> Bool) (rightSource : right.latent.Assignment -> Bool)
    (leftSignal : (left.withHedgeReadouts rich steps).latent.Assignment -> Bool)
    (rightSignal : (right.withHedgeReadouts rich steps).latent.Assignment -> Bool)
    (leftEquation : forall bits unit, leftSignal (left.hedgeReadoutAssignment rich bits steps unit) =
      Bool.xor (leftSource unit) (hedgeReadoutFreshParity steps bits))
    (rightEquation : forall bits unit, rightSignal (right.hedgeReadoutAssignment rich bits steps unit) =
      Bool.xor (rightSource unit) (hedgeReadoutFreshParity steps bits)) :
    QProb.Equiv ((left.withHedgeReadouts rich steps).prior.probVal leftSignal)
        ((right.withHedgeReadouts rich steps).prior.probVal rightSignal) ↔
      QProb.Equiv (left.prior.probVal leftSource) (right.prior.probVal rightSource) := by
  induction steps generalizing left right with
  | nil =>
      have leftSame := left.prior.probVal_congr leftSignal leftSource (by
        intro unit
        exact (leftEquation (fun _node => false) unit).trans (Bool.xor_false _))
      have rightSame := right.prior.probVal_congr rightSignal rightSource (by
        intro unit
        exact (rightEquation (fun _node => false) unit).trans (Bool.xor_false _))
      exact ⟨fun equivalent => QProb.equiv_trans (QProb.equiv_symm leftSame) (QProb.equiv_trans equivalent rightSame),
        fun equivalent => QProb.equiv_trans leftSame (QProb.equiv_trans equivalent (QProb.equiv_symm rightSame))⟩
  | cons step rest inductionHypothesis =>
      have tail := inductionHypothesis (step.apply rich left) (step.apply rich right)
        (List.pairwise_cons.mp distinct).2
        (fun next listed => gapPositive next (List.mem_cons_of_mem _ listed))
        (fun next listed => bias next (List.mem_cons_of_mem _ listed))
        (HedgeReadoutNoise.headSignal left rich step leftSource) (HedgeReadoutNoise.headSignal right rich step rightSource)
        leftSignal rightSignal
        (HedgeReadoutNoise.tail_equation left rich step rest (List.pairwise_cons.mp distinct).1 leftSource leftSignal leftEquation)
        (HedgeReadoutNoise.tail_equation right rich step rest (List.pairwise_cons.mp distinct).1 rightSource rightSignal rightEquation)
      have leftChannel := HedgeReadoutNoise.headSignal_probVal left rich step leftSource
      have rightChannel := HedgeReadoutNoise.headSignal_probVal right rich step rightSource
      have cancel := FiniteProbRecord.xorChannel_probVal_equiv_iff_of_bias left.prior leftSource right.prior rightSource
        step.noise (gap step.pivot) (gapPositive step List.mem_cons_self) (bias step List.mem_cons_self)
      exact ⟨fun equivalent => cancel.mp (QProb.equiv_trans (QProb.equiv_symm leftChannel)
          (QProb.equiv_trans (tail.mp equivalent) rightChannel)),
        fun equivalent => tail.mpr (QProb.equiv_trans leftChannel
          (QProb.equiv_trans (cancel.mpr equivalent) (QProb.equiv_symm rightChannel)))⟩

end Causality
end Thesis
