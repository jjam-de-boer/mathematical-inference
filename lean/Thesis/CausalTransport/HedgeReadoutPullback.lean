import Thesis.CausalTransport.HedgeReadoutSequence

namespace Thesis
namespace Causality

open Probability

/-!
# Backward parity substitution through actual private readout SCMs

Routing can merge several root signals, so a separated one-coordinate bit
is not a sufficient invariant.  We instead pull a parity event on the final
outcomes backward through the complete finite readout plan.  Substitution
replaces every occurrence of a modified pivot by the old-bit injection and
its declared-parent signal.  Duplicate coordinates are intentional: XOR
cancels an even number of occurrences, without choosing or sorting support
witnesses.

At one update the pulled event is passed through the actual fresh private
noise channel.  The event either retains that noise bit or cancels it; both
cases preserve separation for biased noise.  The proof uses the model's
literal product prior and common assignment transformation, not an assumed
equality of interventional tables.

This is the interventional companion to `HedgeReadoutSequence`.  A routing
construction must still establish that the fully substituted outcome event
is the hedge's root parity and that its pivots have the initial non-influence
property.  In particular, internal-forest re-entry is not silently included.
-/

variable {S : ObservedSignature.{0}}

/-! ## Parity events retain explicit finite coordinate lists -/

/-- XOR the selected observed bits, retaining duplicates as algebraic data.
This agrees with root parity on the root set's member enumeration. -/
def hedgeParityList (rich : ObservedSignature.ValueRich S)
    (nodes : List (Fin S.count)) (sample : S.Assignment) : Bool :=
  nodes.foldl (fun total node => Bool.xor total (hedgeIsSecond rich node (sample node))) false

theorem hedgeParityList_nil (rich : ObservedSignature.ValueRich S) (sample : S.Assignment) :
    hedgeParityList rich [] sample = false := rfl

theorem hedgeParityList_cons (rich : ObservedSignature.ValueRich S)
    (node : Fin S.count) (nodes : List (Fin S.count)) (sample : S.Assignment) :
    hedgeParityList rich (node :: nodes) sample =
      Bool.xor (hedgeIsSecond rich node (sample node)) (hedgeParityList rich nodes sample) := by
  unfold hedgeParityList
  rw [List.foldl_cons, foldl_xor_init]
  simp only [Bool.false_xor]

theorem hedgeParityList_append (rich : ObservedSignature.ValueRich S)
    (left right : List (Fin S.count)) (sample : S.Assignment) :
    hedgeParityList rich (left ++ right) sample =
      Bool.xor (hedgeParityList rich left sample) (hedgeParityList rich right sample) := by
  unfold hedgeParityList
  rw [List.foldl_append, foldl_xor_init]

/-- A linear readout names all parent coordinates explicitly and proves
that each one is a declared parent.  Duplicate parents are harmless and
allow substitution without a normalization or classical set operation. -/
structure HedgeLinearReadoutStep (S : ObservedSignature.{0}) where
  pivot : Fin S.count
  noise : FiniteProbRecord Bool
  injectOld : Bool
  parents : List (Fin S.count)
  parent_edges : forall parent, parent ∈ parents -> S.directed parent pivot = true

namespace HedgeLinearReadoutStep

/-- The typed parent fold can read only declared parents.  Its finite
membership test makes the callback total; the false branch is unused on
every entry actually folded. -/
def parentSignal (step : HedgeLinearReadoutStep S) (rich : ObservedSignature.ValueRich S)
    (values : S.ParentValues step.pivot) : Bool :=
  step.parents.foldl (fun total parent => Bool.xor total
    (if listed : parent ∈ step.parents then
      hedgeIsSecond rich parent (values parent (step.parent_edges parent listed))
    else false)) false

def toReadoutStep (step : HedgeLinearReadoutStep S) (rich : ObservedSignature.ValueRich S) :
    HedgeReadoutStep S :=
  ⟨step.pivot, step.noise, step.injectOld, step.parentSignal rich⟩

theorem parentSignal_assignment (step : HedgeLinearReadoutStep S)
    (rich : ObservedSignature.ValueRich S) (sample : S.Assignment) :
    step.parentSignal rich (fun parent _edge => sample parent) = hedgeParityList rich step.parents sample := by
  unfold parentSignal hedgeParityList
  apply foldl_congr_of_mem
  intro total parent listed
  rw [dif_pos listed]

/-- The old observed coordinates injected by the updated pivot. -/
def sourceNodes (step : HedgeLinearReadoutStep S) : List (Fin S.count) :=
  if step.injectOld then step.pivot :: step.parents else step.parents

theorem sourceNodes_signal (step : HedgeLinearReadoutStep S)
    (rich : ObservedSignature.ValueRich S) (sample : S.Assignment) :
    hedgeParityList rich step.sourceNodes sample =
      hedgeReadoutSignal rich step.pivot step.injectOld (step.parentSignal rich) sample := by
  unfold sourceNodes hedgeReadoutSignal
  rw [step.parentSignal_assignment rich sample]
  cases step.injectOld <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor,
    hedgeParityList_cons]

/-- Substitute the old source coordinates for each modified-pivot
occurrence in the requested event.  Non-pivot coordinates remain literal
singletons, and duplicates are not discarded. -/
def pullbackNodes (step : HedgeLinearReadoutStep S) : List (Fin S.count) -> List (Fin S.count)
  | [] => []
  | node :: rest =>
      (if node = step.pivot then step.sourceNodes else [node]) ++ step.pullbackNodes rest

/-- Whether the requested event retains the new noise bit.  Two pivot
occurrences cancel both the old source and the same independent noise. -/
def noiseActive (step : HedgeLinearReadoutStep S) : List (Fin S.count) -> Bool
  | [] => false
  | node :: rest => Bool.xor (decide (node = step.pivot)) (step.noiseActive rest)

/-- Exact event substitution on the observable assignment map.  The
statement covers arbitrary old assignments and all observed background
labels, not just assignments attained by one of the carrier models. -/
theorem pullback_assignment (step : HedgeLinearReadoutStep S)
    (rich : ObservedSignature.ValueRich S) (nodes : List (Fin S.count))
    (sample : S.Assignment) (bit : Bool) :
    hedgeParityList rich nodes
        (S.privateReadoutAssignment step.pivot
          (hedgeNoisyReadout rich step.pivot step.injectOld (step.parentSignal rich)) sample bit) =
      Bool.xor (hedgeParityList rich (step.pullbackNodes nodes) sample) (step.noiseActive nodes && bit) := by
  induction nodes with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      rw [hedgeParityList_cons, inductionHypothesis]
      simp only [pullbackNodes, hedgeParityList_append, noiseActive]
      by_cases same : node = step.pivot
      · subst node
        simp only [↓reduceIte, decide_true,
          ObservedSignature.privateReadoutAssignment, ObservedSignature.replace_at,
          hedgeNoisyReadout, hedgeIsSecond_parityCarrierValue]
        change ((hedgeReadoutSignal rich step.pivot step.injectOld (step.parentSignal rich) sample ^^ bit) ^^
          (hedgeParityList rich (step.pullbackNodes rest) sample ^^ step.noiseActive rest && bit)) = _
        rw [← step.sourceNodes_signal rich sample]
        generalize hedgeParityList rich step.sourceNodes sample = source
        generalize hedgeParityList rich (step.pullbackNodes rest) sample = tail
        cases source <;> cases tail <;> cases step.noiseActive rest <;> cases bit <;> rfl
      · rw [if_neg same]
        simp only [hedgeParityList_cons, hedgeParityList_nil, Bool.xor_false,
          ObservedSignature.privateReadoutAssignment, S.replace_ne sample step.pivot node _ same,
          decide_eq_false same, Bool.false_xor]
        generalize hedgeIsSecond rich node (sample node) = head
        generalize hedgeParityList rich (step.pullbackNodes rest) sample = tail
        cases head <;> cases tail <;> cases step.noiseActive rest <;> cases bit <;> rfl

/-! ## The retained or cancelled noise is still an injective finite channel -/

/-- The event's effective fresh noise: cancelled pivot occurrences send
both noise values to zero, while an odd occurrence retains the supplied bit.
This is a pushforward of the genuine independent factor, not a new latent
assumption. -/
def effectiveNoise (step : HedgeLinearReadoutStep S) (nodes : List (Fin S.count)) :
    FiniteProbRecord Bool :=
  step.noise.map (fun bit => step.noiseActive nodes && bit)

def effectiveGap (step : HedgeLinearReadoutStep S) (nodes : List (Fin S.count)) (gap : Nat) : Nat :=
  if step.noiseActive nodes then gap else step.noise.den

theorem effectiveGap_positive (step : HedgeLinearReadoutStep S)
    (nodes : List (Fin S.count)) (gap : Nat) (positive : 0 < gap) :
    0 < step.effectiveGap nodes gap := by
  unfold effectiveGap
  cases step.noiseActive nodes
  · exact step.noise.den_pos
  · exact positive

/-- Cancelling a noise coordinate produces the identity channel, whose
stay excess is its positive denominator.  Retaining it preserves the
original strictly positive bias.  Thus neither substitution case can erase
a pre-existing interventional event gap. -/
theorem effectiveNoise_bias (step : HedgeLinearReadoutStep S)
    (nodes : List (Fin S.count)) (gap : Nat)
    (bias : FiniteProbRecord.eventMass step.noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass step.noise.atoms id + gap) :
    FiniteProbRecord.eventMass (step.effectiveNoise nodes).atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass (step.effectiveNoise nodes).atoms id + step.effectiveGap nodes gap := by
  simp only [effectiveNoise, FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels, effectiveGap]
  cases active : step.noiseActive nodes with
  | false =>
      simp only [Bool.false_and, Bool.not_false, id_eq, Bool.false_eq_true, ↓reduceIte]
      change FiniteProbRecord.eventMass step.noise.atoms (topEvent : Event Bool) =
        FiniteProbRecord.eventMass step.noise.atoms (fun _ => false) + step.noise.den
      rw [FiniteProbRecord.eventMass_top, step.noise.total_mass, FiniteProbRecord.eventMass_false]
      exact (Nat.zero_add _).symm
  | true =>
      simpa only [active, Bool.true_and, ↓reduceIte] using bias

/-- The actual updated SCM's parity event is exactly the pulled-back old
event passed through its effective independent channel.  All latent
coordinates and unequal prior denominators are retained by finite
pushforward identities.  Only the pivot must remain unintervened. -/
theorem interventionalValue_equiv (step : HedgeLinearReadoutStep S)
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (nodes : List (Fin S.count)) (ignored : base.OtherMechanismsIgnore step.pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : intervention step.pivot = none) :
    QProb.Equiv
      (((step.toReadoutStep rich).apply rich base).interventionalValue intervention (hedgeParityList rich nodes))
      ((base.noisyInterventionalSignal intervention
        (hedgeParityList rich (step.pullbackNodes nodes)) (step.effectiveNoise nodes)).probVal id) := by
  let model := (step.toReadoutStep rich).apply rich base
  let signal := fun latent => hedgeParityList rich (step.pullbackNodes nodes) (base.evalUnder intervention latent)
  have evaluation (pair : Bool × base.latent.Assignment) :
      hedgeParityList rich nodes
          (model.evalUnder intervention (PrivateBooleanNoise.assignment base.latent pair.1 pair.2)) =
        Bool.xor (signal pair.2) (step.noiseActive nodes && pair.1) := by
    change hedgeParityList rich nodes ((base.withPrivateReadout step.pivot step.noise
      (hedgeNoisyReadout rich step.pivot step.injectOld (step.parentSignal rich))).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent pair.1 pair.2)) = _
    rw [base.withPrivateReadout_evalUnder step.pivot step.noise _ ignored intervention free pair.2 pair.1]
    exact step.pullback_assignment rich nodes (base.evalUnder intervention pair.2) pair.1
  have pushed := (step.noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => hedgeParityList rich nodes (model.evalUnder intervention latent))
  have substituted := (step.noise.product base.prior).probVal_congr _ _ evaluation
  have effective := step.noise.product_map_left_probVal base.prior
    (fun bit => step.noiseActive nodes && bit) (fun pair => Bool.xor (signal pair.2) pair.1)
  exact QProb.equiv_trans (model.interventionalValue_eq intervention (hedgeParityList rich nodes))
    (QProb.equiv_trans pushed (QProb.equiv_trans substituted
      (QProb.equiv_trans (QProb.equiv_symm effective)
        (base.prior.xorChannel_noise_first_probVal signal (step.effectiveNoise nodes)))))

/-- A one-step equality of the new event is equivalent to equality of its
explicit old-coordinate substitution.  Positivity and observational
equivalence are separate invariants; they are not needed to cancel the
strictly biased channel. -/
theorem interventionalValue_equiv_iff (step : HedgeLinearReadoutStep S)
    (left right : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (nodes : List (Fin S.count))
    (leftIgnored : left.OtherMechanismsIgnore step.pivot)
    (rightIgnored : right.OtherMechanismsIgnore step.pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : intervention step.pivot = none) (gap : Nat) (gapPositive : 0 < gap)
    (bias : FiniteProbRecord.eventMass step.noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass step.noise.atoms id + gap) :
    QProb.Equiv
      (((step.toReadoutStep rich).apply rich left).interventionalValue intervention (hedgeParityList rich nodes))
      (((step.toReadoutStep rich).apply rich right).interventionalValue intervention (hedgeParityList rich nodes)) ↔
    QProb.Equiv (left.interventionalValue intervention (hedgeParityList rich (step.pullbackNodes nodes)))
      (right.interventionalValue intervention (hedgeParityList rich (step.pullbackNodes nodes))) := by
  have leftEq := step.interventionalValue_equiv left rich nodes leftIgnored intervention free
  have rightEq := step.interventionalValue_equiv right rich nodes rightIgnored intervention free
  have channel := FiniteLatentSCM.noisyInterventionalSignal_equiv_iff_of_bias left right intervention
    (hedgeParityList rich (step.pullbackNodes nodes)) (step.effectiveNoise nodes)
    (step.effectiveGap nodes gap) (step.effectiveGap_positive nodes gap gapPositive) (step.effectiveNoise_bias nodes gap bias)
  constructor
  · intro equivalent
    exact channel.mp (QProb.equiv_trans (QProb.equiv_symm leftEq) (QProb.equiv_trans equivalent rightEq))
  · intro equivalent
    exact QProb.equiv_trans leftEq (QProb.equiv_trans (channel.mpr equivalent) (QProb.equiv_symm rightEq))

end HedgeLinearReadoutStep

/-! ## Arbitrary finite substitution, not a fixed catalogue of path lengths -/

namespace HedgeLinearReadoutPlan

/-- The actual executable SCM instructions generated by the linear plan. -/
def readouts (rich : ObservedSignature.ValueRich S) (steps : List (HedgeLinearReadoutStep S)) :
    List (HedgeReadoutStep S) :=
  steps.map (fun step => step.toReadoutStep rich)

/-- Pull the final requested coordinates backward through the whole plan.
Execution is left-to-right, so substitution visits the tail before replacing
the first pivot.  In particular, merging parent lists can cancel a noise
coordinate even when that coordinate occurs in several requested outputs. -/
def pullbackNodes : List (HedgeLinearReadoutStep S) -> List (Fin S.count) -> List (Fin S.count)
  | [], nodes => nodes
  | step :: rest, nodes => step.pullbackNodes (pullbackNodes rest nodes)

/-- Equality of the final outcome parity in the two actual updated SCMs is
equivalent to equality of its fully substituted old-coordinate parity.

The induction has no fixed depth.  Each step may have a different biased
positive-denominator noise record and any number of declared parents.
The proof derives intermediate non-influence from the initial invariant and
topological order, and cancels each effective independent channel.  The
existential bias witness is eliminated only into this proposition; no SCM
or noise data is chosen from a proposition. -/
theorem interventionalValue_equiv_iff
    (left right : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeLinearReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (leftIgnored : forall step, step ∈ steps -> left.OtherMechanismsIgnore step.pivot)
    (rightIgnored : forall step, step ∈ steps -> right.OtherMechanismsIgnore step.pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : forall step, step ∈ steps -> intervention step.pivot = none)
    (biased : forall step, step ∈ steps -> Exists fun gap =>
      0 < gap ∧ FiniteProbRecord.eventMass step.noise.atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass step.noise.atoms id + gap)
    (nodes : List (Fin S.count)) :
    QProb.Equiv
      ((left.withHedgeReadouts rich (readouts rich steps)).interventionalValue intervention (hedgeParityList rich nodes))
      ((right.withHedgeReadouts rich (readouts rich steps)).interventionalValue intervention (hedgeParityList rich nodes)) ↔
    QProb.Equiv (left.interventionalValue intervention (hedgeParityList rich (pullbackNodes steps nodes)))
      (right.interventionalValue intervention (hedgeParityList rich (pullbackNodes steps nodes))) := by
  induction steps generalizing left right nodes with
  | nil => exact Iff.rfl
  | cons step rest inductionHypothesis =>
      rcases biased step List.mem_cons_self with ⟨gap, gapPositive, bias⟩
      change QProb.Equiv
        ((((step.toReadoutStep rich).apply rich left).withHedgeReadouts rich (readouts rich rest)).interventionalValue
          intervention (hedgeParityList rich nodes))
        ((((step.toReadoutStep rich).apply rich right).withHedgeReadouts rich (readouts rich rest)).interventionalValue
          intervention (hedgeParityList rich nodes)) ↔ _
      apply Iff.trans
      · apply inductionHypothesis
        · exact (List.pairwise_cons.mp ordered).2
        · intro next listed
          exact left.withPrivateBooleanNoise_otherMechanismsIgnore_of_earlier step.pivot next.pivot step.noise
            _ (leftIgnored next (List.mem_cons_of_mem _ listed)) ((List.pairwise_cons.mp ordered).1 next listed)
        · intro next listed
          exact right.withPrivateBooleanNoise_otherMechanismsIgnore_of_earlier step.pivot next.pivot step.noise
            _ (rightIgnored next (List.mem_cons_of_mem _ listed)) ((List.pairwise_cons.mp ordered).1 next listed)
        · intro next listed
          exact free next (List.mem_cons_of_mem _ listed)
        · intro next listed
          exact biased next (List.mem_cons_of_mem _ listed)
      · exact step.interventionalValue_equiv_iff left right rich (pullbackNodes rest nodes)
          (leftIgnored step List.mem_cons_self) (rightIgnored step List.mem_cons_self)
          intervention (free step List.mem_cons_self) gap gapPositive bias

end HedgeLinearReadoutPlan

end Causality
end Thesis
