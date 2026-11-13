import Thesis.CausalTransport.HedgeChannelTable
import Thesis.Probability.FiniteProductBlocks

namespace Thesis
namespace Causality
namespace HedgeChannelTable

open Probability

/-!
# Whole-model likelihoods on the actual pair-root channel prior

Local character identities are not yet equalities of SCM probabilities.
This module supplies that semantic bridge: the genuine CPT likelihood is
split into its original shared prefix and integrated private-row suffix.
Every shared singleton has numerator one, whereas its actual denominator
is retained.  Every free row retains twice its capacity, and every forced
row retains denominator one, including conflicting cells of numerator zero.

Consequently all shared assignments have a common, strictly positive
likelihood denominator.  Their natural row numerators can be summed first,
without constructing or reducing the much larger response-function prior.
The same numerator is then identified with the complete character expansion
integrated against the actual independent pair-root record.

These statements hold for all typed local signals, all finite channel lists
(including repeated labels), and every hard intervention.  They do not yet
choose the graph-specific coefficients that make two observational laws
equal, nor do they assert a causal gap.  They make those remaining algebraic
obligations sufficient for equality of the actual model probabilities.
-/

variable {S : ObservedSignature.{0}}

/-- Natural numerator of the integrated private-row product at a fixed
actual shared assignment.  Intervened rows use their exact indicators. -/
def rowNumerator (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (shared : (PairRootChannels.extension G.binary channels).Assignment) : Nat :=
  (FiniteProduct.qProduct S.count (fun child => (tables child).cellUnder
    (signals child (fun parent _edge => sample parent) (fun root _incident => shared root))
    (target child) (sample child))).num

/-- The private-row denominator depends on capacities and the intervention,
not on the observed sample or any hidden signal. -/
def rowDenominator (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) : Nat :=
  FiniteProduct.natProduct S.count (fun child => match target child with
    | none => 2 * (tables child).capacity
    | some _ => 1)

/-- The denominator product remains positive even when some forced
row numerators are zero.  No support premise is required for this fact. -/
theorem rowDenominator_positive (tables : Fin S.count -> BooleanChannelTable (Fin channels))
    (target : Fin S.count -> Option Bool) : 0 < rowDenominator tables target := by
  apply FiniteProduct.natProduct_positive
  intro child
  cases target child with
  | none => exact Nat.mul_pos (by decide) (tables child).capacity_positive
  | some _ => exact Nat.zero_lt_one

/-- Common denominator of each actual likelihood summand: the private
suffix followed by the full independent shared-prior denominator. -/
def likelihoodDenominator (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (target : Fin S.count -> Option Bool) : Nat :=
  rowDenominator tables target * (PairRootChannels.prior G.binary channels).den

/-- Both the actual shared prior and the integrated private suffix have
positive normalization masses, including their empty-product boundaries. -/
theorem likelihoodDenominator_positive (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (target : Fin S.count -> Option Bool) :
    0 < likelihoodDenominator G channels tables target :=
  Nat.mul_pos (rowDenominator_positive tables target) (PairRootChannels.prior G.binary channels).den_pos

/-- Sum the actual private-row numerators over every root-major shared
assignment exactly once.  No private response function is enumerated. -/
def integratedNumerator (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) : Nat :=
  ((PairRootChannels.enumeration G.binary channels).map (rowNumerator G channels tables signals target sample)).sum

/-- The shared prefix contributes only unit numerators; the remaining
literal numerator is precisely the actual private-row product. -/
theorem sliceProduct_num (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (shared : (PairRootChannels.extension G.binary channels).Assignment) :
    (FiniteProduct.qProduct (cpt G channels tables signals).extension.count
      ((cpt G channels tables signals).sliceFactors target shared sample)).num =
        rowNumerator G channels tables signals target sample shared := by
  rw [FiniteProduct.qProduct_num]
  change FiniteProduct.natProduct (pairRootCount G.binary + S.count) _ = _
  rw [FiniteProduct.natProduct_append]
  have suffix := FiniteProduct.natProduct_congr S.count
    (fun child => ((cpt G channels tables signals).sliceFactors target shared sample
      (Fin.natAdd (pairRootCount G.binary) child)).num)
    (fun child => ((tables child).cellUnder
      (signals child (fun parent _edge => sample parent) (fun root _incident => shared root))
      (target child) (sample child)).num)
    (fun child => congrArg QProb.num (privateFactor_eq_cellUnder G channels tables signals target shared sample child))
  have sharedProduct := FiniteProduct.natProduct_congr (pairRootCount G.binary)
    (fun root => ((cpt G channels tables signals).sliceFactors target shared sample (root.castAdd S.count)).num)
    (fun _ => 1) (fun root => by
      change ((cpt G channels tables signals).sliceFactors target shared sample
        ((cpt G channels tables signals).sharedRoot root)).num = 1
      rw [FiniteLatentRationalCPT.sliceFactors_sharedRoot]
      exact PairRootChannels.factor_singleton_num channels (shared root))
  refine (congrArg (fun factor => factor * _) suffix).trans
    ((congrArg (fun factor => _ * factor) sharedProduct).trans ?_)
  rw [FiniteProduct.natProduct_one, Nat.mul_one]
  exact (FiniteProduct.qProduct_num S.count _).symm

/-- The whole slice denominator is independent of all hidden centres and
of the sample.  Forced zero cells remain in the proof without cancellation. -/
theorem sliceProduct_den (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (shared : (PairRootChannels.extension G.binary channels).Assignment) :
    (FiniteProduct.qProduct (cpt G channels tables signals).extension.count
      ((cpt G channels tables signals).sliceFactors target shared sample)).den =
        likelihoodDenominator G channels tables target := by
  rw [FiniteProduct.qProduct_den]
  change FiniteProduct.natProduct (pairRootCount G.binary + S.count) _ = _
  rw [FiniteProduct.natProduct_append]
  have suffix := FiniteProduct.natProduct_congr S.count
    (fun child => ((cpt G channels tables signals).sliceFactors target shared sample
      (Fin.natAdd (pairRootCount G.binary) child)).den)
    (fun child => match target child with | none => 2 * (tables child).capacity | some _ => 1)
    (fun child => (congrArg QProb.den
      (privateFactor_eq_cellUnder G channels tables signals target shared sample child)).trans
        ((tables child).cellUnder_den _ _ _))
  have sharedProduct := FiniteProduct.natProduct_congr (pairRootCount G.binary)
    (fun root => ((cpt G channels tables signals).sliceFactors target shared sample (root.castAdd S.count)).den)
    (fun _ => (PairRootChannels.factor channels).den) (fun root => by
      change ((cpt G channels tables signals).sliceFactors target shared sample
        ((cpt G channels tables signals).sharedRoot root)).den = (PairRootChannels.factor channels).den
      rw [FiniteLatentRationalCPT.sliceFactors_sharedRoot]
      rfl)
  refine (congrArg (fun factor => factor * _) suffix).trans
    ((congrArg (fun factor => _ * factor) sharedProduct).trans ?_)
  exact congrArg (rowDenominator tables target * ·)
    (FiniteProduct.record_den_eq_natProduct (pairRootCount G.binary)
      (fun _ => PairRootChannels.BitVector channels) (fun _ => PairRootChannels.factor channels)).symm

/-- One actual likelihood summand has the stated common-denominator
presentation.  Only positive denominators, never row numerators, are used. -/
theorem sliceProduct_equiv (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (shared : (PairRootChannels.extension G.binary channels).Assignment) :
    QProb.Equiv (FiniteProduct.qProduct (cpt G channels tables signals).extension.count
      ((cpt G channels tables signals).sliceFactors target shared sample))
      ⟨rowNumerator G channels tables signals target sample shared,
        likelihoodDenominator G channels tables target, likelihoodDenominator_positive G channels tables target⟩ := by
  unfold QProb.Equiv
  rw [sliceProduct_num, sliceProduct_den]

/-- Sum all genuine shared likelihood slices on their common denominator.
This avoids the unrelated denominators introduced by a raw rational sum. -/
theorem likelihoodWith_equiv (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    QProb.Equiv ((cpt G channels tables signals).likelihoodWith
      (PairRootChannels.enumeration G.binary channels) target sample)
      ⟨integratedNumerator G channels tables signals target sample,
        likelihoodDenominator G channels tables target, likelihoodDenominator_positive G channels tables target⟩ := by
  refine QProb.equiv_trans (QProb.listSum_map_congr (PairRootChannels.enumeration G.binary channels) _ _
    (sliceProduct_equiv G channels tables signals target sample)) ?_
  simpa only [List.map_map, Function.comp_def] using
    QProb.listSum_mk_same_den (likelihoodDenominator G channels tables target)
      (likelihoodDenominator_positive G channels tables target)
      ((PairRootChannels.enumeration G.binary channels).map (rowNumerator G channels tables signals target sample))

/-- Actual interventional singleton probability, with every shared source
and private response source integrated under its real independent record. -/
theorem model_interventional_singleton (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    QProb.Equiv ((model G channels tables signals).interventionalValue target (FiniteProbRecord.singletonEvent sample))
      ⟨integratedNumerator G channels tables signals target sample,
        likelihoodDenominator G channels tables target, likelihoodDenominator_positive G channels tables target⟩ :=
  QProb.equiv_trans ((cpt G channels tables signals).toSCM_interventional_singleton_likelihoodWith
    (PairRootChannels.enumeration G.binary channels) (PairRootChannels.enumeration_nodup G.binary channels)
    (PairRootChannels.enumeration_complete G.binary channels) target sample)
    (likelihoodWith_equiv G channels tables signals target sample)

/-- The factual counterpart is the no-intervention specialization, not a
separate assumption that a table-shaped object has the right observed law. -/
theorem model_observational_singleton (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (sample : S.binary.Assignment) :
    QProb.Equiv ((model G channels tables signals).observationalValue (FiniteProbRecord.singletonEvent sample))
      ⟨integratedNumerator G channels tables signals (FiniteLatentSCM.noIntervention S.binary) sample,
        likelihoodDenominator G channels tables (FiniteLatentSCM.noIntervention S.binary),
        likelihoodDenominator_positive G channels tables (FiniteLatentSCM.noIntervention S.binary)⟩ :=
  model_interventional_singleton G channels tables signals (FiniteLatentSCM.noIntervention S.binary) sample

private theorem nat_sum_cast (values : List Nat) :
    (values.sum : Int) = (values.map fun value : Nat => (value : Int)).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.sum_cons, List.map_cons, Int.natCast_add, inductionHypothesis]

/-- The natural integrated numerator is the signed-mass presentation of
that same nonnegative integrand on the actual unit-weight root-major prior.
Integers are used only for later cancellation, never as probability weights. -/
theorem integratedNumerator_signedMass (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    (integratedNumerator G channels tables signals target sample : Int) =
      (PairRootChannels.prior G.binary channels).signedMass
        (fun shared => (rowNumerator G channels tables signals target sample shared : Int)) := by
  unfold FiniteProbRecord.signedMass
  rw [PairRootChannels.prior_atoms]
  simp only [FiniteProbRecord.signedAtomMass, List.map_map, Function.comp_def, Int.natCast_one, Int.one_mul]
  exact (nat_sum_cast _).trans (congrArg List.sum (List.map_map ..))

/-- The complete choice expansion integrated against the actual shared
prior.  This includes simultaneous selections of different channels at
different rows, as well as every repeated summand in the local lists. -/
def expandedIntegral (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) : Int :=
  (PairRootChannels.prior G.binary channels).signedMass (fun shared =>
    ((FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
      (fun child => (tables child).expansionChoicesUnder (target child))).map fun assignment =>
        FiniteProduct.iProduct S.count (fun child => (tables child).expansionTermUnder
          (signals child (fun parent _edge => sample parent) (fun root _incident => shared root))
          (target child) (sample child) (assignment child))).sum)

/-- The full character integral equals the numerator of the actual model
likelihood.  No graph-specific term has been dropped and no observational
agreement is assumed in establishing this semantic identity. -/
theorem integratedNumerator_expansion (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    (integratedNumerator G channels tables signals target sample : Int) =
      expandedIntegral G channels tables signals target sample := by
  refine (integratedNumerator_signedMass G channels tables signals target sample).trans ?_
  unfold expandedIntegral FiniteProbRecord.signedMass
  apply FiniteProbRecord.signedAtomMass_congr
  intro shared
  exact BooleanChannelTable.product_num_expansion S.count (fun _ => Fin channels) tables
    (fun child => signals child (fun parent _edge => sample parent) (fun root _incident => shared root)) target sample

/-- Integrate each full row-choice monomial separately under the real
pair-root prior.  This form permits the independent-channel cancellation
theorems to be applied to each term before coefficient matching. -/
theorem expandedIntegral_eq_sum (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    expandedIntegral G channels tables signals target sample =
      ((FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
        (fun child => (tables child).expansionChoicesUnder (target child))).map fun assignment =>
          (PairRootChannels.prior G.binary channels).signedMass (fun shared =>
            FiniteProduct.iProduct S.count (fun child => (tables child).expansionTermUnder
              (signals child (fun parent _edge => sample parent) (fun root _incident => shared root))
              (target child) (sample child) (assignment child)))).sum :=
  FiniteProbRecord.signedMass_listSum (PairRootChannels.prior G.binary channels) _ _

/-- Equal row capacities give literally equal likelihood denominators.
No equality of amplitudes, channel labels or local centres is required. -/
theorem likelihoodDenominator_congr (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels))
    (capacities : forall child, (left child).capacity = (right child).capacity)
    (target : Fin S.count -> Option Bool) :
    likelihoodDenominator G channels left target = likelihoodDenominator G channels right target := by
  apply congrArg (· * (PairRootChannels.prior G.binary channels).den)
  apply FiniteProduct.natProduct_congr
  intro child
  cases target child with
  | none => exact congrArg (2 * ·) (capacities child)
  | some _ => rfl

/-- Coefficient matching in the complete signed expansion is sufficient
for equality of actual interventional singleton probabilities.  The only
normalization premise is equality of capacities at each original row. -/
theorem model_interventional_singleton_equiv_of_expansion (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels))
    (leftSignals rightSignals : Signals G channels)
    (capacities : forall child, (left child).capacity = (right child).capacity)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (integrals : expandedIntegral G channels left leftSignals target sample =
      expandedIntegral G channels right rightSignals target sample) :
    QProb.Equiv ((model G channels left leftSignals).interventionalValue target (FiniteProbRecord.singletonEvent sample))
      ((model G channels right rightSignals).interventionalValue target (FiniteProbRecord.singletonEvent sample)) := by
  have numerators := Int.ofNat_inj.mp ((integratedNumerator_expansion G channels left leftSignals target sample).trans
    (integrals.trans (integratedNumerator_expansion G channels right rightSignals target sample).symm))
  refine QProb.equiv_trans (model_interventional_singleton G channels left leftSignals target sample)
    (QProb.equiv_trans ?_ (QProb.equiv_symm (model_interventional_singleton G channels right rightSignals target sample)))
  change integratedNumerator G channels left leftSignals target sample * likelihoodDenominator G channels right target =
    integratedNumerator G channels right rightSignals target sample * likelihoodDenominator G channels left target
  rw [numerators, likelihoodDenominator_congr G channels left right capacities target]

/-- Matching the complete expansion at every factual sample yields the
entire observed law, not merely coordinate marginals or a chosen query.
Finite singleton extensionality then covers every Boolean observed event. -/
theorem model_observationallyEquivalent_of_expansion (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels))
    (leftSignals rightSignals : Signals G channels)
    (capacities : forall child, (left child).capacity = (right child).capacity)
    (integrals : forall sample : S.binary.Assignment,
      expandedIntegral G channels left leftSignals (FiniteLatentSCM.noIntervention S.binary) sample =
        expandedIntegral G channels right rightSignals (FiniteLatentSCM.noIntervention S.binary) sample) :
    ObservationallyEquivalent (model G channels left leftSignals) (model G channels right rightSignals) := by
  intro event
  exact FiniteProbRecord.probVal_extensional_of_singletons
    (model G channels left leftSignals).observationalDist (model G channels right rightSignals).observationalDist
    S.binary.assignmentEnumeration S.binary.assignmentEnumeration_nodup S.binary.assignmentEnumeration_complete
    (fun sample => model_interventional_singleton_equiv_of_expansion G channels left right leftSignals rightSignals
      capacities (FiniteLatentSCM.noIntervention S.binary) sample (integrals sample)) event

/-- Natural likelihood numerator of an arbitrary observed event.  The
original full assignments are summed only when the event selects them;
outcome cylinders and parity readouts need not be singleton events. -/
def eventNumerator (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) : Nat :=
  ((S.binary.assignmentEnumeration.filter event).map (integratedNumerator G channels tables signals target)).sum

/-- The same common denominator presents every actual interventional
event probability.  This is the semantic form needed for an original-query
gap: a difference at a full assignment alone need not survive projection. -/
theorem model_interventional_event (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) :
    QProb.Equiv ((model G channels tables signals).interventionalValue target event)
      ⟨eventNumerator G channels tables signals target event,
        likelihoodDenominator G channels tables target, likelihoodDenominator_positive G channels tables target⟩ := by
  refine QProb.equiv_trans ((cpt G channels tables signals).toSCM_interventionalValue_likelihoodWith
    (PairRootChannels.enumeration G.binary channels) (PairRootChannels.enumeration_nodup G.binary channels)
    (PairRootChannels.enumeration_complete G.binary channels) S.binary.assignmentEnumeration
    S.binary.assignmentEnumeration_nodup S.binary.assignmentEnumeration_complete target event) ?_
  refine QProb.equiv_trans (QProb.listSum_map_congr (S.binary.assignmentEnumeration.filter event) _ _
    (likelihoodWith_equiv G channels tables signals target)) ?_
  simpa only [List.map_map, Function.comp_def] using
    QProb.listSum_mk_same_den (likelihoodDenominator G channels tables target)
      (likelihoodDenominator_positive G channels tables target)
      ((S.binary.assignmentEnumeration.filter event).map (integratedNumerator G channels tables signals target))

/-- With matching capacities, actual event equality is equivalent to
equality of the integrated natural numerators.  Only the positive common
denominator is cancelled, so the equivalence also covers zero probabilities. -/
theorem model_interventional_event_equiv_iff (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels))
    (leftSignals rightSignals : Signals G channels)
    (capacities : forall child, (left child).capacity = (right child).capacity)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) :
    QProb.Equiv ((model G channels left leftSignals).interventionalValue target event)
      ((model G channels right rightSignals).interventionalValue target event) ↔
    eventNumerator G channels left leftSignals target event = eventNumerator G channels right rightSignals target event := by
  have leftPresentation := model_interventional_event G channels left leftSignals target event
  have rightPresentation := model_interventional_event G channels right rightSignals target event
  constructor
  · intro equivalent
    have presented := QProb.equiv_trans (QProb.equiv_symm leftPresentation)
      (QProb.equiv_trans equivalent rightPresentation)
    change eventNumerator G channels left leftSignals target event * likelihoodDenominator G channels right target =
      eventNumerator G channels right rightSignals target event * likelihoodDenominator G channels left target at presented
    rw [likelihoodDenominator_congr G channels left right capacities target] at presented
    exact Nat.eq_of_mul_eq_mul_right (likelihoodDenominator_positive G channels right target) presented
  · intro numerators
    refine QProb.equiv_trans leftPresentation (QProb.equiv_trans ?_ (QProb.equiv_symm rightPresentation))
    change eventNumerator G channels left leftSignals target event * likelihoodDenominator G channels right target =
      eventNumerator G channels right rightSignals target event * likelihoodDenominator G channels left target
    rw [numerators, likelihoodDenominator_congr G channels left right capacities target]

/-- A genuine projected event-numerator gap separates the actual model
probabilities.  No excluded-middle step turns a failed equality into data;
the constructive gap is supplied explicitly by the countermodel argument. -/
theorem model_interventional_event_not_equiv (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels))
    (leftSignals rightSignals : Signals G channels)
    (capacities : forall child, (left child).capacity = (right child).capacity)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment)
    (gap : eventNumerator G channels left leftSignals target event ≠ eventNumerator G channels right rightSignals target event) :
    ¬ QProb.Equiv ((model G channels left leftSignals).interventionalValue target event)
      ((model G channels right rightSignals).interventionalValue target event) :=
  fun equivalent => gap ((model_interventional_event_equiv_iff G channels left right leftSignals rightSignals
    capacities target event).mp equivalent)

end HedgeChannelTable
end Causality
end Thesis
