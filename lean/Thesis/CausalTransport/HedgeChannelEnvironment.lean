import Thesis.CausalTransport.HedgeChannelLikelihood
import Thesis.Causality.PairRootChannelsEnvironment
import Thesis.Probability.BooleanChannelReserve

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironment

open Probability

/-!
# Positive channel models with independent latent-input signals

The earlier installation permits small and background signals to read only
observed parents.  That restriction is insufficient at a genuine latent
entry: `Examples.HedgeChannelLatentBoundary` proves that all such installed
signals can leave a non-identifiable conditional query unchanged.

Here a centre can also read the independent terminal bit at each incident
pair root.  The main character coordinates remain independent of these
environment coordinates under the actual product prior.  No global mixing
source is added, and a row is never given nonincident root inputs.

`BooleanChannelTable.reserveChannel` embeds the old row terms unchanged in
the enlarged alphabet.  Thus the existing CPT implementation, positive-row
proof and exact likelihood bridge apply directly; there is no second table
SCM implementation to maintain.  Freezing an environment is only a step in
the integration proof, not a replacement SCM with a selected hidden state.

The complete natural likelihood numerator separates into actual main-prior
integrals at every environment.  Pointwise factual matching of those inner
integrals therefore proves equality of the entire observed law of the two
actual enlarged models.  Finding signals with a conditional gap remains a
separate obligation; this general semantic bridge does not assert universal
conditional completeness or discard any normalization change.
-/

variable {S : ObservedSignature.{0}}

/-- A vector of main-channel centres with access to the actual enlarged
incident inputs.  The reserved environment is not itself a row summand. -/
abbrev Signals (G : ObservedGraph S) (channels : Nat) :=
  (child : Fin S.count) -> S.binary.ParentValues child ->
    (PairRootChannels.extension G.binary (channels + 1)).Inputs child -> PairRootChannels.BitVector channels

/-- Retain the old local terms once; the terminal coordinate is unlisted. -/
def paddedTables (tables : Fin S.count -> BooleanChannelTable (Fin channels)) :
    Fin S.count -> BooleanChannelTable (Fin (channels + 1)) := fun child => (tables child).reserveChannel

/-- The terminal centre has no row amplitude.  Choosing its fixed displayed
value does not fix or remove the actual terminal latent bit read by signals. -/
def paddedSignals (G : ObservedGraph S) (channels : Nat) (signals : Signals G channels) :
    HedgeChannelTable.Signals G (channels + 1) :=
  fun child parents inputs => FiniteProduct.extend false (signals child parents inputs)

/-- The actual finite latent SCM is the established positive CPT builder on
the enlarged pair-root alphabet, with its genuine private response sources. -/
def model (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels) : ExactModel S.binary :=
  HedgeChannelTable.model G (channels + 1) (paddedTables tables) (paddedSignals G channels signals)

/-- Every original graph edge and the canonical latent incidence are kept.
In particular the environment block does not introduce a common parent of
three observed vertices or erase an unused original bidirected pair. -/
theorem model_compatible (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels) :
    Compatible (model G channels tables signals) G.binary :=
  HedgeChannelTable.model_compatible G (channels + 1) _ _

/-- All complete Boolean observed assignments still have positive mass,
independently of the supplied local latent-input signals. -/
theorem model_positive (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels) :
    ObservationallyPositive (model G channels tables signals) :=
  HedgeChannelTable.model_positive G (channels + 1) _ _

/-- At a fixed displayed environment, join its incident constants to the
ordinary main inputs.  Only those constants with the child's actual incidence
proof are passed to its original local centre function. -/
def frozenSignals (G : ObservedGraph S) (channels : Nat) (signals : Signals G channels)
    (environment : PairRootChannels.Environment.Assignment G.binary) : HedgeChannelTable.Signals G channels :=
  fun child parents inputs => signals child parents
    (fun root incident => FiniteProduct.extend (environment root) (inputs root incident))

/-- Each real joined shared slice has literally the same private numerator
as its frozen main slice.  This retains every hard-intervention indicator,
including conflicts of numerator zero, and every original observed row. -/
theorem rowNumerator_join (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (environment : PairRootChannels.Environment.Assignment G.binary)
    (shared : (PairRootChannels.extension G.binary channels).Assignment) :
    HedgeChannelTable.rowNumerator G (channels + 1) (paddedTables tables) (paddedSignals G channels signals)
      target sample (PairRootChannels.Environment.join G.binary channels environment shared) =
      HedgeChannelTable.rowNumerator G channels tables (frozenSignals G channels signals environment) target sample shared := by
  unfold HedgeChannelTable.rowNumerator
  rw [FiniteProduct.qProduct_num, FiniteProduct.qProduct_num]
  apply FiniteProduct.natProduct_congr
  intro child
  apply congrArg QProb.num
  simpa only [paddedTables, paddedSignals, FiniteProduct.extend_castSucc] using
    (tables child).reserveChannel_cellUnder
      (FiniteProduct.extend (Value := fun _ => Bool) false
        (signals child (fun parent _edge => sample parent)
          (fun root _incident => PairRootChannels.Environment.join G.binary channels environment shared root)))
      (target child) (sample child)

/-- The full actual likelihood numerator is the sum of the complete main
numerators at every independent environment.  This is derived from the
actual shared support permutation, not assumed as a mixture identity. -/
theorem integratedNumerator_split (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    HedgeChannelTable.integratedNumerator G (channels + 1) (paddedTables tables) (paddedSignals G channels signals)
      target sample =
      ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
        HedgeChannelTable.integratedNumerator G channels tables (frozenSignals G channels signals environment)
          target sample)).sum := by
  unfold HedgeChannelTable.integratedNumerator
  rw [PairRootChannels.Environment.enumeration_sum_split]
  simp only [rowNumerator_join]

/-- Reserve no new row mass.  Only the complete independent environment
support multiplies the common actual likelihood denominator.  The identity
is valid for every intervention, without a positive-cell premise. -/
theorem likelihoodDenominator_split (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (target : Fin S.count -> Option Bool) :
    HedgeChannelTable.likelihoodDenominator G (channels + 1) (paddedTables tables) target =
      (PairRootChannels.Environment.enumeration G.binary).length *
        HedgeChannelTable.likelihoodDenominator G channels tables target := by
  have rows : HedgeChannelTable.rowDenominator (paddedTables tables) target =
      HedgeChannelTable.rowDenominator tables target := by
    apply FiniteProduct.natProduct_congr
    intro child
    cases target child with
    | none => exact congrArg (2 * ·) ((tables child).reserveChannel_capacity)
    | some _ => rfl
  unfold HedgeChannelTable.likelihoodDenominator
  rw [rows, PairRootChannels.Environment.prior_den_split]
  ac_rfl

private theorem natural_sum_add (values : List α) (left right : α -> Nat) :
    (values.map (fun value => left value + right value)).sum = (values.map left).sum + (values.map right).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis]
      ac_rfl

private theorem natural_sum_swap (left : List α) (right : List β) (term : α -> β -> Nat) :
    (left.map (fun first => (right.map (term first)).sum)).sum =
      (right.map (fun second => (left.map (fun first => term first second)).sum)).sum := by
  induction left with
  | nil =>
      change 0 = (right.map (fun _ => (0 : Nat))).sum
      induction right with
      | nil => rfl
      | cons value rest inductionHypothesis =>
          rw [List.map_cons, List.sum_cons, ← inductionHypothesis]
  | cons first rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [natural_sum_add, inductionHypothesis]

/-- Event projection retains both complete sums: all event-compatible
observed assignments and all environments.  Swapping these finite sums
gives the actual frozen-event numerators, not a selected singleton gap. -/
theorem eventNumerator_split (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) :
    HedgeChannelTable.eventNumerator G (channels + 1) (paddedTables tables) (paddedSignals G channels signals)
      target event =
      ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
        HedgeChannelTable.eventNumerator G channels tables (frozenSignals G channels signals environment)
          target event)).sum := by
  unfold HedgeChannelTable.eventNumerator
  have expanded :
      (S.binary.assignmentEnumeration.filter event).map
        (HedgeChannelTable.integratedNumerator G (channels + 1) (paddedTables tables) (paddedSignals G channels signals) target) =
      (S.binary.assignmentEnumeration.filter event).map (fun sample =>
        ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
          HedgeChannelTable.integratedNumerator G channels tables (frozenSignals G channels signals environment)
            target sample)).sum) :=
    List.map_congr_left (fun sample _selected => integratedNumerator_split G channels tables signals target sample)
  rw [expanded]
  exact natural_sum_swap (S.binary.assignmentEnumeration.filter event)
    (PairRootChannels.Environment.enumeration G.binary)
    (fun sample environment => HedgeChannelTable.integratedNumerator G channels tables
      (frozenSignals G channels signals environment) target sample)

/-- The genuine interventional probability of every observed event is the
complete environment sum on the proven product denominator.  It integrates
the same actual shared and private sources as `model`, and does not enumerate
the potentially much larger private response-function support. -/
theorem model_interventional_event (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) :
    QProb.Equiv ((model G channels tables signals).interventionalValue target event)
      ⟨((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
          HedgeChannelTable.eventNumerator G channels tables (frozenSignals G channels signals environment)
            target event)).sum,
        (PairRootChannels.Environment.enumeration G.binary).length *
          HedgeChannelTable.likelihoodDenominator G channels tables target,
        Nat.mul_pos (PairRootChannels.Environment.enumeration_length_positive G.binary)
          (HedgeChannelTable.likelihoodDenominator_positive G channels tables target)⟩ := by
  simpa only [eventNumerator_split, likelihoodDenominator_split] using
    HedgeChannelTable.model_interventional_event G (channels + 1) (paddedTables tables)
      (paddedSignals G channels signals) target event

/-- Equal capacities and complete main-numerator matching at each factual
sample and every environment suffice for equality of all actual observed
events.  Finiteness supplies whole-law extensionality; no source is selected
or identified merely from equality of a few coordinate marginals. -/
theorem models_observationallyEquivalent_of_frozenNumerators (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels)) (leftSignals rightSignals : Signals G channels)
    (capacities : forall child, (left child).capacity = (right child).capacity)
    (numerators : forall environment : PairRootChannels.Environment.Assignment G.binary,
      forall sample : S.binary.Assignment,
        HedgeChannelTable.integratedNumerator G channels left (frozenSignals G channels leftSignals environment)
          (fun _ => none) sample =
        HedgeChannelTable.integratedNumerator G channels right (frozenSignals G channels rightSignals environment)
          (fun _ => none) sample) :
    ObservationallyEquivalent (model G channels left leftSignals) (model G channels right rightSignals) := by
  apply HedgeChannelTable.model_observationallyEquivalent_of_expansion G (channels + 1)
    (paddedTables left) (paddedTables right) (paddedSignals G channels leftSignals) (paddedSignals G channels rightSignals)
  · intro child
    exact ((left child).reserveChannel_capacity).trans ((capacities child).trans (right child).reserveChannel_capacity.symm)
  · intro sample
    rw [← HedgeChannelTable.integratedNumerator_expansion, ← HedgeChannelTable.integratedNumerator_expansion]
    apply congrArg (fun value : Nat => (value : Int))
    rw [integratedNumerator_split, integratedNumerator_split]
    exact congrArg List.sum (List.map_congr_left (fun environment _listed => numerators environment sample))

end HedgeChannelEnvironment
end Causality
end Thesis
