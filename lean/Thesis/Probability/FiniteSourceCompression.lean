import Thesis.Probability.FiniteRationalCompression
import Thesis.Probability.RationalValues

namespace Thesis
namespace Probability
namespace FiniteSourceCompression

open FiniteProbRecord

/-!
# Replace one independent source while preserving requested probabilities

A finite source is paired with an unchanged independent background record.
For each requested Boolean event on the pair, integrate the background first
to obtain a rational response of the source alone.  Compressing these
responses preserves the requested probabilities of the actual product.

The background may represent many other sources jointly; its alphabet need
not be enumerated here.  The response is computed by finite integration, not
by conditioning on a source value or dividing by its old probability.  Thus
zero source weights and zero-probability slices need no extra assumptions.

The constructed source has at most `count + 1` positive atom occurrences,
uses only original labels, and remains independent of the whole background
by the genuine product-record law.  Native DAG adapters must still prove
that their prior/readout is represented by this split; that is not taken as
an implicit premise of a claimed native compression theorem.
-/

def sliceResponse (background : FiniteProbRecord X) (event : Event (Ω × X)) (value : Ω) : SignedRatio :=
  (background.probVal (fun other => event (value, other))).toSignedRatio

theorem signedAtomMass_slice (source : List (Ω × Nat)) (background : List (X × Nat)) (event : Event (Ω × X)) :
    signedAtomMass source (fun value => (eventMass background (fun other => event (value, other)) : Int)) =
      (eventMass (weightedCartesian source background) event : Int) := by
  rw [eventMass_weightedCartesian_bind]
  induction source with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp only [signedAtomMass, List.map_cons, List.sum_cons, Int.natCast_add, Int.natCast_mul] at inductionHypothesis ⊢
      rw [inductionHypothesis]

/-- Finite iterated integration agrees with the ordinary event probability
of the same product record.  No conditional is introduced at any stage. -/
theorem rationalMean_sliceResponse (source : FiniteProbRecord Ω) (background : FiniteProbRecord X)
    (event : Event (Ω × X)) :
    SignedRatio.Equiv (source.rationalMean (sliceResponse background event))
      ((source.product background).probVal event).toSignedRatio := by
  have cleared := rationalMean_cleared source (sliceResponse background event)
    (fun value => (eventMass background.atoms (fun other => event (value, other)) : Int))
    background.den background.den_pos (fun _ => SignedRatio.equiv_refl _)
  refine SignedRatio.equiv_trans cleared ?_
  change source.signedMass (fun value => (eventMass background.atoms (fun other => event (value, other)) : Int)) *
      ((source.den * background.den : Nat) : Int) =
    (eventMass (weightedCartesian source.atoms background.atoms) event : Int) *
      ((source.den * background.den : Nat) : Int)
  rw [signedMass, signedAtomMass_slice]

structure Replacement (source : FiniteProbRecord Ω) (background : FiniteProbRecord X)
    (events : Fin count → Event (Ω × X)) where
  factor : FiniteProbRecord Ω
  bound : factor.atoms.length ≤ count + 1
  positive : forall atom, atom ∈ factor.atoms → 0 < atom.2
  label_mem : forall atom, atom ∈ factor.atoms → Exists fun weight => (atom.1, weight) ∈ source.atoms
  preserved : forall index, QProb.Equiv ((factor.product background).probVal (events index))
    ((source.product background).probVal (events index))
  independent : forall sourceEvent backgroundEvent,
    QProb.Equiv ((factor.product background).probVal (fun pair => sourceEvent pair.1 && backgroundEvent pair.2))
      (QProb.mul (factor.probVal sourceEvent) (background.probVal backgroundEvent))

/-- Construct the replacement factor and its exact product-level guarantees.
The background record is literally unchanged; only the independent source's
natural weights and positive denominator may change. -/
def compress (source : FiniteProbRecord Ω) (background : FiniteProbRecord X)
    (events : Fin count → Event (Ω × X)) : Replacement source background events := by
  let solved := FiniteRationalCompression.compress source (fun index => sliceResponse background (events index))
  refine ⟨solved.record, solved.bound, solved.positive, solved.label_mem, ?_, ?_⟩
  · intro index
    apply (QProb.toSignedRatio_equiv_iff _ _).mp
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (rationalMean_sliceResponse solved.record background (events index)))
      (SignedRatio.equiv_trans (solved.preserved index) (rationalMean_sliceResponse source background (events index)))
  · intro sourceEvent backgroundEvent
    exact solved.record.product_probVal background sourceEvent backgroundEvent

end FiniteSourceCompression
end Probability
end Thesis
