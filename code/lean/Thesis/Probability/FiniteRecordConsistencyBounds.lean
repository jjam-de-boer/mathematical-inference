import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Finite probability bounds from agreement on a factual event

If two Boolean outcomes agree on an evidence event, the second outcome
contains the evidence-and-first-outcome event.  Outside the evidence it can
contribute at most the entire remaining mass.  This elementary sandwich is
the probability foundation for intervention consistency bounds.

Natural-weight induction already proves event-mass monotonicity.  Here it
is lifted to exact rational probabilities and combined with disjoint union.
Repeated atom labels, zero weights, and null evidence are all permitted.
There are no conditionals, positivity premises, optimizers, or completion of
division at zero.  Attainment of the bounds is a separate model-construction
question: this module does not assert sharpness in a constrained model class.
-/

/-- Boolean event inclusion preserves probability order.  The same finite
record supplies both denominators, so no denominator cancellation or chosen
normal form is necessary. -/
theorem probVal_mono (record : FiniteProbRecord Ω) (left right : Event Ω)
    (included : forall value, left value = true → right value = true) :
    QProb.LE (record.probVal left) (record.probVal right) :=
  QProb.le_of_same_den rfl (eventMass_mono record.atoms left right included)

/-- Agreement on evidence gives both the factual lower bound and the
factual-plus-outside upper bound.  Zero-weight exceptions need no special
handling because inclusion is proved before finite weights are summed. -/
theorem probVal_consistency_bounds (record : FiniteProbRecord Ω)
    (evidence factual alternative : Event Ω)
    (agree : forall value, evidence value = true → alternative value = factual value) :
    QProb.LE (record.probVal (fun value => evidence value && factual value))
        (record.probVal alternative) ∧
      QProb.LE (record.probVal alternative)
        (QProb.add (record.probVal (fun value => evidence value && factual value))
          (record.probVal (fun value => !evidence value))) := by
  let lower : Event Ω := fun value => evidence value && factual value
  let outside : Event Ω := fun value => !evidence value
  have lowerIncluded : forall value, lower value = true → alternative value = true := by
    intro value selected
    have parts := Bool.and_eq_true_iff.mp selected
    rw [agree value parts.1]
    exact parts.2
  have upperIncluded : forall value, alternative value = true → union lower outside value = true := by
    intro value selected
    cases observed : evidence value with
    | false => simp only [union, outside, observed, Bool.not_false, Bool.or_true]
    | true =>
        have factualTrue : factual value = true := (agree value observed).symm.trans selected
        simp only [union, lower, outside, observed, factualTrue,
          Bool.and_self, Bool.not_true, Bool.or_false]
  have disjointParts : disjoint lower outside := by
    intro value selected excluded
    have evidenceTrue := (Bool.and_eq_true_iff.mp selected).1
    simp only [outside, evidenceTrue, Bool.not_true, Bool.false_eq_true] at excluded
  exact ⟨record.probVal_mono lower alternative lowerIncluded,
    QProb.le_congr (QProb.equiv_refl _)
      (record.probVal_union_disjoint lower outside disjointParts)
      (record.probVal_mono alternative (union lower outside) upperIncluded)⟩

end FiniteProbRecord
end Probability
end Thesis
