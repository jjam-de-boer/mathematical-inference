import Thesis.Probability.FiniteProductReplacement
import Thesis.Probability.FiniteProductSupportLaw

namespace Thesis.Probability.FiniteProduct

/-!
# Source-wise evidence preserves an independent finite law

Conditioning arbitrary evidence can correlate independent sources. A precise
exception is rectangular evidence: each source is tested separately, with a
supported event on each factor. The posterior is then the product of those
individually conditioned factors. This module proves the statement for any
joint record carrying the rectangular product law, rather than requiring its
atom list to be literally the canonical Cartesian construction.

The first theorem is the rational algebra used by Bayes normalization. The
second identifies conjunction of rectangles with a rectangle of conjunctions.
Together they prove the posterior rectangular law, retaining zero posterior
cells and an empty source family. Finite extensionality then gives equality
of every mixed posterior event with the constructed product, so the result
is sufficient for causal mechanisms that inspect several sources together.
-/

universe u

/-- Supported coordinate denominators normalize a product coordinate by
coordinate. Positivity of the joint denominator is derived from the factors,
not assumed independently or inferred from the intended identity. -/
theorem qProduct_div (n : Nat) (numerator denominator : Fin n → QProb)
    (positive : ∀ index, 0 < (denominator index).num) :
    QProb.Equiv
      (qProduct n (fun index => QProb.div (numerator index) (denominator index) (positive index)))
      (QProb.div (qProduct n numerator) (qProduct n denominator)
        ((qProduct_num_pos_iff n denominator).mpr positive)) := by
  induction n with
  | zero => simp [qProduct, QProb.Equiv, QProb.div, QProb.one]
  | succ n ih =>
      refine QProb.equiv_trans
        (QProb.mul_congr (QProb.equiv_refl _)
          (ih (fun index => numerator index.castSucc)
            (fun index => denominator index.castSucc)
            (fun index => positive index.castSucc))) ?_
      simp only [qProduct, QProb.Equiv, QProb.div, QProb.mul]
      ac_rfl

/-- Intersecting two rectangles constrains every coordinate by both tests.
This pointwise identity remains valid for dependent value types. -/
theorem rectangularEvent_inter (n : Nat) (Value : Fin n → Type u)
    (left right : (index : Fin n) → Event (Value index)) :
    (fun assignment => rectangularEvent n Value left assignment &&
      rectangularEvent n Value right assignment) =
      rectangularEvent n Value (fun index value => left index value && right index value) := by
  funext assignment
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, rectangularEvent_eq_true_iff]
  constructor
  · rintro ⟨first, second⟩ index
    exact ⟨first index, second index⟩
  · intro both
    exact ⟨fun index => (both index).1, fun index => (both index).2⟩

variable {n : Nat} {Value : Fin n → Type u}

/-- Separate supported observations have supported joint rectangular
evidence under an independent prior. No positive sample is selected. -/
theorem IndependentLaw.rectangular_positive (law : IndependentLaw Value)
    (evidence : (index : Fin n) → Event (Value index))
    (positive : ∀ index, (law.factor index).EventPositive (evidence index)) :
    law.prior.EventPositive (rectangularEvent n Value evidence) :=
  (QProb.equiv_num_pos_iff (law.product_law evidence)).mpr
    ((qProduct_num_pos_iff n _).mpr positive)

/-- The posterior retains exactly the product law of the source-wise
posteriors. Conditional outcomes may have zero mass; only each evidence
denominator must be supported. -/
theorem IndependentLaw.condition_rectangular (law : IndependentLaw Value)
    (evidence : (index : Fin n) → Event (Value index))
    (positive : ∀ index, (law.factor index).EventPositive (evidence index))
    (events : (index : Fin n) → Event (Value index)) :
    QProb.Equiv
      ((law.prior.conditionOn (rectangularEvent n Value evidence)
        (law.rectangular_positive evidence positive)).probVal (rectangularEvent n Value events))
      (qProduct n (fun index =>
        ((law.factor index).conditionOn (evidence index) (positive index)).probVal (events index))) := by
  refine QProb.equiv_trans (law.prior.conditionOn_probVal _ _ _) ?_
  rw [rectangularEvent_inter]
  refine QProb.equiv_trans
    (QProb.div_congr (law.product_law (fun index value => evidence index value && events index value))
      (law.product_law evidence) (law.rectangular_positive evidence positive)
      ((qProduct_num_pos_iff n _).mpr positive)) ?_
  refine QProb.equiv_trans (QProb.equiv_symm (qProduct_div n
    (fun index => (law.factor index).probVal (fun value => evidence index value && events index value))
    (fun index => (law.factor index).probVal (evidence index)) positive)) ?_
  exact qProduct_congr n (fun index => QProb.equiv_symm
    ((law.factor index).conditionOn_probVal (evidence index) (events index) (positive index)))

/-- Package the posterior as another proof-carrying independent law.
Mechanism and incidence data can therefore keep their old independence
assumptions for this explicitly proved class of epistemic observations. -/
def IndependentLaw.condition (law : IndependentLaw Value)
    (evidence : (index : Fin n) → Event (Value index))
    (positive : ∀ index, (law.factor index).EventPositive (evidence index)) :
    IndependentLaw Value where
  factor index := (law.factor index).conditionOn (evidence index) (positive index)
  prior := law.prior.conditionOn (rectangularEvent n Value evidence)
    (law.rectangular_positive evidence positive)
  product_law := law.condition_rectangular evidence positive

/-- The reconstructed product agrees with every posterior event, including
events coupling coordinates. Supplied complete coordinate listings and
decidable equalities provide the constructive finite-extensionality bridge. -/
theorem IndependentLaw.condition_all_events (law : IndependentLaw Value)
    (evidence : (index : Fin n) → Event (Value index))
    (positive : ∀ index, (law.factor index).EventPositive (evidence index))
    (values : (index : Fin n) → List (Value index))
    (complete : ∀ index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index))
    (event : Event (Assignment n Value)) :
    QProb.Equiv ((law.condition evidence positive).prior.probVal event)
      ((record n Value (law.condition evidence positive).factor).probVal event) := by
  apply probVal_extensional_of_rectangles _ _ values complete decEq ?_ event
  intro events
  exact QProb.equiv_trans ((law.condition evidence positive).product_law events)
    (QProb.equiv_symm (record_rectangular_probVal n Value _ events))

end Thesis.Probability.FiniteProduct
