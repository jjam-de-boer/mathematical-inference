import Thesis.Probability.FiniteProductResponse
import Thesis.Probability.FiniteRecordSlicing

namespace Thesis
namespace Probability
namespace FiniteProduct

universe u v w

/-!
# Splicing two independent copies of a finite coordinate law

For an explicitly independent coordinate law, replace each coordinate by
the corresponding coordinate of one of two independent draws.  Any fixed
Boolean allocation preserves the complete original law, including mixed
events that are not rectangles.  The proof first checks rectangles against
the original product-law field, then uses the explicitly finite assignment
enumeration to transfer equality to all events.

This gives a useful constructive independence principle: if one readout
uses only the allocated coordinates and another uses only their complement,
their joint law is the product of their actual pushforward laws.  Neither
source is merged, an arbitrary latent cardinality is not bounded, and no
default value or representative is selected.  We splice actual supplied
assignments, so even unused coordinates need no chosen inhabitant.

Zero weights, repeated atom labels, empty allocations, and an empty coordinate
family are allowed.  There are no conditionals or positive-cell cancellations.
The statement is about the supplied independent law, not an assumed coupling
between unrelated causal models.
-/

variable {n : Nat} {Value : Fin n → Type u}

/-- Each coordinate is read from exactly one of the supplied assignments. -/
def splice (allocation : Fin n → Bool) (left right : Assignment n Value) : Assignment n Value :=
  fun index => if allocation index then left index else right index

private def leftEvents (allocation : Fin n → Bool)
    (events : (index : Fin n) → Value index → Bool) : (index : Fin n) → Value index → Bool :=
  fun index value => if allocation index then events index value else true

private def rightEvents (allocation : Fin n → Bool)
    (events : (index : Fin n) → Value index → Bool) : (index : Fin n) → Value index → Bool :=
  fun index value => if allocation index then true else events index value

/-- A rectangle of the spliced draw separates into one rectangle per copy.
The unused coordinate checks are literally true, not probabilities divided out. -/
private theorem splice_rectangle (allocation : Fin n → Bool)
    (events : (index : Fin n) → Value index → Bool) (left right : Assignment n Value) :
    rectangularEvent n Value events (splice allocation left right) =
      (rectangularEvent n Value (leftEvents allocation events) left &&
        rectangularEvent n Value (rightEvents allocation events) right) := by
  apply Bool.eq_iff_iff.mpr
  rw [rectangularEvent_eq_true_iff, Bool.and_eq_true_iff,
    rectangularEvent_eq_true_iff, rectangularEvent_eq_true_iff]
  constructor
  · intro selected
    constructor
    · intro index
      cases allocated : allocation index with
      | false => simp only [leftEvents, allocated, Bool.false_eq_true, if_false]
      | true => simpa only [leftEvents, splice, allocated, if_true] using selected index
    · intro index
      cases allocated : allocation index with
      | false => simpa only [rightEvents, splice, allocated, Bool.false_eq_true, if_false] using selected index
      | true => simp only [rightEvents, allocated, if_true]
  · rintro ⟨leftSelected, rightSelected⟩ index
    cases allocated : allocation index with
    | false =>
        simpa only [rightEvents, splice, allocated, Bool.false_eq_true, if_false] using rightSelected index
    | true => simpa only [leftEvents, splice, allocated, if_true] using leftSelected index

/-- The actual spliced probability record is a finite independent pair,
pushed through the displayed coordinate map. -/
def splicedRecord (record : FiniteProbRecord (Assignment n Value)) (allocation : Fin n → Bool) :
    FiniteProbRecord (Assignment n Value) :=
  (record.product record).map (fun pair => splice allocation pair.1 pair.2)

private theorem splicedRecord_rectangle
    (record : FiniteProbRecord (Assignment n Value))
    (factors : (index : Fin n) → FiniteProbRecord (Value index))
    (independent : forall events, QProb.Equiv (record.probVal (rectangularEvent n Value events))
      (qProduct n (fun index => (factors index).probVal (events index))))
    (allocation : Fin n → Bool) (events : (index : Fin n) → Value index → Bool) :
    QProb.Equiv ((splicedRecord record allocation).probVal (rectangularEvent n Value events))
      (record.probVal (rectangularEvent n Value events)) := by
  have paired : QProb.Equiv
      ((splicedRecord record allocation).probVal (rectangularEvent n Value events))
      (QProb.mul (record.probVal (rectangularEvent n Value (leftEvents allocation events)))
        (record.probVal (rectangularEvent n Value (rightEvents allocation events)))) :=
    QProb.equiv_trans
      ((record.product record).map_probVal (fun pair => splice allocation pair.1 pair.2) _)
      (QProb.equiv_trans
        ((record.product record).probVal_congr _ _ (fun pair => splice_rectangle allocation events pair.1 pair.2))
        (record.product_probVal record (rectangularEvent n Value (leftEvents allocation events))
          (rectangularEvent n Value (rightEvents allocation events))))
  have coordinate (index : Fin n) : QProb.Equiv
      (QProb.mul ((factors index).probVal (leftEvents allocation events index))
        ((factors index).probVal (rightEvents allocation events index)))
      ((factors index).probVal (events index)) := by
    cases allocated : allocation index with
    | false =>
        simpa only [leftEvents, rightEvents, allocated, Bool.false_eq_true, if_false] using
          (QProb.equiv_trans
            (QProb.mul_congr (factors index).normalization (QProb.equiv_refl ((factors index).probVal (events index))))
            (QProb.one_mul ((factors index).probVal (events index))))
    | true =>
        simpa only [leftEvents, rightEvents, allocated, if_true] using
          (QProb.equiv_trans
            (QProb.mul_congr (QProb.equiv_refl ((factors index).probVal (events index))) (factors index).normalization)
            (QProb.mul_one ((factors index).probVal (events index))))
  exact QProb.equiv_trans paired
    (QProb.equiv_trans
      (QProb.mul_congr (independent (leftEvents allocation events)) (independent (rightEvents allocation events)))
      (QProb.equiv_trans
        (QProb.equiv_symm (qProduct_pointwise_mul n
          (fun index => (factors index).probVal (leftEvents allocation events index))
          (fun index => (factors index).probVal (rightEvents allocation events index))))
        (QProb.equiv_trans (qProduct_congr n coordinate) (QProb.equiv_symm (independent events)))))

/-- Full-assignment singleton events are coordinate rectangles, with an
explicit coordinate equality decision rather than classical function equality. -/
private theorem singleton_rectangle (decEq : (index : Fin n) → DecidableEq (Value index))
    (reference : Assignment n Value) :
    rectangularEvent n Value (fun index value => @decide (value = reference index) (decEq index _ _)) =
      @FiniteProbRecord.singletonEvent _ (assignmentDecidableEq n Value decEq) reference := by
  funext sample
  apply Bool.eq_iff_iff.mpr
  rw [rectangularEvent_eq_true_iff]
  simp only [FiniteProbRecord.singletonEvent, decide_eq_true_eq]
  constructor
  · intro equalCoordinates; exact funext equalCoordinates
  · intro equal; exact congrFun equal

/-- Splicing preserves *every* event, not merely product rectangles.  The
enumeration proof is symbolic and never reduces a concrete large source cube. -/
theorem splicedRecord_probVal
    (record : FiniteProbRecord (Assignment n Value))
    (factors : (index : Fin n) → FiniteProbRecord (Value index))
    (independent : forall events, QProb.Equiv (record.probVal (rectangularEvent n Value events))
      (qProduct n (fun index => (factors index).probVal (events index))))
    (values : (index : Fin n) → List (Value index))
    (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index))
    (allocation : Fin n → Bool) (event : Event (Assignment n Value)) :
    QProb.Equiv ((splicedRecord record allocation).probVal event) (record.probVal event) := by
  letI : DecidableEq (Assignment n Value) := assignmentDecidableEq n Value decEq
  let labels := deduplicate (enumeration n Value values)
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _ labels (deduplicate_nodup _)
    (fun assignment => (mem_deduplicate _ _).mpr (enumeration_complete n Value values complete assignment))
    (fun reference => ?_) event
  rw [← singleton_rectangle decEq reference]
  exact splicedRecord_rectangle record factors independent allocation _

/-- Complementary readouts have the actual product of their pushforward
laws.  The locality premises concern explicit supplied assignments; no
probabilistic independence premise about those readouts is assumed. -/
theorem readouts_product_probVal {Left : Type v} {Right : Type w}
    (record : FiniteProbRecord (Assignment n Value))
    (factors : (index : Fin n) → FiniteProbRecord (Value index))
    (independent : forall events, QProb.Equiv (record.probVal (rectangularEvent n Value events))
      (qProduct n (fun index => (factors index).probVal (events index))))
    (values : (index : Fin n) → List (Value index))
    (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index))
    (allocation : Fin n → Bool) (left : Assignment n Value → Left) (right : Assignment n Value → Right)
    (leftLocal : forall first second, left (splice allocation first second) = left first)
    (rightLocal : forall first second, right (splice allocation first second) = right second)
    (event : Event (Left × Right)) :
    QProb.Equiv (record.probVal (fun unit => event (left unit, right unit)))
      (((record.map left).product (record.map right)).probVal event) := by
  let sourceEvent : Event (Assignment n Value) := fun unit => event (left unit, right unit)
  have preserved := splicedRecord_probVal record factors independent values complete decEq allocation sourceEvent
  have paired := (record.product record).map_probVal (fun pair => splice allocation pair.1 pair.2) sourceEvent
  have localReadouts : QProb.Equiv
      ((record.product record).probVal (fun pair => sourceEvent (splice allocation pair.1 pair.2)))
      ((record.product record).probVal (fun pair => event (left pair.1, right pair.2))) := by
    apply (record.product record).probVal_congr
    intro pair
    simp only [sourceEvent, leftLocal, rightLocal]
  have rightMap := (record.map left).product_map_right_probVal record right event
  have leftMap := record.product_map_left_probVal record left (fun pair => event (pair.1, right pair.2))
  exact QProb.equiv_trans (QProb.equiv_symm preserved)
    (QProb.equiv_trans paired
      (QProb.equiv_trans localReadouts (QProb.equiv_symm (QProb.equiv_trans rightMap leftMap))))

end FiniteProduct
end Probability
end Thesis
