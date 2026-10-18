import Thesis.Probability.FiniteRecordPresentation
import Thesis.Probability.FiniteProductExtensional

namespace Thesis.Probability.FiniteProduct

universe u
variable {n : Nat} {Value : Fin n → Type u}
variable {factors : (index : Fin n) → FiniteProbRecord (Value index)}

/-!
# Independent finite sampling presentations preserve the complete joint law

Each factor can be presented on its own finite sampling codes, with a proved
decoder. Build their actual product record and decode every coordinate.
Factor recovery proves rectangular independence; finite whole-law uniqueness
then proves preservation of *every* mixed event, not only rectangles.

The original prior need only satisfy its product law. It need not literally
be the canonical product record, have distinct atom labels, or assign positive
mass to every enumerated value. Complete original coordinate enumerations and
their equality decisions are supplied explicitly, as in native finite SCMs.

Codes retain natural weights. Their cardinalities count presented positions,
not unit cells or probability denominators. Decoders need not be bijective:
different sampling positions may denote the same old value. No representative
is selected from a proposition and no null conditional is completed here.
-/

abbrev PresentationCode (presentations : (index : Fin n) → FiniteProbRecord.FinitePresentation (factors index))
    (index : Fin n) := Fin (presentations index).card

def presentationRecord (presentations : (index : Fin n) → FiniteProbRecord.FinitePresentation (factors index)) :
    FiniteProbRecord (Assignment n (PresentationCode presentations)) :=
  record n (PresentationCode presentations) (fun index => (presentations index).record)

def decodePresentation (presentations : (index : Fin n) → FiniteProbRecord.FinitePresentation (factors index))
    (codes : Assignment n (PresentationCode presentations)) : Assignment n Value :=
  fun index => (presentations index).decode (codes index)

/-- Coordinate decoding commutes with an arbitrary rectangular event.
The statement includes the empty dependent product. -/
theorem rectangularEvent_decodePresentation
    (presentations : (index : Fin n) → FiniteProbRecord.FinitePresentation (factors index))
    (events : (index : Fin n) → Event (Value index)) (codes : Assignment n (PresentationCode presentations)) :
    rectangularEvent n Value events (decodePresentation presentations codes) =
      rectangularEvent n (PresentationCode presentations)
        (fun index code => events index ((presentations index).decode code)) codes := by
  apply Bool.eq_iff_iff.mpr
  rw [rectangularEvent_eq_true_iff, rectangularEvent_eq_true_iff]
  rfl

/-- The actual coded product reproduces every event of any prior with the
supplied original factors. This is the mixed-event bridge needed when an SCM
mechanism reads several sources together; rectangular agreement alone is not
silently treated as whole-law equality. -/
theorem presentation_probVal
    (prior : FiniteProbRecord (Assignment n Value))
    (productLaw : ∀ events, QProb.Equiv (prior.probVal (rectangularEvent n Value events))
      (qProduct n (fun index => (factors index).probVal (events index))))
    (values : (index : Fin n) → List (Value index)) (complete : ∀ index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index))
    (presentations : (index : Fin n) → FiniteProbRecord.FinitePresentation (factors index))
    (event : Event (Assignment n Value)) :
    QProb.Equiv ((presentationRecord presentations).probVal (fun codes => event (decodePresentation presentations codes)))
      (prior.probVal event) := by
  let decoded := (presentationRecord presentations).map (decodePresentation presentations)
  have rectangles (events : (index : Fin n) → Event (Value index)) :
      QProb.Equiv (decoded.probVal (rectangularEvent n Value events))
        (prior.probVal (rectangularEvent n Value events)) := by
    apply QProb.equiv_trans ((presentationRecord presentations).map_probVal
      (decodePresentation presentations) (rectangularEvent n Value events))
    have sameEvent : (fun codes => rectangularEvent n Value events (decodePresentation presentations codes)) =
        rectangularEvent n (PresentationCode presentations)
          (fun index code => events index ((presentations index).decode code)) :=
      funext (rectangularEvent_decodePresentation presentations events)
    rw [sameEvent]
    exact QProb.equiv_trans
      (record_rectangular_probVal n (PresentationCode presentations) (fun index => (presentations index).record) _)
      (QProb.equiv_trans (qProduct_congr n (fun index => (presentations index).probVal (events index)))
        (QProb.equiv_symm (productLaw events)))
  exact QProb.equiv_trans
    (QProb.equiv_symm ((presentationRecord presentations).map_probVal (decodePresentation presentations) event))
    (probVal_extensional_of_rectangles decoded prior values complete decEq rectangles event)

end Thesis.Probability.FiniteProduct
