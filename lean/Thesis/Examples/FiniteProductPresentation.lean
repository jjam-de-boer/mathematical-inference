import Thesis.Probability.FiniteProductPresentation

namespace Thesis.Probability.Examples.FiniteProductPresentation

/-!
# Unequal source alphabets, repeated labels and zero-weight codes

Both original source types are Boolean. Their sampling presentations have
three and two codes respectively. The first keeps a zero-weight false atom
and two occurrences of true; decoding is intentionally not injective.
The mixed XOR event checks joint-law recovery, rather than only individual
coordinate marginals. A separate empty-family instantiation retains the
unit product without assuming a positive number of sources.
-/

def left : FiniteProbRecord Bool := ⟨[(false, 0), (true, 1), (true, 3)], 4, by decide, rfl⟩
def right : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩
def factors (index : Fin 2) := if index.val = 0 then left else right
def prior := FiniteProduct.record 2 (fun _ => Bool) factors
def presentations (index : Fin 2) := (factors index).atomPresentation

theorem first_card : (presentations 0).card = 3 := rfl
theorem second_card : (presentations 1).card = 2 := rfl
theorem null_position_retained : (presentations 0).decode 0 = false := rfl
theorem repeated_label : (presentations 0).decode 1 = (presentations 0).decode 2 := rfl

theorem every_joint_event (event : Event (FiniteProduct.Assignment 2 (fun _ => Bool))) :
    QProb.Equiv ((FiniteProduct.presentationRecord presentations).probVal
      (fun codes => event (FiniteProduct.decodePresentation presentations codes))) (prior.probVal event) :=
  FiniteProduct.presentation_probVal prior (FiniteProduct.record_rectangular_probVal 2 _ factors)
    (fun _ => [false, true]) (fun _ value => by cases value <;> simp) (fun _ => inferInstance) presentations event

def mixed : Event (FiniteProduct.Assignment 2 (fun _ => Bool)) := fun values => Bool.xor (values 0) (values 1)

theorem mixed_value :
    QProb.Equiv ((FiniteProduct.presentationRecord presentations).probVal
      (fun codes => mixed (FiniteProduct.decodePresentation presentations codes))) ⟨2, 3, by decide⟩ :=
  QProb.equiv_trans (every_joint_event mixed) (by decide +kernel)

theorem decoded_null_stays_null :
    QProb.Equiv ((FiniteProduct.presentationRecord presentations).probVal
      (fun codes => !(FiniteProduct.decodePresentation presentations codes 0))) QProb.zero :=
  QProb.equiv_trans (every_joint_event (fun values => !(values 0))) (by decide +kernel)

def emptyFactors (index : Fin 0) : FiniteProbRecord Bool := Fin.elim0 index
def emptyPresentations (index : Fin 0) : FiniteProbRecord.FinitePresentation (emptyFactors index) := Fin.elim0 index

theorem empty_joint (event : Event (FiniteProduct.Assignment 0 (fun _ => Bool))) :
    QProb.Equiv ((FiniteProduct.presentationRecord emptyPresentations).probVal
      (fun codes => event (FiniteProduct.decodePresentation emptyPresentations codes)))
      ((FiniteProduct.record 0 (fun _ => Bool) emptyFactors).probVal event) :=
  FiniteProduct.presentation_probVal _ (FiniteProduct.record_rectangular_probVal 0 _ emptyFactors)
    (fun _ => [false, true]) (fun _ value => by cases value <;> simp) (fun _ => inferInstance) emptyPresentations event

end Thesis.Probability.Examples.FiniteProductPresentation
