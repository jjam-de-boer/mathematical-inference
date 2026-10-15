import Thesis.Probability.FiniteProductExtensional
import Thesis.Probability.FiniteProductResponse

namespace Thesis
namespace Probability
namespace FiniteProduct

universe u
variable {n : Nat} {Value : Fin n → Type u}

/-!
# Replace one coordinate of an independent finite law

The supplied law need not literally be the canonical product record.  Its
rectangular product law suffices, and finite extensionality transfers equality
to arbitrary events.  Replacement samples a fresh coordinate independently
of the old joint assignment, then overwrites just that coordinate.  The old
coordinate is integrated out, not fixed to a default value and not conditioned
on a positive source cell.

The value family, all other coordinate factors and their independence are
retained.  Dependent transports use only decidable finite-index equality.
Replacing a coordinate with its original factor preserves every event,
including events inspecting many coordinates together.
-/

structure IndependentLaw (Value : Fin n → Type u) where
  factor : (index : Fin n) → FiniteProbRecord (Value index)
  prior : FiniteProbRecord (Assignment n Value)
  product_law : forall events, QProb.Equiv (prior.probVal (rectangularEvent n Value events))
    (qProduct n (fun index => (factor index).probVal (events index)))

def replaceCoordinate (chosen : Fin n) (value : Value chosen) (background : Assignment n Value) : Assignment n Value :=
  fun index => if same : index = chosen then same.symm ▸ value else background index

theorem replaceCoordinate_chosen (chosen : Fin n) (value : Value chosen) (background : Assignment n Value) :
    replaceCoordinate chosen value background chosen = value := by
  simp only [replaceCoordinate, dif_pos rfl]

theorem replaceCoordinate_other (chosen : Fin n) (value : Value chosen) (background : Assignment n Value)
    (index : Fin n) (different : index ≠ chosen) :
    replaceCoordinate chosen value background index = background index := by
  simp only [replaceCoordinate, dif_neg different]

def replaceFactor (factors : (index : Fin n) → FiniteProbRecord (Value index)) (chosen : Fin n)
    (replacement : FiniteProbRecord (Value chosen)) : (index : Fin n) → FiniteProbRecord (Value index) :=
  fun index => if same : index = chosen then same.symm ▸ replacement else factors index

theorem replaceFactor_chosen (factors : (index : Fin n) → FiniteProbRecord (Value index)) (chosen : Fin n)
    (replacement : FiniteProbRecord (Value chosen)) : replaceFactor factors chosen replacement chosen = replacement := by
  simp only [replaceFactor, dif_pos rfl]

theorem replaceFactor_other (factors : (index : Fin n) → FiniteProbRecord (Value index)) (chosen : Fin n)
    (replacement : FiniteProbRecord (Value chosen)) (index : Fin n) (different : index ≠ chosen) :
    replaceFactor factors chosen replacement index = factors index := by
  simp only [replaceFactor, dif_neg different]

theorem replaceFactor_self (factors : (index : Fin n) → FiniteProbRecord (Value index)) (chosen : Fin n) :
    replaceFactor factors chosen (factors chosen) = factors := by
  funext index
  by_cases same : index = chosen
  · subst index
    exact replaceFactor_chosen factors chosen (factors chosen)
  · exact replaceFactor_other factors chosen (factors chosen) index same

def eventsWithout (chosen : Fin n) (events : (index : Fin n) → Event (Value index)) :
    (index : Fin n) → Event (Value index) :=
  fun index value => if index = chosen then true else events index value

theorem replaceCoordinate_rectangle (chosen : Fin n) (value : Value chosen) (background : Assignment n Value)
    (events : (index : Fin n) → Event (Value index)) :
    rectangularEvent n Value events (replaceCoordinate chosen value background) =
      (events chosen value && rectangularEvent n Value (eventsWithout chosen events) background) := by
  apply Bool.eq_iff_iff.mpr
  rw [rectangularEvent_eq_true_iff, Bool.and_eq_true_iff, rectangularEvent_eq_true_iff]
  constructor
  · intro selected
    constructor
    · simpa only [replaceCoordinate_chosen] using selected chosen
    · intro index
      by_cases same : index = chosen
      · simp only [eventsWithout, if_pos same]
      · simpa only [eventsWithout, if_neg same, replaceCoordinate_other chosen value background index same] using selected index
  · rintro ⟨chosenSelected, backgroundSelected⟩ index
    by_cases same : index = chosen
    · subst index
      simpa only [replaceCoordinate_chosen] using chosenSelected
    · simpa only [eventsWithout, if_neg same, replaceCoordinate_other chosen value background index same] using backgroundSelected index

def replaceRecord (original : IndependentLaw Value) (chosen : Fin n) (replacement : FiniteProbRecord (Value chosen)) :
    FiniteProbRecord (Assignment n Value) :=
  (replacement.product original.prior).map (fun pair => replaceCoordinate chosen pair.1 pair.2)

/-- The actual overwritten record has the product law of the updated
factors.  No source probability is cancelled, including at the coordinate
being overwritten or in the unchanged background. -/
theorem replaceRecord_product_law (original : IndependentLaw Value) (chosen : Fin n)
    (replacement : FiniteProbRecord (Value chosen)) (events : (index : Fin n) → Event (Value index)) :
    QProb.Equiv ((replaceRecord original chosen replacement).probVal (rectangularEvent n Value events))
      (qProduct n (fun index => (replaceFactor original.factor chosen replacement index).probVal (events index))) := by
  have paired := QProb.equiv_trans
    ((replacement.product original.prior).map_probVal (fun pair => replaceCoordinate chosen pair.1 pair.2) _)
    (QProb.equiv_trans
      ((replacement.product original.prior).probVal_congr _ _ (fun pair => replaceCoordinate_rectangle chosen pair.1 pair.2 events))
      (replacement.product_probVal original.prior (events chosen) (rectangularEvent n Value (eventsWithout chosen events))))
  have remaining : QProb.Equiv (original.prior.probVal (rectangularEvent n Value (eventsWithout chosen events)))
      (qProductWithout n chosen (fun index => (replaceFactor original.factor chosen replacement index).probVal (events index))) := by
    refine QProb.equiv_trans (original.product_law (eventsWithout chosen events)) ?_
    apply qProduct_congr n
    intro index
    by_cases same : index = chosen
    · subst index
      simp only [if_pos rfl]
      exact QProb.equiv_trans ((original.factor chosen).probVal_congr _ topEvent (fun value => by
        simp only [eventsWithout, if_pos rfl, topEvent])) (original.factor chosen).normalization
    · simp only [if_neg same, replaceFactor_other original.factor chosen replacement index same]
      exact (original.factor index).probVal_congr _ _ (fun value => by simp only [eventsWithout, if_neg same])
  have isolated := qProduct_coordinate n chosen
    (fun index => (replaceFactor original.factor chosen replacement index).probVal (events index))
  rw [replaceFactor_chosen] at isolated
  exact QProb.equiv_trans paired (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) remaining)
    (QProb.equiv_symm isolated))

def IndependentLaw.replace (original : IndependentLaw Value) (chosen : Fin n)
    (replacement : FiniteProbRecord (Value chosen)) : IndependentLaw Value :=
  ⟨replaceFactor original.factor chosen replacement, replaceRecord original chosen replacement,
    replaceRecord_product_law original chosen replacement⟩

theorem replace_original_probVal (original : IndependentLaw Value)
    (values : (index : Fin n) → List (Value index)) (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index)) (chosen : Fin n) (event : Event (Assignment n Value)) :
    QProb.Equiv ((original.replace chosen (original.factor chosen)).prior.probVal event) (original.prior.probVal event) := by
  apply probVal_extensional_of_rectangles _ _ values complete decEq (fun events => ?_) event
  have updated := (original.replace chosen (original.factor chosen)).product_law events
  change QProb.Equiv _ (qProduct n (fun index => (replaceFactor original.factor chosen (original.factor chosen) index).probVal (events index))) at updated
  rw [replaceFactor_self] at updated
  exact QProb.equiv_trans updated (QProb.equiv_symm (original.product_law events))

end FiniteProduct
end Probability
end Thesis
