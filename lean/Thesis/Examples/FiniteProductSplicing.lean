import Thesis.Probability.FiniteProductSplicing

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteProductSplicing

/-!
# Splicing regressions with unequal biases and zero-weight labels

The first coordinate has success probability two thirds and the second one
quarter.  An exclusive-or event inspects both readouts, so preservation of
its law is stronger than checking each marginal alone.  The same universal
coupling theorem is also applied after replacing the first factor by a
probability-one record that retains a listed zero-weight false atom.

Only the two-coordinate numerical fixture is evaluated by kernel reduction.
The arbitrary-event independence and law-preservation claims come from the
symbolic theorem, with the actual finite product law as input evidence.
-/

def first : Fin 2 := ⟨0, by decide⟩
def second : Fin 2 := ⟨1, by decide⟩

def firstFactor : FiniteProbRecord Bool :=
  ⟨[(false, 1), (true, 2)], 3, by decide, rfl⟩

def secondFactor : FiniteProbRecord Bool :=
  ⟨[(false, 3), (true, 1)], 4, by decide, rfl⟩

def concentrated : FiniteProbRecord Bool :=
  ⟨[(false, 0), (true, 1)], 1, by decide, rfl⟩

def factors (leading : FiniteProbRecord Bool) (index : Fin 2) : FiniteProbRecord Bool :=
  if index = first then leading else secondFactor

def source (leading : FiniteProbRecord Bool) : FiniteProbRecord (Fin 2 → Bool) :=
  FiniteProduct.record 2 (fun _ => Bool) (factors leading)

def allocation : Fin 2 → Bool := fun index => decide (index = first)
def leftRead : (Fin 2 → Bool) → Bool := fun unit => unit first
def rightRead : (Fin 2 → Bool) → Bool := fun unit => unit second

theorem arbitrary_event_independence (leading : FiniteProbRecord Bool) (event : Event (Bool × Bool)) :
    QProb.Equiv ((source leading).probVal (fun unit => event (leftRead unit, rightRead unit)))
      ((((source leading).map leftRead).product ((source leading).map rightRead)).probVal event) :=
  FiniteProduct.readouts_product_probVal (source leading) (factors leading)
    (FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool) (factors leading))
    (fun _ => [false, true]) (by intro _ value; cases value <;> simp)
    (fun _ => inferInstance) allocation leftRead rightRead
    (by intro _ _; rfl) (by intro _ _; rfl) event

theorem arbitrary_event_splice_preservation (leading : FiniteProbRecord Bool) (event : Event (Fin 2 → Bool)) :
    QProb.Equiv ((FiniteProduct.splicedRecord (source leading) allocation).probVal event)
      ((source leading).probVal event) :=
  FiniteProduct.splicedRecord_probVal (source leading) (factors leading)
    (FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool) (factors leading))
    (fun _ => [false, true]) (by intro _ value; cases value <;> simp)
    (fun _ => inferInstance) allocation event

/-- A genuinely mixed event has the correct nontrivial biased value. -/
theorem biased_xor_value :
    QProb.Equiv ((source firstFactor).probVal (fun unit => Bool.xor (leftRead unit) (rightRead unit)))
      ⟨7, 12, by decide⟩ := by decide +kernel

/-- Independence survives a zero-containing factor without requiring its
listed false label to carry positive mass or selecting a replacement label. -/
theorem concentrated_xor_independence :
    QProb.Equiv ((source concentrated).probVal (fun unit => Bool.xor (leftRead unit) (rightRead unit)))
      ((((source concentrated).map leftRead).product ((source concentrated).map rightRead)).probVal
        (fun pair => Bool.xor pair.1 pair.2)) :=
  arbitrary_event_independence concentrated (fun pair => Bool.xor pair.1 pair.2)

end FiniteProductSplicing
end Examples
end Probability
end Thesis
