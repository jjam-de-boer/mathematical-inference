import Thesis.Probability.FiniteProductReplacement

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteProductReplacement

open FiniteProduct

/-!
# Coordinate replacement preserves the full law and other marginals

A biased two-bit independent law is given as an actual finite product.  The
arbitrary-event theorem checks replacement by the original factor, while a
new probability-one first bit gives a different, computed xor probability.
The unused zero atom in that replacement is intentionally retained.

A second fixture has genuinely different coordinate types, `Fin 2` and
`Fin 3`.  Updating the latter exercises the dependent transport rather than
only a homogeneous Bool assignment.  These are small kernel computations;
the whole-law equality itself is obtained symbolically from rectangles.
-/

def first : Fin 2 := ⟨0, by decide⟩
def second : Fin 2 := ⟨1, by decide⟩
def leading : FiniteProbRecord Bool := ⟨[(false, 1), (true, 2)], 3, by decide, rfl⟩
def trailing : FiniteProbRecord Bool := ⟨[(false, 3), (true, 1)], 4, by decide, rfl⟩
def factors (index : Fin 2) : FiniteProbRecord Bool := if index = first then leading else trailing
def law : IndependentLaw (fun _ : Fin 2 => Bool) :=
  ⟨factors, record 2 (fun _ => Bool) factors, record_rectangular_probVal 2 (fun _ => Bool) factors⟩

theorem original_replacement_every_event (event : Event (Fin 2 → Bool)) :
    QProb.Equiv ((law.replace first (law.factor first)).prior.probVal event) (law.prior.probVal event) :=
  replace_original_probVal law (fun _ => [false, true]) (by intro _ value; cases value <;> simp)
    (fun _ => inferInstance) first event

def certain : FiniteProbRecord Bool := ⟨[(false, 0), (true, 1)], 1, by decide, rfl⟩
def updated := law.replace first certain
theorem other_factor_unchanged : updated.factor second = law.factor second :=
  replaceFactor_other law.factor first certain second (by decide)
theorem updated_xor : QProb.Equiv (updated.prior.probVal (fun unit => Bool.xor (unit first) (unit second)))
    ⟨3, 4, by decide⟩ := by decide +kernel

def heterogeneousValue (index : Fin 2) := Fin (index.val + 2)
def zeroFactors (index : Fin 2) : FiniteProbRecord (heterogeneousValue index) :=
  ⟨[(⟨0, by have bounded := index.isLt; omega⟩, 1)], 1, by decide, rfl⟩
def heterogeneous : IndependentLaw heterogeneousValue :=
  ⟨zeroFactors, record 2 heterogeneousValue zeroFactors, record_rectangular_probVal 2 heterogeneousValue zeroFactors⟩
def lastValue : FiniteProbRecord (heterogeneousValue second) := ⟨[(⟨2, by decide⟩, 1)], 1, by decide, rfl⟩
def heterogeneousUpdated := heterogeneous.replace second lastValue
theorem heterogeneous_readout : QProb.Equiv
    (heterogeneousUpdated.prior.probVal (fun unit => decide ((unit first).val = 0 ∧ (unit second).val = 2))) QProb.one := by
  decide +kernel

end FiniteProductReplacement
end Examples
end Probability
end Thesis
