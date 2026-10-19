import Thesis.Probability.IndependentBooleanObstruction

namespace Thesis.Probability.Examples.IndependentBooleanObstruction

open FiniteProbRecord
open Probability.IndependentBooleanObstruction

/-!
# Fixed mechanisms, not their parent graph, cause the rational obstruction

The obstructed readout uses three independent Boolean inputs. Making `A`
certainly true and the other inputs fair satisfies the conjunction and joint
targets, but not the remaining outcome target. This checks that the three
equations cannot be replaced by a superficial support or denominator test.

On the same finite independent-source space, the alternative readout
`(O, V) = (F, A)` really does have the complete uniform event law. Its smaller
parent sets are allowed subsets of the original readout's parent sets. The
uniform table is therefore not intrinsically incompatible with rational
finite probability or with that parent graph; the negative theorem fixes
the original mechanisms. These examples introduce no real-valued law.
-/

def fair : FiniteProbRecord Bool := ⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩
def certainTrue : FiniteProbRecord Bool := ⟨[(true, 1)], 1, by decide, rfl⟩
def repeatedFair : FiniteProbRecord Bool := ⟨[(false, 0), (true, 2), (false, 2), (true, 0)], 4, by decide, rfl⟩

theorem partial_targets_really_fit :
    QProb.Equiv ((law certainTrue fair fair).probVal Prod.snd) ⟨1, 2, by decide⟩ ∧
    QProb.Equiv ((law certainTrue fair fair).probVal (fun pair => pair.1 && pair.2)) ⟨1, 4, by decide⟩ := by decide +kernel

theorem third_target_fails :
    ¬ QProb.Equiv ((law certainTrue fair fair).probVal Prod.fst) ⟨1, 2, by decide⟩ := by decide +kernel

theorem repeated_zero_records_excluded :
    ¬ (∀ event, QProb.Equiv ((law repeatedFair repeatedFair repeatedFair).probVal event) (uniform.probVal event)) :=
  not_uniform repeatedFair repeatedFair repeatedFair

def alternativeLaw : FiniteProbRecord (Bool × Bool) :=
  (inputLaw fair fair fair).map (fun state => (state.1, state.2.1))

/-- Equality holds for every observed event, not just the three marginals
used in the obstruction. The independent unused input integrates out. -/
theorem alternative_uniform (event : Event (Bool × Bool)) :
    QProb.Equiv (alternativeLaw.probVal event) (uniform.probVal event) := by
  apply probVal_extensional_of_singletons alternativeLaw uniform
    [(false, false), (false, true), (true, false), (true, true)]
    (by decide)
    (by intro reference; rcases reference with ⟨first, second⟩; cases first <;> cases second <;> decide)
    (fun reference => ?_) event
  rcases reference with ⟨first, second⟩
  cases first <;> cases second <;> decide +kernel

end Thesis.Probability.Examples.IndependentBooleanObstruction
