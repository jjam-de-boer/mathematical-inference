import Thesis.Probability.ConstructiveRealCauchyOrder

namespace Thesis.Probability.ConstructiveReal

/-- Two-sided closed error bounds whose radius is itself a constructive real.
The rational-error interface `Within` is its exact embedded specialization. -/
def WithinReal (error x y : ConstructiveReal) : Prop := LE x (add y error) ∧ LE y (add x error)

theorem withinReal_congr {error error' x x' y y' : ConstructiveReal}
    (radius : Equiv error error') (first : Equiv x x') (second : Equiv y y') :
    WithinReal error x y ↔ WithinReal error' x' y' :=
  and_congr (le_congr first (add_congr second radius)) (le_congr second (add_congr first radius))

theorem withinReal_mono {error larger x y : ConstructiveReal} (bounded : WithinReal error x y) (enlarged : LE error larger) :
    WithinReal larger x y :=
  ⟨le_trans bounded.1 (add_le_add (le_refl _) enlarged), le_trans bounded.2 (add_le_add (le_refl _) enlarged)⟩

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- A varying, convergent analytic error bound passes to the effective limits
along with the two values it compares. -/
theorem limit_withinReal (first second error : RealCauchySequence)
    (bounded : ∀ n, WithinReal (error.value n) (first.value n) (second.value n)) :
    WithinReal error.limit first.limit second.limit :=
  ⟨(le_congr (equiv_refl _) (second.add_limit error)).mp
      (limit_le_limit first (second.add error) (fun n => (bounded n).1)),
    (le_congr (equiv_refl _) (first.add_limit error)).mp
      (limit_le_limit second (first.add error) (fun n => (bounded n).2))⟩

end Thesis.Probability.RealCauchySequence
