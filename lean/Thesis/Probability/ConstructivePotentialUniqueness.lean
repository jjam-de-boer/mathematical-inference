import Thesis.Probability.ConstructiveUniformDerivative

namespace Thesis.Probability.ConstructiveReal.UniformDerivativeWithin
open ConstructiveReal

/-- Two independently supplied functions with the same certified uniform
first variation differ by a constant along an admitted interval. The proof
uses finite rational partition bounds; no mean-value point, real sign
decision, compactness axiom, or equality of the functions is assumed. -/
theorem difference_constant {domain : ConstructiveReal → Prop}
    {first second firstSlope secondSlope : ∀ x, domain x → ConstructiveReal}
    (firstDerivative : UniformDerivativeWithin domain first firstSlope)
    (secondDerivative : UniformDerivativeWithin domain second secondSlope)
    (sameSlope : ∀ x hx, Equiv (firstSlope x hx) (secondSlope x hx))
    (a b : ConstructiveReal) (ordered : LE a b) (width : LE (sub b a) one)
    (admitted : ∀ x, LE a x → LE x b → domain x) :
    Equiv (sub (first b (admitted b ordered (le_refl b))) (second b (admitted b ordered (le_refl b))))
      (sub (first a (admitted a (le_refl a) ordered)) (second a (admitted a (le_refl a) ordered))) := by
  let difference : UniformDerivativeWithin domain (fun x hx => sub (first x hx) (second x hx)) (fun _ _ => zero) :=
    (firstDerivative.add secondDerivative.neg).slope_congr (fun x hx => (sub_equiv_zero_iff _ _).mpr (sameSlope x hx))
  have upper := difference.upper_bound a b zero ordered width admitted (fun _ _ _ _ => le_refl zero)
  have lower := difference.lower_bound a b zero ordered width admitted (fun _ _ _ _ => le_refl zero)
  have canceled : Equiv (ConstructiveReal.add
      (sub (first a (admitted a (le_refl a) ordered)) (second a (admitted a (le_refl a) ordered)))
      (mul (sub b a) zero))
      (sub (first a (admitted a (le_refl a) ordered)) (second a (admitted a (le_refl a) ordered))) :=
    equiv_trans (add_congr (equiv_refl _) (mul_zero _)) (add_zero _)
  exact ⟨(le_congr (equiv_refl _) canceled).mp upper, (le_congr canceled (equiv_refl _)).mp lower⟩

/-- A reference convention fixes the additive constant between independent
potentials. Uniform quantitative regularity is explicit: pointwise
smoothness alone is not silently promoted to a uniform certificate. -/
theorem agreement_of_reference {domain : ConstructiveReal → Prop}
    {first second firstSlope secondSlope : ∀ x, domain x → ConstructiveReal}
    (firstDerivative : UniformDerivativeWithin domain first firstSlope)
    (secondDerivative : UniformDerivativeWithin domain second secondSlope)
    (sameSlope : ∀ x hx, Equiv (firstSlope x hx) (secondSlope x hx))
    (a b constant : ConstructiveReal) (ordered : LE a b) (width : LE (sub b a) one)
    (admitted : ∀ x, LE a x → LE x b → domain x)
    (reference : Equiv (first a (admitted a (le_refl a) ordered))
      (ConstructiveReal.add (second a (admitted a (le_refl a) ordered)) constant)) :
    Equiv (first b (admitted b ordered (le_refl b)))
      (ConstructiveReal.add (second b (admitted b ordered (le_refl b))) constant) := by
  let firstA := first a (admitted a (le_refl a) ordered)
  let secondA := second a (admitted a (le_refl a) ordered)
  let firstB := first b (admitted b ordered (le_refl b))
  let secondB := second b (admitted b ordered (le_refl b))
  have atReference : Equiv (sub firstA secondA) constant :=
    equiv_trans (add_congr reference (equiv_refl _))
      (equiv_trans (add_congr (add_comm _ _) (equiv_refl _))
        (equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg _)) (add_zero _))))
  have difference := equiv_trans (firstDerivative.difference_constant secondDerivative sameSlope a b ordered width admitted) atReference
  have restored : Equiv (ConstructiveReal.add (sub firstB secondB) secondB) firstB :=
    equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (add_neg _))) (add_zero _))
  exact equiv_trans (equiv_symm restored) (equiv_trans (add_congr difference (equiv_refl _)) (add_comm _ _))

end Thesis.Probability.ConstructiveReal.UniformDerivativeWithin
