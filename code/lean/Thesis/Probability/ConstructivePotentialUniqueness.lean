import Thesis.Probability.ConstructiveUniformAffine

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

/-- Equal certified variations determine potentials up to a constant on
any admitted finite interval. An exact affine change of parameter reduces
the proof to the unit-interval telescope, removing the auxiliary width bound
without a real sign decision or an assumed compactness principle. -/
theorem difference_constant_on_interval {domain : ConstructiveReal → Prop}
    {first second firstSlope secondSlope : ∀ x, domain x → ConstructiveReal}
    (firstDerivative : UniformDerivativeWithin domain first firstSlope)
    (secondDerivative : UniformDerivativeWithin domain second secondSlope)
    (sameSlope : ∀ x hx, Equiv (firstSlope x hx) (secondSlope x hx))
    (a b : ConstructiveReal) (ordered : LE a b)
    (admitted : ∀ x, LE a x → LE x b → domain x) :
    Equiv (sub (first b (admitted b ordered (le_refl b))) (second b (admitted b ordered (le_refl b))))
      (sub (first a (admitted a (le_refl a) ordered)) (second a (admitted a (le_refl a) ordered))) := by
  let delta := sub b a
  let unit := fun x => LE zero x ∧ LE x one
  let point := fun t => ConstructiveReal.add (mul t delta) a
  have deltaNonnegative : LE zero delta := (zero_le_sub_iff b a).mpr ordered
  have restored : Equiv (ConstructiveReal.add delta a) b :=
    equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _)
      (equiv_trans (add_comm _ _) (add_neg a))) (add_zero b))
  have pointBounds (t : ConstructiveReal) (ht : unit t) : LE a (point t) ∧ LE (point t) b := by
    have positive := mul_nonnegative ht.1 deltaNonnegative
    have upper := mul_le_mul_nonnegative_right deltaNonnegative ht.2
    exact ⟨(le_congr (zero_add a) (equiv_refl _)).mp (add_le_add positive (le_refl a)),
      (le_congr (equiv_refl _) (equiv_trans (add_congr (one_mul delta) (equiv_refl a)) restored)).mp
        (add_le_add upper (le_refl a))⟩
  let included := fun t ht => admitted (point t) (pointBounds t ht).1 (pointBounds t ht).2
  let firstPulled := firstDerivative.affine_pullback delta a included
  let secondPulled := secondDerivative.affine_pullback delta a included
  have zeroOne : LE zero one := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  have unitWidth : LE (sub one zero) one :=
    (le_congr (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero one))
      (equiv_refl one)).mpr (le_refl one)
  have compared := firstPulled.difference_constant secondPulled
    (fun t ht => mul_congr (equiv_refl delta) (sameSlope (point t) (included t ht)))
    zero one zeroOne unitWidth (fun _ above below => ⟨above, below⟩)
  have atZero : Equiv (point zero) a := equiv_trans (add_congr (zero_mul delta) (equiv_refl a)) (zero_add a)
  have atOne : Equiv (point one) b := equiv_trans (add_congr (one_mul delta) (equiv_refl a)) restored
  have left : Equiv (sub (first (point one) (included one ⟨zeroOne, le_refl one⟩))
      (second (point one) (included one ⟨zeroOne, le_refl one⟩)))
      (sub (first b (admitted b ordered (le_refl b))) (second b (admitted b ordered (le_refl b)))) :=
    add_congr (firstDerivative.congr _ _ _ _ atOne) (neg_congr (secondDerivative.congr _ _ _ _ atOne))
  have right : Equiv (sub (first (point zero) (included zero ⟨le_refl zero, zeroOne⟩))
      (second (point zero) (included zero ⟨le_refl zero, zeroOne⟩)))
      (sub (first a (admitted a (le_refl a) ordered)) (second a (admitted a (le_refl a) ordered))) :=
    add_congr (firstDerivative.congr _ _ _ _ atZero) (neg_congr (secondDerivative.congr _ _ _ _ atZero))
  exact equiv_trans (equiv_symm left) (equiv_trans compared right)

/-- Reference-normalized agreement on any admitted ordered interval, with
no auxiliary bound on its parameter length. -/
theorem agreement_of_reference_on_interval {domain : ConstructiveReal → Prop}
    {first second firstSlope secondSlope : ∀ x, domain x → ConstructiveReal}
    (firstDerivative : UniformDerivativeWithin domain first firstSlope)
    (secondDerivative : UniformDerivativeWithin domain second secondSlope)
    (sameSlope : ∀ x hx, Equiv (firstSlope x hx) (secondSlope x hx))
    (a b constant : ConstructiveReal) (ordered : LE a b)
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
  have difference := equiv_trans (firstDerivative.difference_constant_on_interval secondDerivative sameSlope a b ordered admitted) atReference
  have restored : Equiv (ConstructiveReal.add (sub firstB secondB) secondB) firstB :=
    equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (add_neg _))) (add_zero _))
  exact equiv_trans (equiv_symm restored) (equiv_trans (add_congr difference (equiv_refl _)) (add_comm _ _))

end Thesis.Probability.ConstructiveReal.UniformDerivativeWithin
