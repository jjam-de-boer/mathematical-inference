import Thesis.Probability.Distros.RationalLinearOrder

namespace Thesis.Probability.Distros

/-- An executable one-variable inequality decision with a computed witness
or an explicit pair of incompatible rational endpoints. -/
inductive RationalIntervalCheck (lower upper : List SignedRatio) where
  | feasible (value : SignedRatio) (lowerBound : ∀ bound ∈ lower, SignedRatio.LE bound value)
      (upperBound : ∀ bound ∈ upper, SignedRatio.LE value bound)
  | infeasible (below : SignedRatio) (lowerMember : below ∈ lower)
      (above : SignedRatio) (upperMember : above ∈ upper) (incompatible : ¬ SignedRatio.LE below above)

def checkRationalInterval (lower upper : List SignedRatio) : RationalIntervalCheck lower upper :=
  match lower, upper with
  | [], [] => .feasible SignedRatio.zero (by intro bound member; exact False.elim (List.not_mem_nil member))
      (by intro bound member; exact False.elim (List.not_mem_nil member))
  | [], above :: upper => .feasible (SignedRatio.selectMin above upper)
      (by intro bound member; exact False.elim (List.not_mem_nil member)) (SignedRatio.selectMin_bounds above upper)
  | below :: lower, [] => .feasible (SignedRatio.selectMax below lower) (SignedRatio.selectMax_bounds below lower)
      (by intro bound member; exact False.elim (List.not_mem_nil member))
  | below :: lower, above :: upper =>
      let lo := SignedRatio.selectMax below lower
      let hi := SignedRatio.selectMin above upper
      if compatible : SignedRatio.LE lo hi then
        .feasible lo (SignedRatio.selectMax_bounds below lower)
          (fun bound member => SignedRatio.le_trans compatible (SignedRatio.selectMin_bounds above upper bound member))
      else .infeasible lo (SignedRatio.selectMax_mem below lower) hi (SignedRatio.selectMin_mem above upper) compatible

theorem RationalIntervalCheck.infeasible_not_exists (lower upper : List SignedRatio)
    (below : SignedRatio) (lowerMember : below ∈ lower) (above : SignedRatio) (upperMember : above ∈ upper)
    (incompatible : ¬ SignedRatio.LE below above) :
    ¬ ∃ value : SignedRatio, (∀ bound ∈ lower, SignedRatio.LE bound value) ∧ (∀ bound ∈ upper, SignedRatio.LE value bound) := by
  rintro ⟨value, lows, highs⟩
  exact incompatible (SignedRatio.le_trans (lows below lowerMember) (highs above upperMember))

end Thesis.Probability.Distros
