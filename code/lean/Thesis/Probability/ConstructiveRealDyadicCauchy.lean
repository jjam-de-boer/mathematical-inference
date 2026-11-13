import Thesis.Probability.RationalSeriesNorm

namespace Thesis.Probability.ConstructiveReal
open RationalGeometricSeries

/-- Summing finite step errors controls the distance between the endpoints.
The values may themselves be irrational; only the supplied bounds are rational. -/
theorem within_of_step_bounds (value : Nat → ConstructiveReal) (sizes : Nat → QProb)
    (steps : ∀ n, Within (sizes n) (value n) (value (n + 1))) (start count : Nat) :
    Within (normSum sizes start count) (value start) (value (start + count)) := by
  induction count generalizing start with
  | zero => simpa only [normSum, Nat.add_zero] using within_refl QProb.zero (value start)
  | succ count ih =>
      have combined := within_triangle (steps start) (ih (start + 1))
      simpa only [normSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using combined

/-- A geometric bound on successive changes gives a geometric bound on
all later changes, without requiring any real-valued order decision. -/
theorem within_of_dyadic_steps (value : Nat → ConstructiveReal) (coefficient : Nat)
    (steps : ∀ n, Within (envelope coefficient n) (value n) (value (n + 1)))
    (first second : Nat) (ordered : first ≤ second) :
    Within (envelope (2 * coefficient) first) (value first) (value second) := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le ordered
  exact within_mono (within_of_step_bounds value (envelope coefficient) steps first count)
    (normSum_geometric_bound (envelope coefficient) coefficient (fun _ => QProb.le_refl _) first count)

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal RationalGeometricSeries

/-- An effective real Cauchy sequence constructed from dyadically bounded
increments. Its binary-logarithm modulus is explicit and executable. -/
def ofDyadicSteps (value : Nat → ConstructiveReal) (coefficient : Nat)
    (steps : ∀ n, Within (envelope coefficient n) (value n) (value (n + 1))) : RealCauchySequence where
  value := value
  modulus precision := (2 * coefficient * precision.den).log2 + 1
  cauchy precision n m left right := by
    by_cases ordered : n ≤ m
    · exact within_mono (within_of_dyadic_steps value coefficient steps n m ordered)
        (envelope_small coefficient precision n left)
    · exact within_symm (within_mono (within_of_dyadic_steps value coefficient steps m n (by omega))
        (envelope_small coefficient precision m right))

/-- The completed value has an error certificate at every index, rather
than only at the indices selected by the Cauchy modulus. -/
theorem ofDyadicSteps_remainder (value : Nat → ConstructiveReal) (coefficient : Nat)
    (steps : ∀ n, Within (envelope coefficient n) (value n) (value (n + 1))) (n : Nat) :
    Within (envelope (2 * coefficient) n) (value n) (ofDyadicSteps value coefficient steps).limit := by
  have limits := limit_within_of_tail (constant (value n)) (ofDyadicSteps value coefficient steps)
    (envelope (2 * coefficient) n) n (fun m later => within_of_dyadic_steps value coefficient steps n m later)
  exact (within_congr (constant_limit _) (equiv_refl _)).mp limits

end Thesis.Probability.RealCauchySequence
