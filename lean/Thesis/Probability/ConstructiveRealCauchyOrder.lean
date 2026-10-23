import Thesis.Probability.ConstructiveRealCauchy

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- Closed order passes to effective real limits. The common late index is
computed from the two moduli, with no monotonicity requirement. -/
theorem limit_le_limit (first second : RealCauchySequence)
    (compared : ∀ n, LE (first.value n) (second.value n)) : LE first.limit second.limit := by
  apply le_of_forall_rational_error
  intro precision
  let n := max (first.modulus precision.half.half.half) (second.modulus precision.half.half.half)
  have left := (first.tail_within precision.half n (Nat.le_max_left _ _)).2
  have right := (second.tail_within precision.half n (Nat.le_max_right _ _)).1
  have middle := add_le_add (compared n) (le_refl (ofSignedRatio precision.half.toSignedRatio))
  have shifted := add_le_add right (le_refl (ofSignedRatio precision.half.toSignedRatio))
  have collected : Equiv
      (ConstructiveReal.add (ConstructiveReal.add second.limit (ofSignedRatio precision.half.toSignedRatio))
        (ofSignedRatio precision.half.toSignedRatio))
      (ConstructiveReal.add second.limit (ofSignedRatio precision.toSignedRatio)) :=
    equiv_trans (add_assoc _ _ _) (add_congr (equiv_refl _)
      (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr precision.half_add_half)))
  exact (le_congr (equiv_refl _) collected).mp (le_trans left (le_trans middle shifted))

theorem limit_le (sequence : RealCauchySequence) (upper : ConstructiveReal)
    (bounded : ∀ n, LE (sequence.value n) upper) : LE sequence.limit upper :=
  (le_congr (equiv_refl _) (constant_limit upper)).mp (limit_le_limit sequence (constant upper) bounded)

theorem le_limit (sequence : RealCauchySequence) (lower : ConstructiveReal)
    (bounded : ∀ n, LE lower (sequence.value n)) : LE lower sequence.limit :=
  (le_congr (constant_limit lower) (equiv_refl _)).mp (limit_le_limit (constant lower) sequence bounded)

/-- In particular, closed interval constraints survive effective limits. -/
theorem limit_bounds (sequence : RealCauchySequence) (lower upper : ConstructiveReal)
    (bounded : ∀ n, LE lower (sequence.value n) ∧ LE (sequence.value n) upper) :
    LE lower sequence.limit ∧ LE sequence.limit upper :=
  ⟨le_limit sequence lower (fun n => (bounded n).1), limit_le sequence upper (fun n => (bounded n).2)⟩

end Thesis.Probability.RealCauchySequence
