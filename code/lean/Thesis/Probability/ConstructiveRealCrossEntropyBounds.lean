import Thesis.Probability.ConstructiveRealGibbsInequality
import Thesis.Probability.ConstructiveRealLogInverse

namespace Thesis.Probability.ConstructiveReal

/-- A deliberately coarse entropy bound, computed from the declared finite
state count. It is used for positivity, not as a sharp inference certificate. -/
def entropySizeBound (variables : Nat) : ConstructiveReal :=
  listSum ((List.finRange variables).map (fun _ => ofSignedRatio (⟨3, 1, by decide⟩ : SignedRatio)))

theorem UnitIntervalValue.entropy_le_three (observed : UnitIntervalValue) :
    LE observed.entropy (ofSignedRatio (⟨3, 1, by decide⟩ : SignedRatio)) := by
  let reference : UnitIntervalValue := ⟨one, (ofSignedRatio_le_iff _ _).mpr (by decide +kernel), le_refl one⟩
  have supported := observed.entropy_cross_supporting reference PositiveRatio.one (le_refl one)
  have simplified : Equiv (add (neg (mul observed.value (one.positiveLog2 PositiveRatio.one (le_refl one))))
      (mul RationalLogSecant.limit (sub one observed.value)))
      (mul RationalLogSecant.limit (sub one observed.value)) :=
    equiv_trans (add_congr (equiv_trans (neg_congr (equiv_trans
      (mul_congr (equiv_refl _) (positiveLog2_one _ _)) (mul_zero _)))
      (ofSignedRatio_neg SignedRatio.zero)) (equiv_refl _)) (zero_add _)
  have displacement : LE (sub one observed.value) one :=
    (le_congr (equiv_refl _) (add_zero one)).mp
      (add_le_add (le_refl one) ((le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp
        ((neg_le_neg_iff zero observed.value).mpr observed.nonnegative)))
  have coefficientPositive : LE zero RationalLogSecant.limit := le_trans
    ((ofSignedRatio_le_iff _ _).mpr (by decide +kernel)) RationalLogSecant.one_le_limit
  exact le_trans ((le_congr (equiv_refl _) simplified).mp supported)
    (le_trans ((le_congr (equiv_refl _) (mul_one _)).mp
      (mul_le_mul_nonnegative coefficientPositive displacement)) RationalLogSecant.limit_le_three)

theorem realEntropySum_le_sizeBound (masses : Fin variables → UnitIntervalValue) :
    LE (realEntropySum ((List.finRange variables).map masses)) (entropySizeBound variables) := by
  simpa only [realEntropySum, List.map_map, entropySizeBound] using
    listSum_map_mono (List.finRange variables) (fun i => (masses i).entropy)
      (fun _ => ofSignedRatio (⟨3, 1, by decide⟩ : SignedRatio)) (fun i _ => (masses i).entropy_le_three)

/-- A single negative-log contribution is bounded by cross entropy divided
by a supplied positive observed mass floor. The reference floor is only a
domain witness for its logarithm; it does not enter the resulting bound. -/
theorem negativeLog_le_crossEntropy (observed reference : Fin variables → UnitIntervalValue)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value)
    (index : Fin variables) (observedLower : PositiveRatio)
    (observedPositive : LE (ofSignedRatio observedLower.toSignedRatio) (observed index).value)
    (upper : ConstructiveReal) (bounded : LE (realCrossEntropySum observed reference lower positive) upper) :
    LE (neg ((reference index).value.positiveLog2 (lower index) (positive index)))
      (mul ((ofSignedRatio observedLower.toSignedRatio).positiveInverse observedLower (le_refl _)) upper) := by
  let negativeLog := fun i => neg ((reference i).value.positiveLog2 (lower i) (positive i))
  have logPositive (i : Fin variables) : LE zero (negativeLog i) :=
    (le_congr (equiv_symm (ofSignedRatio_neg SignedRatio.zero)) (equiv_refl (negativeLog i))).mp
      ((neg_le_neg_iff ((reference i).value.positiveLog2 (lower i) (positive i)) zero).mpr
        (positiveLog2_nonpositive (reference i).value (lower i) (positive i) (reference i).bounded))
  have termPositive (i : Fin variables) : LE zero (neg (mul (observed i).value ((reference i).value.positiveLog2 (lower i) (positive i)))) :=
    (le_congr (equiv_refl _) (mul_neg _ _)).mp (mul_nonnegative (observed i).nonnegative (logPositive i))
  have termBound := le_listSum_of_mem
    ((List.finRange variables).map (fun i => neg (mul (observed i).value ((reference i).value.positiveLog2 (lower i) (positive i)))))
    (by intro term member; obtain ⟨i, _, rfl⟩ := List.mem_map.mp member; exact termPositive i)
    _ (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)
  have scaled : LE (mul (ofSignedRatio observedLower.toSignedRatio) (negativeLog index)) upper :=
    le_trans (mul_le_mul_nonnegative_right (logPositive index) observedPositive)
      (le_trans ((le_congr (mul_neg _ _) (equiv_refl _)).mpr termBound) bounded)
  let inverse := (ofSignedRatio observedLower.toSignedRatio).positiveInverse observedLower (le_refl _)
  have cancel : Equiv (mul inverse (mul (ofSignedRatio observedLower.toSignedRatio) (negativeLog index))) (negativeLog index) :=
    equiv_trans (equiv_symm (mul_assoc _ _ _))
      (equiv_trans (mul_congr (equiv_trans (mul_comm _ _)
        ((ofSignedRatio observedLower.toSignedRatio).mul_positiveInverse observedLower (le_refl _))) (equiv_refl _)) (one_mul _))
  exact (le_congr cancel (equiv_refl _)).mp (mul_le_mul_nonnegative
    ((ofSignedRatio observedLower.toSignedRatio).positiveInverse_nonnegative observedLower (le_refl _)) scaled)

/-- A computed floor depending only on the cross-entropy bound and a positive
observed mass. It is independent of any temporary reference-domain floor. -/
def crossEntropyFloor (upper : ConstructiveReal) (observedLower : PositiveRatio) : PositiveRatio :=
  (neg (mul (mul ((ofSignedRatio observedLower.toSignedRatio).positiveInverse observedLower (le_refl _)) upper) lnTwo)).expLower

/-- Bounded cross entropy against an observed positive law prevents every
reference coordinate from tending to zero. This quantitative form makes the
later interior-optimizer argument constructive. -/
theorem crossEntropyFloor_le (observed reference : Fin variables → UnitIntervalValue)
    (lower : Fin variables → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (reference i).value)
    (index : Fin variables) (observedLower : PositiveRatio)
    (observedPositive : LE (ofSignedRatio observedLower.toSignedRatio) (observed index).value)
    (upper : ConstructiveReal) (bounded : LE (realCrossEntropySum observed reference lower positive) upper) :
    LE (ofSignedRatio (crossEntropyFloor upper observedLower).toSignedRatio) (reference index).value := by
  let logarithm := (reference index).value.positiveLog2 (lower index) (positive index)
  let bound := mul ((ofSignedRatio observedLower.toSignedRatio).positiveInverse observedLower (le_refl _)) upper
  have reversed : LE (neg bound) logarithm :=
    (le_congr (equiv_refl _) (neg_neg logarithm)).mp ((neg_le_neg_iff _ _).mpr
      (negativeLog_le_crossEntropy observed reference lower positive index observedLower observedPositive upper bounded))
  have factorPositive : LE zero lnTwo := le_trans
    ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr
      RationalLogSecant.limit.positiveInverseLower.signed_nonnegative)) lnTwo_lower
  have natural : LE (neg (mul bound lnTwo)) ((reference index).value.positiveLn (lower index) (positive index)) :=
    (le_congr (neg_mul _ _) (equiv_refl _)).mp (mul_le_mul_nonnegative_right factorPositive reversed)
  exact le_trans (exp_lower (neg (mul bound lnTwo)))
    ((le_congr (equiv_refl _) (exp_positiveLn _ _ _)).mp ((exp_le_exp_iff _ _).mpr natural))

end Thesis.Probability.ConstructiveReal
