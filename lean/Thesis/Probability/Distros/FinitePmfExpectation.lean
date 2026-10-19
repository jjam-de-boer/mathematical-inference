import Thesis.Probability.Distros.MomentTableAlgebra

namespace Thesis.Probability.Distros

/-- The rational expectation of a Boolean indicator is its event probability. -/
theorem Distro.rationalExpectation_indicator (μ : Distro Ω) (event : Event Ω) :
    SignedRatio.Equiv (μ.rationalExpectation (fun x => if event x then SignedRatio.one else SignedRatio.zero))
      (μ.record.probVal event).toSignedRatio := by
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr _
    (fun x => (QProb.ofNat (if event x then 1 else 0)).toSignedRatio) ?_) ?_
  · intro x
    cases selected : event x <;> simp only [selected, Bool.false_eq_true, if_true, if_false] <;> exact SignedRatio.equiv_refl _
  · have result := μ.rationalExpectation_ofNat (fun x => if event x then 1 else 0)
    simpa only [Distro.expectNat, natIntegral_indicator, FiniteProbRecord.probVal] using result

/-- Integration against the bounded PMF, without discarding raw null outliers. -/
theorem Distro.rationalExpectation_bounded_pmf (μ : Distro Nat) (bound : Nat)
    (support : μ.AlmostSurely (fun value => value ≤ bound)) (f : Nat → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation f)
      (SignedRatio.listSum ((List.range (bound + 1)).map (fun value =>
        SignedRatio.mul (μ.pmf value).toSignedRatio (f value)))) := by
  let term := fun value x => if x = value then f value else SignedRatio.zero
  have selected : μ.AlmostSurely (fun x => SignedRatio.Equiv
      (SignedRatio.listSum ((List.range (bound + 1)).map (fun value => term value x))) (f x)) := by
    intro atom member weight
    refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.range (bound + 1)) _
      (fun value => if value = atom.1 then f atom.1 else SignedRatio.zero) ?_)
      (SignedRatio.listSum_range_select (bound + 1) atom.1 f (Nat.lt_succ_of_le (support atom member weight)))
    intro value
    by_cases same : value = atom.1
    · subst value
      simp only [term, if_true]
      exact SignedRatio.equiv_refl _
    · simp only [term, if_neg same, if_neg (Ne.symm same)]
      exact SignedRatio.equiv_refl _
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr_positive f _
    (fun atom member weight => SignedRatio.equiv_symm (selected atom member weight))) ?_
  refine SignedRatio.equiv_trans (μ.rationalExpectation_listSum (List.range (bound + 1)) term) ?_
  apply SignedRatio.listSum_map_congr
  intro value
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr (term value)
    (fun x => SignedRatio.mul (f value) (if decide (x = value) then SignedRatio.one else SignedRatio.zero)) ?_) ?_
  · intro x
    by_cases same : x = value
    · simp only [term, same, if_true, decide_true]
      exact SignedRatio.equiv_symm (SignedRatio.mul_one _)
    · simp only [term, same, if_false, decide_false, Bool.false_eq_true]
      exact SignedRatio.equiv_symm (SignedRatio.mul_zero _)
  · exact SignedRatio.equiv_trans (μ.rationalExpectation_mul_left _ _)
      (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (μ.rationalExpectation_indicator (FiniteProbRecord.singletonEvent value))) (SignedRatio.mul_comm _ _))

end Thesis.Probability.Distros
