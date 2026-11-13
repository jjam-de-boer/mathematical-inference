import Thesis.Probability.Distros.ConditionalAlgebra
import Thesis.Probability.Distros.RationalConcentration

namespace Thesis.Probability.Distros

/-- Filtering a weighted integral equals masking its response. Null atom
occurrences remain in the original record throughout the argument. -/
theorem rationalAtomSum_filter (atoms : List (Ω × Nat)) (event : Event Ω) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum (atoms.filter (fun atom => event atom.1)) f)
      (FiniteProbRecord.rationalAtomSum atoms (fun x => if event x then f x else SignedRatio.zero)) := by
  induction atoms with
  | nil => exact SignedRatio.equiv_refl _
  | cons atom atoms ih =>
      cases selected : event atom.1 with
      | true =>
          simpa only [List.filter_cons, selected, if_true, FiniteProbRecord.rationalAtomSum,
            List.map_cons, SignedRatio.listSum] using SignedRatio.add_congr (SignedRatio.equiv_refl _) ih
      | false =>
          simp only [List.filter_cons, selected, Bool.false_eq_true, if_false,
            FiniteProbRecord.rationalAtomSum, List.map_cons, SignedRatio.listSum]
          exact SignedRatio.equiv_trans ih (SignedRatio.equiv_symm (SignedRatio.equiv_trans
            (SignedRatio.add_congr (by simp only [SignedRatio.Equiv, SignedRatio.scaleNat, SignedRatio.zero, Int.mul_zero, Int.zero_mul])
              (SignedRatio.equiv_refl _)) (SignedRatio.zero_add _)))

/-- Unnormalized integration against a label observable is preserved by
conditional expectation. This version does not require cancellation of a denominator. -/
theorem Distro.conditionalExpectation_weighted_integral (μ : Distro Ω) (key : Ω → Fin colours)
    (f : Ω → SignedRatio) (h : Fin colours → SignedRatio) :
    SignedRatio.Equiv
      (FiniteProbRecord.rationalAtomSum μ.record.atoms (fun x => SignedRatio.mul (h (key x)) (f x)))
      (FiniteProbRecord.rationalAtomSum μ.record.atoms (fun x => SignedRatio.mul (h (key x)) (μ.conditionalExpectation key f x))) := by
  refine SignedRatio.equiv_trans (rationalAtomSum_byObservable μ.record.atoms key _) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.finRange colours) _ _ (fun label => ?_))
    (SignedRatio.equiv_symm (rationalAtomSum_byObservable μ.record.atoms key _))
  let cell := μ.record.atoms.filter (fun atom => decide (key atom.1 = label))
  have factor (u : Ω → SignedRatio) :
      SignedRatio.Equiv (FiniteProbRecord.rationalAtomSum cell (fun x => SignedRatio.mul (h (key x)) (u x)))
        (SignedRatio.mul (h label) (FiniteProbRecord.rationalAtomSum cell u)) := by
    refine SignedRatio.equiv_trans (rationalAtomSum_congr_on_support cell _ _ ?_) (rationalAtomSum_mul_left cell (h label) u)
    intro atom member
    have same := of_decide_eq_true (List.mem_filter.mp member).2
    rw [same]
    exact SignedRatio.equiv_refl _
  exact SignedRatio.equiv_trans (factor f) (SignedRatio.equiv_trans
    (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (μ.conditionalExpectation_fibre_integral key f label)))
    (SignedRatio.equiv_symm (factor (μ.conditionalExpectation key f))))

/-- Tower under almost-sure refinement. The conclusion is pointwise on
all outcomes, including unsupported coarse fibres. Refinement may fail at
retained zero-weight occurrences without affecting any fibre integral. -/
theorem Distro.conditionalExpectation_tower_almostSurely (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (merge : Fin n → Fin m)
    (agrees : μ.AlmostSurely (fun x => coarse x = merge (fine x)))
    (f : Ω → SignedRatio) (x : Ω) :
    SignedRatio.Equiv (μ.conditionalExpectation coarse (μ.conditionalExpectation fine f) x)
      (μ.conditionalExpectation coarse f x) := by
  let h := fun label => if merge label = coarse x then SignedRatio.one else SignedRatio.zero
  have mask (u : Ω → SignedRatio) : SignedRatio.Equiv
      (FiniteProbRecord.rationalAtomSum (μ.record.atoms.filter (fun atom => decide (coarse atom.1 = coarse x))) u)
      (FiniteProbRecord.rationalAtomSum μ.record.atoms (fun y => SignedRatio.mul (h (fine y)) (u y))) := by
    refine SignedRatio.equiv_trans (rationalAtomSum_filter μ.record.atoms (fun y => decide (coarse y = coarse x)) u) ?_
    apply rationalAtomSum_congr_positive
    intro atom member weight
    rw [agrees atom member weight]
    by_cases same : merge (fine atom.1) = coarse x
    · simp only [h, same, decide_true, if_true]
      exact SignedRatio.equiv_symm (SignedRatio.one_mul _)
    · simp only [h, same, decide_false, Bool.false_eq_true, if_false]
      exact SignedRatio.equiv_symm (SignedRatio.zero_mul _)
  apply conditionalBlockMean_congr_integral
  exact SignedRatio.equiv_trans (mask (μ.conditionalExpectation fine f))
    (SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.conditionalExpectation_weighted_integral fine f h))
      (SignedRatio.equiv_symm (mask f)))

end Thesis.Probability.Distros
