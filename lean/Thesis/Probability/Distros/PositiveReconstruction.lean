import Thesis.Probability.Distros.PositiveFactorialPGF
import Thesis.Probability.Distros.PositivePGFUniqueness
import Thesis.Probability.Distros.MultivariateReconstruction

namespace Thesis.Probability.Distros

/-- A finite rectangle of mixed moments reconstructs the full joint law
under shape and coordinate bounds holding only almost surely. -/
theorem Distro.sameLaw_of_jointFactorialMoments_positiveSupport (μ ν : Distro (List Nat)) (length bound : Nat)
    (hμ : μ.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count ≤ bound))
    (hν : ν.AlmostSurely (fun counts => counts.length = length ∧ ∀ count ∈ counts, count ≤ bound))
    (same : ∀ orders, orders.length = length → (∀ order ∈ orders, order ≤ bound) →
      QProb.Equiv (jointFactorialMoment μ orders) (jointFactorialMoment ν orders)) :
    μ.SameLaw ν := by
  apply Distro.sameLaw_of_multivariatePGF_positive_nat_positiveSupport μ ν length (bound + 1) (Nat.succ_pos _)
    (fun atom member weight => ⟨(hμ atom member weight).1, fun count within => Nat.lt_succ_of_le ((hμ atom member weight).2 count within)⟩)
    (fun atom member weight => ⟨(hν atom member weight).1, fun count within => Nat.lt_succ_of_le ((hν atom member weight).2 count within)⟩)
  intro args dimension positive
  let offsets := args.map (fun arg => QProb.ofNat (arg - 1))
  have offsetLength : offsets.length = length := by simpa only [offsets, List.length_map] using dimension
  have left := multivariatePGF_factorial_expansion_positiveSupport μ offsets bound (fun atom member weight =>
    ⟨(hμ atom member weight).1.trans offsetLength.symm, (hμ atom member weight).2⟩)
  have right := multivariatePGF_factorial_expansion_positiveSupport ν offsets bound (fun atom member weight =>
    ⟨(hν atom member weight).1.trans offsetLength.symm, (hν atom member weight).2⟩)
  have matching := qprob_listSum_map_congr_on_mem (factorialBox offsets.length bound)
    (fun orders => QProb.mul (multivariateFactorialCoefficient μ orders) (multivariateMonomial offsets orders))
    (fun orders => QProb.mul (multivariateFactorialCoefficient ν orders) (multivariateMonomial offsets orders))
    (fun orders member => QProb.mul_congr
      (QProb.div_congr (same orders ((factorialBox_mem offsets.length bound orders member).1.trans offsetLength)
        (factorialBox_mem offsets.length bound orders member).2) (QProb.equiv_refl _) _ _)
      (QProb.equiv_refl _))
  exact QProb.equiv_trans (μ.multivariatePGF_positive_nat_offset args positive)
    (QProb.equiv_trans left (QProb.equiv_trans matching
      (QProb.equiv_trans (QProb.equiv_symm right)
        (QProb.equiv_symm (ν.multivariatePGF_positive_nat_offset args positive)))))

/-- All mixed moments characterize fixed-dimensional laws when dimension
holds only almost surely. Raw records and declared null values remain intact. -/
theorem Distro.sameLaw_iff_jointFactorialMoments_positiveSupport (μ ν : Distro (List Nat)) (length : Nat)
    (hμ : μ.AlmostSurely (fun counts => counts.length = length))
    (hν : ν.AlmostSurely (fun counts => counts.length = length)) :
    μ.SameLaw ν ↔ ∀ orders, orders.length = length →
      QProb.Equiv (jointFactorialMoment μ orders) (jointFactorialMoment ν orders) := by
  constructor
  · exact fun law orders _ => law.jointFactorialMoment orders
  · intro same
    let bound := max (observableBound μ.record.atoms List.sum) (observableBound ν.record.atoms List.sum)
    apply Distro.sameLaw_of_jointFactorialMoments_positiveSupport μ ν length bound
    · intro atom member weight
      exact ⟨hμ atom member weight, fun count within => Nat.le_trans (natList_mem_le_sum atom.1 count within)
        (Nat.le_trans (observableBound_mem μ.record.atoms List.sum atom member) (Nat.le_max_left _ _))⟩
    · intro atom member weight
      exact ⟨hν atom member weight, fun count within => Nat.le_trans (natList_mem_le_sum atom.1 count within)
        (Nat.le_trans (observableBound_mem ν.record.atoms List.sum atom member) (Nat.le_max_right _ _))⟩
    · exact fun orders dimension _ => same orders dimension

end Thesis.Probability.Distros
