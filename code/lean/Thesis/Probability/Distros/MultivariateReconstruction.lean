import Thesis.Probability.Distros.MultivariateFactorialPGF

namespace Thesis.Probability.Distros

/-- Coordinatewise rational equivalence preserves monomials, including
mismatched dimensions, without selecting reduced fraction representatives. -/
theorem multivariateMonomial_map_congr (values : List A) (f g : A → QProb) (counts : List Nat)
    (same : ∀ value ∈ values, QProb.Equiv (f value) (g value)) :
    QProb.Equiv (multivariateMonomial (values.map f) counts) (multivariateMonomial (values.map g) counts) := by
  induction values generalizing counts with
  | nil => cases counts <;> exact QProb.equiv_refl _
  | cons value values ih => cases counts with
      | nil => exact QProb.equiv_refl _
      | cons count counts =>
          exact QProb.mul_congr (qpow_congr (same value (List.mem_cons_self ..)) count)
            (ih counts (fun other member => same other (List.mem_cons_of_mem _ member)))

/-- Every positive natural argument is one plus a nonnegative offset.
This connects expansions about one to constructive PGF uniqueness. -/
theorem Distro.multivariatePGF_positive_nat_offset (μ : Distro (List Nat)) (args : List Nat)
    (positive : ∀ arg ∈ args, 0 < arg) :
    QProb.Equiv (multivariatePGF μ (args.map QProb.ofNat))
      (multivariatePGF μ ((args.map (fun arg => QProb.ofNat (arg - 1))).map
        (fun offset => QProb.add offset QProb.one))) := by
  apply μ.expectation_congr
  intro counts
  rw [List.map_map]
  apply multivariateMonomial_map_congr args QProb.ofNat (fun arg => QProb.add (QProb.ofNat (arg - 1)) QProb.one) counts
  intro arg member
  have restored : arg - 1 + 1 = arg := Nat.sub_add_cancel (by have bound := positive arg member; omega)
  simpa only [QProb.Equiv, QProb.ofNat, QProb.add, QProb.one, Nat.mul_one, Nat.one_mul] using restored.symm

/-- A finite rectangle of mixed factorial moments determines every Boolean
event of a bounded, fixed-length count vector, not merely its marginals. -/
theorem Distro.sameLaw_of_jointFactorialMoments (μ ν : Distro (List Nat)) (length bound : Nat)
    (hμ : ∀ atom ∈ μ.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count ≤ bound)
    (hν : ∀ atom ∈ ν.record.atoms, atom.1.length = length ∧ ∀ count ∈ atom.1, count ≤ bound)
    (same : ∀ orders, orders.length = length → (∀ order ∈ orders, order ≤ bound) →
      QProb.Equiv (jointFactorialMoment μ orders) (jointFactorialMoment ν orders)) :
    μ.SameLaw ν := by
  apply Distro.sameLaw_of_multivariatePGF_positive_nat μ ν length (bound + 1) (Nat.succ_pos _)
    (fun atom member => ⟨(hμ atom member).1, fun count within => Nat.lt_succ_of_le ((hμ atom member).2 count within)⟩)
    (fun atom member => ⟨(hν atom member).1, fun count within => Nat.lt_succ_of_le ((hν atom member).2 count within)⟩)
  intro args dimension positive
  let offsets := args.map (fun arg => QProb.ofNat (arg - 1))
  have offsetLength : offsets.length = length := by simpa only [offsets, List.length_map] using dimension
  have left := multivariatePGF_factorial_expansion μ offsets bound (fun atom member =>
    ⟨(hμ atom member).1.trans offsetLength.symm, (hμ atom member).2⟩)
  have right := multivariatePGF_factorial_expansion ν offsets bound (fun atom member =>
    ⟨(hν atom member).1.trans offsetLength.symm, (hν atom member).2⟩)
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

/-- All mixed factorial moments characterize a finite law of count vectors
of the supplied fixed length. Finite supports provide the common bound;
no enumeration or equality decision of an ambient sample space is needed. -/
theorem Distro.sameLaw_iff_jointFactorialMoments (μ ν : Distro (List Nat)) (length : Nat)
    (hμ : ∀ atom ∈ μ.record.atoms, atom.1.length = length)
    (hν : ∀ atom ∈ ν.record.atoms, atom.1.length = length) :
    μ.SameLaw ν ↔ ∀ orders, orders.length = length →
      QProb.Equiv (jointFactorialMoment μ orders) (jointFactorialMoment ν orders) := by
  constructor
  · exact fun law orders _ => law.jointFactorialMoment orders
  · intro same
    let bound := max (observableBound μ.record.atoms List.sum) (observableBound ν.record.atoms List.sum)
    apply Distro.sameLaw_of_jointFactorialMoments μ ν length bound
    · intro atom member
      exact ⟨hμ atom member, fun count within => Nat.le_trans (natList_mem_le_sum atom.1 count within)
        (Nat.le_trans (observableBound_mem μ.record.atoms List.sum atom member) (Nat.le_max_left _ _))⟩
    · intro atom member
      exact ⟨hν atom member, fun count within => Nat.le_trans (natList_mem_le_sum atom.1 count within)
        (Nat.le_trans (observableBound_mem ν.record.atoms List.sum atom member) (Nat.le_max_right _ _))⟩
    · exact fun orders dimension _ => same orders dimension

end Thesis.Probability.Distros
