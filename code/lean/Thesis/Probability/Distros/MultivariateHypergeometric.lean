import Thesis.Probability.Distros.JointFactorialMoments
import Thesis.Probability.Distros.HypergeometricUrn

namespace Thesis.Probability.Distros
open Combinatorics

/-- Multicolour sampling without replacement. Each occupancy vector has
weight equal to the product of the binomial choices from its colour stocks.
Zero colour stocks and the empty population with zero draws are included. -/
def multivariateHypergeometricAtoms (draws : Nat) : List Nat → List (List Nat × Nat)
  | [] => if draws = 0 then [([], 1)] else []
  | stock :: stocks => (List.range (draws + 1)).flatMap (fun used =>
      (multivariateHypergeometricAtoms (draws - used) stocks).map
        (fun atom => (used :: atom.1, binom stock used * atom.2)))

/-- Multivariate Vandermonde supplies the exact finite-population normalizer. -/
theorem multivariateHypergeometric_totalMass (stocks : List Nat) (draws : Nat) :
    FiniteProbRecord.totalMass (multivariateHypergeometricAtoms draws stocks) = binom stocks.sum draws := by
  induction stocks generalizing draws with
  | nil =>
      cases draws with
      | zero => rfl
      | succ draws =>
          simp only [multivariateHypergeometricAtoms, if_neg (Nat.ne_of_gt (Nat.succ_pos draws)),
            FiniteProbRecord.totalMass, List.sum_nil, binom_zero_succ]
  | cons stock stocks ih =>
      rw [multivariateHypergeometricAtoms, totalMass_range]
      have rows : natSum (draws + 1) (fun used =>
          FiniteProbRecord.totalMass ((multivariateHypergeometricAtoms (draws - used) stocks).map
            (fun atom => (used :: atom.1, binom stock used * atom.2)))) =
          natSum (draws + 1) (fun used => binom stock used * binom stocks.sum (draws - used)) := by
        apply natSum_congr
        intro used _
        rw [FiniteProbRecord.totalMass_map_weight, ih]
      rw [rows, vandermonde]
      rfl

def multivariateHypergeometricDistro (draws : Nat) (stocks : List Nat)
    (positive : 0 < binom stocks.sum draws) : Distro (List Nat) :=
  ⟨⟨multivariateHypergeometricAtoms draws stocks, binom stocks.sum draws, positive,
    multivariateHypergeometric_totalMass stocks draws⟩⟩

theorem multivariateHypergeometric_support (draws : Nat) (stocks : List Nat) (atom : List Nat × Nat)
    (member : atom ∈ multivariateHypergeometricAtoms draws stocks) :
    atom.1.length = stocks.length ∧ atom.1.sum = draws := by
  induction stocks generalizing draws atom with
  | nil =>
      by_cases zero : draws = 0
      · subst draws
        change atom ∈ [([], 1)] at member
        have same := List.mem_singleton.mp member
        cases same
        exact ⟨rfl, rfl⟩
      · rw [multivariateHypergeometricAtoms, if_neg zero] at member
        exact False.elim (List.not_mem_nil member)
  | cons stock stocks ih =>
      rcases List.mem_flatMap.mp member with ⟨used, within, rowMember⟩
      rcases List.mem_map.mp rowMember with ⟨tail, tailMember, same⟩
      cases same
      have shape := ih (draws - used) tail tailMember
      have upper := List.mem_range.mp within
      refine ⟨by simp only [List.length_cons, shape.1], ?_⟩
      simp only [List.sum_cons, shape.2]
      omega

/-- All coordinates are bounded by the sample size, even on explicitly
retained zero-weight atoms. -/
theorem multivariateHypergeometric_coordinate_bound (draws : Nat) (stocks : List Nat)
    (atom : List Nat × Nat) (member : atom ∈ multivariateHypergeometricAtoms draws stocks) (index : Nat) :
    atom.1.getD index 0 ≤ draws := by
  have shape := multivariateHypergeometric_support draws stocks atom member
  exact Nat.le_trans (list_getD_le_sum atom.1 index) (Nat.le_of_eq shape.2)

end Thesis.Probability.Distros
