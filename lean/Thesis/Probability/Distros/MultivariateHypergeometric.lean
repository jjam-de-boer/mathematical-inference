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
  | nil => cases draws <;> simp only [multivariateHypergeometricAtoms, List.sum_nil,
      if_pos rfl, FiniteProbRecord.totalMass, Nat.add_zero, binom_zero_right,
      Nat.zero_ne_add_one, if_false, binom_zero_succ]
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
      · simp only [multivariateHypergeometricAtoms, zero, if_pos rfl, List.mem_singleton] at member
        cases member
        exact ⟨rfl, zero.symm⟩
      · simp only [multivariateHypergeometricAtoms, if_neg zero, List.not_mem_nil] at member
  | cons stock stocks ih =>
      rcases List.mem_flatMap.mp member with ⟨used, within, member⟩
      rcases List.mem_map.mp member with ⟨tail, member, same⟩
      cases same
      have shape := ih (draws - used) tail member
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
  exact (list_getD_le_sum atom.1 index).trans (Nat.le_of_eq shape.2)

end Thesis.Probability.Distros
