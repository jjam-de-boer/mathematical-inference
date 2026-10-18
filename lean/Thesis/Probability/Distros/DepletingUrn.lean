import Thesis.Probability.Distros.HypergeometricFactorialMoments
import Thesis.Probability.Distros.ReinforcedUpdates

namespace Thesis.Probability.Distros
open Combinatorics

/-- A categorical draw removes one ball of its selected colour. Zero-weight
branches are retained as zero-weight occurrences, just as in other finite records. -/
def multicolourDepletingAtoms : Nat → List Nat → List (List Nat × Nat)
  | 0, _ => [([], 1)]
  | n + 1, stocks => (finWeighted stocks.length (fun i => stocks.getD i.val 0)).flatMap fun head =>
      (multicolourDepletingAtoms n (stocks.modify head.1.val (fun stock => stock - 1))).map
        (fun rest => (head.1.val :: rest.1, head.2 * rest.2))

theorem jointFalling_zeroOrders (stocks : List Nat) :
    jointFalling (List.replicate stocks.length 0) stocks = 1 := by
  induction stocks with
  | nil => rfl
  | cons stock stocks ih =>
      simp only [List.length_cons, List.replicate_succ, jointFalling, fallingFactorial, Nat.one_mul, ih]

/-- Absorb the next draw into the selected coordinate's falling factorial. -/
theorem jointFalling_increment (stocks counts : List Nat) (dimension : stocks.length = counts.length)
    (index : Nat) (within : index < stocks.length) :
    jointFalling (counts.modify index (fun count => count + 1)) stocks =
      stocks.getD index 0 * jointFalling counts (stocks.modify index (fun stock => stock - 1)) := by
  induction stocks generalizing counts index with
  | nil => simp only [List.length_nil] at within; exact False.elim (by omega)
  | cons stock stocks ih => cases counts with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; exact False.elim (by omega)
      | cons count counts => cases index with
          | zero => simp only [List.modify_zero_cons, List.getD_cons_zero, jointFalling, fallingFactorial]; ac_rfl
          | succ index =>
              simp only [List.modify_succ_cons, List.getD_cons_succ, jointFalling]
              rw [ih counts (Nat.succ.inj dimension) index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
              ac_rfl

/-- The weight of each actual ordered colour word is the product of its
colour-stock falling factors. No stock positivity is assumed in this raw identity. -/
theorem multicolourDepletingAtoms_word_weights (n : Nat) (stocks : List Nat) :
    multicolourDepletingAtoms n stocks = (unitWordAtoms stocks.length n).map
      (fun atom => (atom.1, atom.2 * jointFalling (colourCounts stocks.length atom.1) stocks)) := by
  induction n generalizing stocks with
  | zero => simp only [multicolourDepletingAtoms, unitWordAtoms, List.map_cons, List.map_nil,
      colourCounts, jointFalling_zeroOrders, Nat.mul_one]
  | succ n ih =>
      rw [multicolourDepletingAtoms, finWeighted_reweight, List.flatMap_map]
      simp only [unitWordAtoms, List.map_flatMap]
      apply congrArg (fun f => (finWeighted stocks.length (fun _ => 1)).flatMap f)
      funext head
      rw [ih, List.length_modify]
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro rest _
      simp only [colourCounts]
      rw [jointFalling_increment stocks _ (colourCounts_length _ _).symm head.1.val head.1.isLt]
      ac_rfl

/-- The sequential denominator is the number of ordered labelled samples. -/
theorem multicolourDepletingAtoms_totalMass (n : Nat) (stocks : List Nat) :
    FiniteProbRecord.totalMass (multicolourDepletingAtoms n stocks) = fallingFactorial stocks.sum n := by
  cases stocks with
  | nil => cases n with
      | zero => rfl
      | succ n => simp only [multicolourDepletingAtoms, List.length_nil, finWeighted, List.flatMap_nil,
          FiniteProbRecord.totalMass, List.sum_nil, fallingFactorial, Nat.zero_mul]
  | cons stock stocks =>
      rw [multicolourDepletingAtoms_word_weights,
        totalMass_reweight (unitWordAtoms (stock :: stocks).length n)
          (fun word => jointFalling (colourCounts (stock :: stocks).length word) (stock :: stocks)),
        ← unitOccupancy_integral n (stock :: stocks).length
          (fun counts => jointFalling counts (stock :: stocks)) (by simp only [List.length_cons]; omega),
        ← totalMass_reweight (multinomialAtoms n (List.replicate (stock :: stocks).length 1))
          (fun counts => jointFalling counts (stock :: stocks))]
      exact multicolourDepletingCount_totalMass n (stock :: stocks)

theorem binom_pos_of_le (total draws : Nat) (within : draws ≤ total) : 0 < binom total draws := by
  have positive := fallingFactorial_pos total draws within
  rw [fallingFactorial_binom] at positive
  exact Nat.pos_of_mul_pos_left positive

/-- Actual ordered draws without replacement, including empty population
and zero draws. The horizon cannot exceed the finite population. -/
def multicolourDepletingDistro (n : Nat) (stocks : List Nat) (within : n ≤ stocks.sum) : Distro (List Nat) :=
  ofWeightedAtoms (multicolourDepletingAtoms n stocks) (by
    rw [multicolourDepletingAtoms_totalMass]; exact fallingFactorial_pos _ _ within)

theorem multicolourDepleting_den (n : Nat) (stocks : List Nat) (within : n ≤ stocks.sum) :
    (multicolourDepletingDistro n stocks within).record.den = fallingFactorial stocks.sum n :=
  multicolourDepletingAtoms_totalMass n stocks

theorem multicolourDepletingAtoms_support (n : Nat) (stocks : List Nat) (atom : List Nat × Nat)
    (member : atom ∈ multicolourDepletingAtoms n stocks) :
    atom.1.length = n ∧ ∀ colour ∈ atom.1, colour < stocks.length := by
  induction n generalizing stocks atom with
  | zero =>
      simp only [multicolourDepletingAtoms, List.mem_singleton] at member
      cases member
      exact ⟨rfl, fun _ member => nomatch member⟩
  | succ n ih =>
      rcases List.mem_flatMap.mp member with ⟨head, _, tail⟩
      rcases List.mem_map.mp tail with ⟨rest, hr, same⟩
      cases same
      have support := ih (stocks.modify head.1.val (fun stock => stock - 1)) rest hr
      simp only [List.length_modify] at support
      refine ⟨by simp only [List.length_cons, support.1], fun colour member => ?_⟩
      rcases List.mem_cons.mp member with same | member
      · subst colour; exact head.1.isLt
      · exact support.2 colour member

/-- The occupancy pushforward of actual sequential removal has the ordered
multiplicity count law already used for hypergeometric factorial moments. -/
theorem multicolourDepleting_count_multiplicity (n : Nat) (stocks : List Nat) (within : n ≤ stocks.sum) :
    ((multicolourDepletingDistro n stocks within).map (colourCounts stocks.length)).SameLaw
      (multicolourDepletingCountDistro n stocks (binom_pos_of_le _ _ within)) := by
  cases stocks with
  | nil =>
      have zero : n = 0 := by simp only [List.sum_nil] at within; omega
      subst n
      intro event
      exact QProb.equiv_refl _
  | cons stock stocks =>
      intro event
      change FiniteProbRecord.eventMass
          ((multicolourDepletingAtoms n (stock :: stocks)).map (fun atom => (colourCounts (stock :: stocks).length atom.1, atom.2))) event *
          fallingFactorial (stock :: stocks).sum n =
        FiniteProbRecord.eventMass (multicolourDepletingCountAtoms n (stock :: stocks)) event *
          (multicolourDepletingDistro n (stock :: stocks) within).record.den
      rw [multicolourDepleting_den, FiniteProbRecord.eventMass_map_labels, multicolourDepletingAtoms_word_weights,
        multicolourDepletingCountAtoms,
        eventMass_reweight (unitWordAtoms (stock :: stocks).length n)
          (fun word => jointFalling (colourCounts (stock :: stocks).length word) (stock :: stocks))
          (fun word => event (colourCounts (stock :: stocks).length word)),
        eventMass_reweight (multinomialAtoms n (List.replicate (stock :: stocks).length 1))
          (fun counts => jointFalling counts (stock :: stocks)) event,
        unitOccupancy_integral n (stock :: stocks).length
          (fun counts => if event counts then jointFalling counts (stock :: stocks) else 0)
          (by simp only [List.length_cons]; omega)]

/-- Sampling without replacement gives the complete multivariate
hypergeometric count law on every Boolean event. -/
theorem multicolourDepleting_hypergeometric (n : Nat) (stocks : List Nat) (within : n ≤ stocks.sum) :
    ((multicolourDepletingDistro n stocks within).map (colourCounts stocks.length)).SameLaw
      (multivariateHypergeometricDistro n stocks (binom_pos_of_le _ _ within)) :=
  (multicolourDepleting_count_multiplicity n stocks within).trans
    (multicolourDepletingCount_sameLaw n stocks (binom_pos_of_le _ _ within))

end Thesis.Probability.Distros
