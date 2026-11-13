import Thesis.Probability.Distros.PGFUniqueness
import Thesis.Probability.Distros.Categorical
import Thesis.Probability.Distros.PointMass

/-! Independent categorical words and their exact multinomial occupancy law. -/

namespace Thesis.Probability.Distros
open Combinatorics

theorem natSum_getD (weights : List Nat) :
    natSum weights.length (fun i => weights.getD i 0) = weights.sum := by
  induction weights with
  | nil => rfl
  | cons weight weights ih =>
      rw [List.length_cons, natSum_head]
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.sum_cons, ih]

theorem finWeight_getD_sum (weights : List Nat) :
    natSum weights.length (finWeight (fun i : Fin weights.length => weights.getD i.val 0)) = weights.sum := by
  have terms : natSum weights.length (finWeight (fun i : Fin weights.length => weights.getD i.val 0)) =
      natSum weights.length (fun i => weights.getD i 0) := by
    apply natSum_congr
    intro i hi
    simp only [finWeight, dif_pos hi]
  rw [terms, natSum_getD]

def listCategoricalDistro (weights : List Nat) (positive : 0 < weights.sum) : Distro (Fin weights.length) :=
  categoricalDistro weights.length (fun i => weights.getD i.val 0) (by
    rw [finWeight_getD_sum]
    exact positive)

/-- Independent categorical draws, retaining the ordered word. -/
def categoricalWordDistro (weights : List Nat) (positive : 0 < weights.sum) : Nat → Distro (List Nat)
  | 0 => Distro.pointMass []
  | n + 1 => ((listCategoricalDistro weights positive).product (categoricalWordDistro weights positive n)).map
      (fun pair => pair.1.val :: pair.2)

def colourCounts (length : Nat) : List Nat → List Nat
  | [] => List.replicate length 0
  | head :: tail => (colourCounts length tail).modify head (fun count => count + 1)

theorem colourCounts_length (length : Nat) (word : List Nat) : (colourCounts length word).length = length := by
  induction word with
  | nil => exact List.length_replicate
  | cons head tail ih => simp only [colourCounts, List.length_modify, ih]

theorem sum_modify_succ (counts : List Nat) (index : Nat) (within : index < counts.length) :
    (counts.modify index (fun count => count + 1)).sum = counts.sum + 1 := by
  induction counts generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons count counts ih =>
      cases index with
      | zero => simp only [List.modify_zero_cons, List.sum_cons]; omega
      | succ index =>
          simp only [List.modify_succ_cons, List.sum_cons]
          rw [ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
          omega

theorem natMonomial_modify_succ (args counts : List Nat) (dimension : args.length = counts.length)
    (index : Nat) (within : index < counts.length) :
    natMonomial args (counts.modify index (fun count => count + 1)) =
      args.getD index 0 * natMonomial args counts := by
  induction counts generalizing args index with
  | nil => simp only [List.length_nil] at within; omega
  | cons count counts ih =>
      cases args with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons arg args =>
          have tailDimension : args.length = counts.length := by
            simpa only [List.length_cons, Nat.add_left_inj] using dimension
          cases index with
          | zero =>
              simp only [List.modify_zero_cons, natMonomial, List.getD_cons_zero, Nat.pow_succ]
              ac_rfl
          | succ index =>
              simp only [List.modify_succ_cons, natMonomial, List.getD_cons_succ]
              rw [ih args tailDimension index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
              ac_rfl

theorem natMonomial_zeros (args : List Nat) : natMonomial args (List.replicate args.length 0) = 1 := by
  induction args with
  | nil => rfl
  | cons arg args ih => simp only [List.length_cons, List.replicate_succ, natMonomial, Nat.pow_zero, Nat.one_mul, ih]

theorem categoricalWord_counts_support (weights : List Nat) (positive : 0 < weights.sum) (n : Nat)
    (atom : List Nat × Nat) (member : atom ∈ (categoricalWordDistro weights positive n).record.atoms) :
    (colourCounts weights.length atom.1).sum = n := by
  induction n generalizing atom with
  | zero =>
      simp only [categoricalWordDistro, Distro.pointMass, List.mem_singleton] at member
      cases member
      simp only [colourCounts, List.sum_replicate_nat, Nat.mul_zero]
  | succ n ih =>
      change atom ∈ ((FiniteProbRecord.weightedCartesian
        (listCategoricalDistro weights positive).record.atoms
        (categoricalWordDistro weights positive n).record.atoms).map
          (fun source => (source.1.1.val :: source.1.2, source.2))) at member
      rcases List.mem_map.mp member with ⟨source, hs, eq⟩
      rcases List.mem_flatMap.mp hs with ⟨head, _, tail⟩
      rcases List.mem_map.mp tail with ⟨rest, hr, he⟩
      cases eq
      cases he
      rw [colourCounts, sum_modify_succ, ih rest hr]
      simpa only [colourCounts_length] using head.1.isLt

def categoricalOccupancyDistro (n : Nat) (weights : List Nat) (positive : 0 < weights.sum) : Distro (List Nat) :=
  (categoricalWordDistro weights positive n).map (colourCounts weights.length)

theorem categoricalOccupancy_support (n : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (atom : List Nat × Nat) (member : atom ∈ (categoricalOccupancyDistro n weights positive).record.atoms) :
    atom.1.length = weights.length ∧ atom.1.sum = n := by
  rcases List.mem_map.mp member with ⟨source, hs, eq⟩
  cases eq
  exact ⟨colourCounts_length _ _, categoricalWord_counts_support weights positive n source hs⟩

theorem weightedNatArgument_sum (weights args : List Nat) (dimension : args.length = weights.length) :
    natSum weights.length (fun i => weights.getD i 0 * args.getD i 0) = weightedNatArgument weights args := by
  induction weights generalizing args with
  | nil => cases args <;> rfl
  | cons weight weights ih =>
      cases args with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons arg args =>
          rw [List.length_cons, natSum_head]
          simp only [List.getD_cons_zero, List.getD_cons_succ, weightedNatArgument]
          rw [ih args (by simpa only [List.length_cons, Nat.add_left_inj] using dimension)]

theorem listCategorical_expectNat (weights args : List Nat) (positive : 0 < weights.sum)
    (dimension : args.length = weights.length) :
    QProb.Equiv ((listCategoricalDistro weights positive).expectNat (fun i : Fin weights.length => args.getD i.val 0))
      ⟨weightedNatArgument weights args, weights.sum, positive⟩ := by
  change natIntegral (finWeighted weights.length (fun i => weights.getD i.val 0))
      (fun i : Fin weights.length => args.getD i.val 0) * weights.sum =
    weightedNatArgument weights args * FiniteProbRecord.totalMass
      (finWeighted weights.length (fun i => weights.getD i.val 0))
  rw [natIntegral_finWeighted weights.length (fun i => weights.getD i.val 0) (fun i => args.getD i 0),
    totalMass_finWeighted, finWeight_getD_sum]
  have terms : natSum weights.length (fun i =>
        finWeight (fun i : Fin weights.length => weights.getD i.val 0) i * args.getD i 0) =
      natSum weights.length (fun i => weights.getD i 0 * args.getD i 0) := by
    apply natSum_congr
    intro i hi
    simp only [finWeight, dif_pos hi]
  rw [terms, weightedNatArgument_sum weights args dimension]

theorem listCategorical_den (weights : List Nat) (positive : 0 < weights.sum) :
    (listCategoricalDistro weights positive).record.den = weights.sum := by
  change FiniteProbRecord.totalMass (finWeighted weights.length (fun i => weights.getD i.val 0)) = _
  rw [totalMass_finWeighted, finWeight_getD_sum]

theorem categoricalWord_den (weights : List Nat) (positive : 0 < weights.sum) (n : Nat) :
    (categoricalWordDistro weights positive n).record.den = weights.sum ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (listCategoricalDistro weights positive).record.den *
        (categoricalWordDistro weights positive n).record.den = weights.sum ^ (n + 1)
      rw [listCategorical_den, ih, Nat.pow_succ]
      ac_rfl

theorem categoricalWord_monomial (weights args : List Nat) (positive : 0 < weights.sum)
    (dimension : args.length = weights.length) (n : Nat) :
    QProb.Equiv ((categoricalWordDistro weights positive n).expectNat
      (fun word => natMonomial args (colourCounts weights.length word)))
      (qpow ⟨weightedNatArgument weights args, weights.sum, positive⟩ n) := by
  induction n with
  | zero =>
      simp only [categoricalWordDistro, Distro.expectNat, Distro.pointMass, natIntegral,
        colourCounts, Nat.one_mul, Nat.add_zero, qpow, QProb.Equiv, QProb.one, Nat.mul_one]
      rw [← dimension, natMonomial_zeros]
  | succ n ih =>
      change QProb.Equiv
        ((((listCategoricalDistro weights positive).product (categoricalWordDistro weights positive n)).map
          (fun pair => pair.1.val :: pair.2)).expectNat
            (fun word => natMonomial args (colourCounts weights.length word))) _
      rw [Distro.expectNat_map]
      have functions : (fun pair : Fin weights.length × List Nat =>
          natMonomial args (colourCounts weights.length (pair.1.val :: pair.2))) =
        (fun pair => args.getD pair.1.val 0 * natMonomial args (colourCounts weights.length pair.2)) := by
        funext pair
        exact natMonomial_modify_succ args _
          (dimension.trans (colourCounts_length _ _).symm) pair.1.val
          (by simpa only [colourCounts_length] using pair.1.isLt)
      rw [functions]
      exact QProb.equiv_trans
        (Distro.expectNat_product _ _ (fun i : Fin weights.length => args.getD i.val 0)
          (fun word => natMonomial args (colourCounts weights.length word)))
        (QProb.mul_congr (listCategorical_expectNat weights args positive dimension) ih)

theorem categoricalOccupancy_pgf_ofNat (n : Nat) (weights args : List Nat) (positive : 0 < weights.sum)
    (dimension : args.length = weights.length) :
    QProb.Equiv (multivariatePGF (categoricalOccupancyDistro n weights positive) (args.map QProb.ofNat))
      ⟨weightedNatArgument weights args ^ n, weights.sum ^ n, Nat.pow_pos positive⟩ := by
  rw [multivariatePGF, categoricalOccupancyDistro, Distro.expectation_map]
  refine QProb.equiv_trans
    ((categoricalWordDistro weights positive n).expectation_congr _ _
      (fun word => multivariateMonomial_ofNat args (colourCounts weights.length word))) ?_
  refine QProb.equiv_trans ((categoricalWordDistro weights positive n).expectation_nat _) ?_
  refine QProb.equiv_trans (categoricalWord_monomial weights args positive dimension n) ?_
  simp only [QProb.Equiv, qpow_num, qpow_den]

theorem natList_mem_le_sum (values : List Nat) (value : Nat) (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with eq | member
      · subst value
        simp only [List.sum_cons]
        omega
      · have h := ih member
        simp only [List.sum_cons]
        omega

/-- Independent draws from the existing categorical constructor, read off
by their occupancy vector, agree with multinomial on every Boolean event. -/
theorem multinomial_categorical_correspondence (n : Nat) (weights : List Nat) (positive : 0 < weights.sum) :
    (categoricalOccupancyDistro n weights positive).SameLaw (multinomialDistro n weights positive) := by
  apply Distro.sameLaw_of_multivariatePGF_nat _ _ weights.length (n + 1) (Nat.succ_pos n)
  · intro atom member
    have support := categoricalOccupancy_support n weights positive atom member
    refine ⟨support.1, fun value mem => ?_⟩
    have bound := natList_mem_le_sum atom.1 value mem
    rw [support.2] at bound
    exact Nat.lt_succ_of_le bound
  · intro atom member
    have support := multinomialAtoms_support n weights atom member
    refine ⟨support.1, fun value mem => ?_⟩
    have bound := natList_mem_le_sum atom.1 value mem
    rw [support.2] at bound
    exact Nat.lt_succ_of_le bound
  · intro args dimension
    exact QProb.equiv_trans (categoricalOccupancy_pgf_ofNat n weights args positive dimension)
      (QProb.equiv_symm (multinomial_multivariate_pgf_ofNat n weights positive args dimension))

theorem getD_modify_add (values : List Nat) (index query increment : Nat) (within : query < values.length) :
    (values.modify index (fun old => old + increment)).getD query 0 =
      values.getD query 0 + if index = query then increment else 0 := by
  induction values generalizing index query with
  | nil => simp only [List.length_nil] at within; omega
  | cons value values ih =>
      cases index <;> cases query
      · simp only [List.modify_zero_cons, List.getD_cons_zero, if_true]
      · simp only [List.modify_zero_cons, List.getD_cons_succ, Nat.zero_ne_add_one, if_false, Nat.add_zero]
      · simp only [List.modify_succ_cons, List.getD_cons_zero, Nat.add_one_ne_zero, if_false, Nat.add_zero]
      · simp only [List.modify_succ_cons, List.getD_cons_succ, Nat.add_left_inj]
        exact ih _ _ (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)

end Thesis.Probability.Distros
