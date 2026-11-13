import Thesis.Probability.Distros.CategoricalSampling
import Thesis.Probability.Distros.BinomialMoments
namespace Thesis.Probability.Distros
open Combinatorics

/-- Merge original coordinates according to their destination labels. -/
def aggregateCounts (groups : Nat) : List Nat → List Nat → List Nat
  | label :: labels, count :: counts =>
      (aggregateCounts groups labels counts).modify label (fun old => old + count)
  | _, _ => List.replicate groups 0

theorem aggregateCounts_length (groups : Nat) (labels counts : List Nat) :
    (aggregateCounts groups labels counts).length = groups := by
  induction labels generalizing counts with
  | nil => exact List.length_replicate
  | cons label labels ih =>
      cases counts with
      | nil => exact List.length_replicate
      | cons count counts => simp only [aggregateCounts, List.length_modify, ih]

theorem aggregateCounts_sum (groups : Nat) (labels counts : List Nat)
    (dimension : labels.length = counts.length) (within : ∀ label ∈ labels, label < groups) :
    (aggregateCounts groups labels counts).sum = counts.sum := by
  induction labels generalizing counts with
  | nil =>
      cases counts with
      | nil => simp only [aggregateCounts, List.sum_replicate_nat, Nat.mul_zero, List.sum_nil]
      | cons count counts => simp only [List.length_nil, List.length_cons] at dimension; omega
  | cons label labels ih =>
      cases counts with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons count counts =>
          rw [aggregateCounts, sum_modify_add, ih counts (Nat.succ.inj dimension)
            (fun l mem => within l (List.mem_cons_of_mem _ mem)), List.sum_cons, Nat.add_comm]
          simpa only [aggregateCounts_length] using within label (List.mem_cons_self ..)

theorem natMonomial_modify_add (args counts : List Nat) (dimension : args.length = counts.length)
    (index increment : Nat) (within : index < counts.length) :
    natMonomial args (counts.modify index (fun old => old + increment)) =
      args.getD index 0 ^ increment * natMonomial args counts := by
  induction counts generalizing args index with
  | nil => simp only [List.length_nil] at within; omega
  | cons count counts ih =>
      cases args with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons arg args =>
          have tailDimension : args.length = counts.length := Nat.succ.inj dimension
          cases index with
          | zero =>
              simp only [List.modify_zero_cons, natMonomial, List.getD_cons_zero, Nat.pow_add]
              ac_rfl
          | succ index =>
              simp only [List.modify_succ_cons, natMonomial, List.getD_cons_succ]
              rw [ih args tailDimension index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
              ac_rfl

theorem natMonomial_aggregate (groups : Nat) (labels counts args : List Nat)
    (dimension : labels.length = counts.length) (argumentDimension : args.length = groups)
    (within : ∀ label ∈ labels, label < groups) :
    natMonomial args (aggregateCounts groups labels counts) =
      natMonomial (labels.map (fun label => args.getD label 0)) counts := by
  induction labels generalizing counts with
  | nil =>
      cases counts with
      | nil => simp only [aggregateCounts]; rw [← argumentDimension, natMonomial_zeros]; rfl
      | cons count counts => simp only [List.length_nil, List.length_cons] at dimension; omega
  | cons label labels ih =>
      cases counts with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons count counts =>
          rw [aggregateCounts, natMonomial_modify_add args _
              (argumentDimension.trans (aggregateCounts_length _ _ _).symm) label count
              (by simpa only [aggregateCounts_length] using within label (List.mem_cons_self ..)),
            ih counts (Nat.succ.inj dimension) (fun l mem => within l (List.mem_cons_of_mem _ mem))]
          rfl

theorem weightedNatArgument_zeros (args : List Nat) :
    weightedNatArgument (List.replicate args.length 0) args = 0 := by
  induction args with
  | nil => rfl
  | cons arg args ih => simp only [List.length_cons, List.replicate_succ, weightedNatArgument,
      Nat.zero_mul, Nat.zero_add, ih]

theorem weightedNatArgument_modify_add (weights args : List Nat) (dimension : weights.length = args.length)
    (index increment : Nat) (within : index < weights.length) :
    weightedNatArgument (weights.modify index (fun old => old + increment)) args =
      weightedNatArgument weights args + increment * args.getD index 0 := by
  induction weights generalizing args index with
  | nil => simp only [List.length_nil] at within; omega
  | cons weight weights ih =>
      cases args with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons arg args =>
          cases index with
          | zero => simp only [List.modify_zero_cons, weightedNatArgument, List.getD_cons_zero, Nat.add_mul]; omega
          | succ index =>
              simp only [List.modify_succ_cons, weightedNatArgument, List.getD_cons_succ]
              rw [ih args (Nat.succ.inj dimension) index
                (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
              omega

theorem weightedNatArgument_aggregate (groups : Nat) (labels weights args : List Nat)
    (dimension : labels.length = weights.length) (argumentDimension : args.length = groups)
    (within : ∀ label ∈ labels, label < groups) :
    weightedNatArgument (aggregateCounts groups labels weights) args =
      weightedNatArgument weights (labels.map (fun label => args.getD label 0)) := by
  induction labels generalizing weights with
  | nil =>
      cases weights with
      | nil => simp only [aggregateCounts]; rw [← argumentDimension, weightedNatArgument_zeros]; rfl
      | cons weight weights => simp only [List.length_nil, List.length_cons] at dimension; omega
  | cons label labels ih =>
      cases weights with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons weight weights =>
          rw [aggregateCounts, weightedNatArgument_modify_add _ args
            ((aggregateCounts_length _ _ _).trans argumentDimension.symm) label weight
            (by simpa only [aggregateCounts_length] using within label (List.mem_cons_self ..)),
            ih weights (Nat.succ.inj dimension) (fun l mem => within l (List.mem_cons_of_mem _ mem))]
          simp only [List.map_cons, weightedNatArgument, Nat.add_comm]

/-- Every partition of the categories gives a multinomial law with summed weights. -/
theorem multinomial_aggregation (trials groups : Nat) (weights labels : List Nat)
    (positive : 0 < weights.sum) (dimension : labels.length = weights.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((multinomialDistro trials weights positive).map (aggregateCounts groups labels)).SameLaw
      (multinomialDistro trials (aggregateCounts groups labels weights)
        (by rw [aggregateCounts_sum groups labels weights dimension within]; exact positive)) := by
  let grouped := aggregateCounts groups labels weights
  have total : grouped.sum = weights.sum := aggregateCounts_sum groups labels weights dimension within
  apply Distro.sameLaw_of_multivariatePGF_nat _ _ groups (trials + 1) (Nat.succ_pos trials)
  · intro atom member
    rcases List.mem_map.mp member with ⟨source, hs, eq⟩
    cases eq
    have support := multinomialAtoms_support trials weights source hs
    have sum : (aggregateCounts groups labels source.1).sum = trials := by
      rw [aggregateCounts_sum groups labels source.1 (dimension.trans support.1.symm) within, support.2]
    refine ⟨aggregateCounts_length _ _ _, fun value mem => ?_⟩
    have bound := natList_mem_le_sum _ value mem
    rw [sum] at bound
    exact Nat.lt_succ_of_le bound
  · intro atom member
    have support := multinomialAtoms_support trials grouped atom member
    refine ⟨support.1.trans (aggregateCounts_length _ _ _), fun value mem => ?_⟩
    have bound := natList_mem_le_sum _ value mem
    rw [support.2] at bound
    exact Nat.lt_succ_of_le bound
  · intro args argumentDimension
    have selectedDimension : (labels.map (fun label => args.getD label 0)).length = weights.length := by
      rw [List.length_map, dimension]
    have left : QProb.Equiv
        (multivariatePGF ((multinomialDistro trials weights positive).map (aggregateCounts groups labels))
          (args.map QProb.ofNat))
        (multivariatePGF (multinomialDistro trials weights positive)
          ((labels.map (fun label => args.getD label 0)).map QProb.ofNat)) := by
      rw [multivariatePGF, Distro.expectation_map, multivariatePGF]
      apply Distro.expectation_congr_on_support
      intro atom member
      have support := multinomialAtoms_support trials weights atom member
      refine QProb.equiv_trans (multivariateMonomial_ofNat args _) ?_
      rw [natMonomial_aggregate groups labels atom.1 args (dimension.trans support.1.symm) argumentDimension within]
      exact QProb.equiv_symm (multivariateMonomial_ofNat _ _)
    refine QProb.equiv_trans left ?_
    refine QProb.equiv_trans (multinomial_multivariate_pgf_ofNat trials weights positive _ selectedDimension) ?_
    refine QProb.equiv_trans ?_ (QProb.equiv_symm
      (multinomial_multivariate_pgf_ofNat trials grouped (by rw [total]; exact positive) args
        (argumentDimension.trans (aggregateCounts_length _ _ _).symm)))
    change weightedNatArgument weights (labels.map (fun label => args.getD label 0)) ^ trials * grouped.sum ^ trials = weightedNatArgument grouped args ^ trials * weights.sum ^ trials
    rw [total, weightedNatArgument_aggregate groups labels weights args dimension argumentDimension within]

/-- The argument list that observes one coordinate of a count vector. -/
def coordinateArguments (s : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | length + 1, 0 => s :: List.replicate length 1
  | length + 1, index + 1 => 1 :: coordinateArguments s length index

theorem coordinateArguments_length (s length index : Nat) :
    (coordinateArguments s length index).length = length := by
  induction length generalizing index with
  | zero => rfl
  | succ length ih => cases index <;> simp only [coordinateArguments, List.length_cons, List.length_replicate, ih]

theorem natMonomial_ones (counts : List Nat) :
    natMonomial (List.replicate counts.length 1) counts = 1 := by
  induction counts with
  | nil => rfl
  | cons count counts ih => simp only [List.length_cons, List.replicate_succ, natMonomial,
      Nat.one_pow, Nat.one_mul, ih]

theorem natMonomial_coordinate (s : Nat) (counts : List Nat) (index : Nat) (within : index < counts.length) :
    natMonomial (coordinateArguments s counts.length index) counts = s ^ counts.getD index 0 := by
  induction counts generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons count counts ih =>
      cases index with
      | zero => simp only [coordinateArguments, natMonomial, natMonomial_ones,
          List.getD_cons_zero, Nat.mul_one]
      | succ index =>
          simp only [coordinateArguments, natMonomial, Nat.one_pow, Nat.one_mul,
            List.getD_cons_succ]
          exact ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)

theorem list_getD_le_sum (values : List Nat) (index : Nat) : values.getD index 0 ≤ values.sum := by
  induction values generalizing index with
  | nil => simp only [List.getD_nil, List.sum_nil, Nat.le_refl]
  | cons value values ih =>
      cases index with
      | zero => simp only [List.getD_cons_zero, List.sum_cons]; omega
      | succ index => simp only [List.getD_cons_succ, List.sum_cons]; have h := ih index; omega

theorem weightedNatArgument_ones (weights : List Nat) :
    weightedNatArgument weights (List.replicate weights.length 1) = weights.sum := by
  induction weights with
  | nil => rfl
  | cons weight weights ih => simp only [List.length_cons, List.replicate_succ, weightedNatArgument,
      Nat.mul_one, List.sum_cons, ih]

theorem weightedNatArgument_coordinate (s : Nat) (weights : List Nat) (index : Nat)
    (within : index < weights.length) :
    weightedNatArgument weights (coordinateArguments s weights.length index) =
      weights.getD index 0 * s + (weights.sum - weights.getD index 0) := by
  induction weights generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons weight weights ih =>
      cases index with
      | zero => simp only [coordinateArguments, weightedNatArgument,
          weightedNatArgument_ones, List.sum_cons, List.getD_cons_zero, Nat.add_sub_cancel_left]
      | succ index =>
          simp only [coordinateArguments, weightedNatArgument, Nat.mul_one,
            List.getD_cons_succ, List.sum_cons]
          rw [ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
          have bound := list_getD_le_sum weights index
          omega

def multinomialCoordinate (trials : Nat) (weights : List Nat) (positive : 0 < weights.sum) (index : Nat) :
    NatDistro (List Nat) := ⟨multinomialDistro trials weights positive, fun counts => counts.getD index 0⟩

/-- Every coordinate count has its binomial law, including weight zero. -/
theorem multinomial_coordinate_binomial (trials : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (index : Nat) (within : index < weights.length) :
    (multinomialCoordinate trials weights positive index).SameLaw
      (binomialNatDistro trials (weights.getD index 0) (weights.sum - weights.getD index 0)
        (by have h := list_getD_le_sum weights index; omega)) := by
  let a := weights.getD index 0
  let b := weights.sum - a
  have total : b + a = weights.sum := Nat.sub_add_cancel (list_getD_le_sum weights index)
  apply NatDistro.sameLaw_of_pgf_largeNat
  let s := (multinomialCoordinate trials weights positive index).distro.record.den *
    (binomialNatDistro trials a b (by omega)).distro.record.den + 1
  have left : QProb.Equiv (pgf (multinomialCoordinate trials weights positive index) (QProb.ofNat s))
      (multivariatePGF (multinomialDistro trials weights positive)
        ((coordinateArguments s weights.length index).map QProb.ofNat)) := by
    rw [pgf_expectation, multivariatePGF]
    apply Distro.expectation_congr_on_support
    intro atom member
    have support := multinomialAtoms_support trials weights atom member
    refine QProb.equiv_trans (qpow_ofNat s _) ?_
    refine QProb.equiv_trans ?_ (QProb.equiv_symm (multivariateMonomial_ofNat _ _))
    rw [← support.1, natMonomial_coordinate s atom.1 index (by omega)]
    exact QProb.equiv_refl _
  refine QProb.equiv_trans left ?_
  refine QProb.equiv_trans (multinomial_multivariate_pgf_ofNat trials weights positive _
    (coordinateArguments_length s weights.length index)) ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (binomial_pgf_ofNat trials a b s (by omega)))
  change weightedNatArgument weights (coordinateArguments s weights.length index) ^ trials * (b + a) ^ trials =
    (a * s + b) ^ trials * weights.sum ^ trials
  rw [weightedNatArgument_coordinate s weights index within, total]


theorem multinomial_coordinate_mean (trials : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (index : Nat) (within : index < weights.length) :
    QProb.Equiv (mean (multinomialCoordinate trials weights positive index))
      ⟨trials * weights.getD index 0, weights.sum, positive⟩ := by
  refine QProb.equiv_trans (multinomial_coordinate_binomial trials weights positive index within).mean ?_
  refine QProb.equiv_trans (binomial_mean_ratio trials _ _ _) ?_
  change (trials * weights.getD index 0) * weights.sum = (trials * weights.getD index 0) * ((weights.sum - weights.getD index 0) + weights.getD index 0)
  rw [Nat.sub_add_cancel (list_getD_le_sum weights index)]

theorem multinomial_coordinate_variance (trials : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (index : Nat) (within : index < weights.length) :
    QProb.Equiv (variance (multinomialCoordinate trials weights positive index))
      ⟨trials * weights.getD index 0 * (weights.sum - weights.getD index 0), weights.sum * weights.sum,
        Nat.mul_pos positive positive⟩ := by
  refine QProb.equiv_trans (multinomial_coordinate_binomial trials weights positive index within).variance ?_
  refine QProb.equiv_trans (binomial_variance trials _ _ _) ?_
  change (trials * weights.getD index 0 * (weights.sum - weights.getD index 0)) * (weights.sum * weights.sum) = (trials * weights.getD index 0 * (weights.sum - weights.getD index 0)) *
    (((weights.sum - weights.getD index 0) + weights.getD index 0) *
     ((weights.sum - weights.getD index 0) + weights.getD index 0))
  rw [Nat.sub_add_cancel (list_getD_le_sum weights index)]

end Thesis.Probability.Distros
