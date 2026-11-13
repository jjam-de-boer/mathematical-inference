import Thesis.Probability.ConstructiveRealLinear
import Thesis.Probability.IntegerNullspace

namespace Thesis.Probability.ConstructiveReal.FiniteLinear
open ConstructiveReal
open Distros.RationalLinear

/-- Finite bilinear pairing of analytic vectors. It has no order tests and
uses exactly the same coordinate order as finite entropy first variations. -/
def pair (size : Nat) (first second : Fin size → ConstructiveReal) : ConstructiveReal :=
  listSum ((List.finRange size).map (fun i => mul (first i) (second i)))

private theorem sum_append (first second : List ConstructiveReal) :
    Equiv (listSum (first ++ second)) (add (listSum first) (listSum second)) := by
  induction first with
  | nil => exact equiv_symm (zero_add _)
  | cons value rest ih => exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (add_assoc _ _ _))

theorem pair_congr (size : Nat) (first first' second second' : Fin size → ConstructiveReal)
    (sameFirst : ∀ i, Equiv (first i) (first' i)) (sameSecond : ∀ i, Equiv (second i) (second' i)) :
    Equiv (pair size first second) (pair size first' second') :=
  listSum_map_congr _ _ _ (fun i _ => mul_congr (sameFirst i) (sameSecond i))

theorem pair_comm (size : Nat) (first second : Fin size → ConstructiveReal) :
    Equiv (pair size first second) (pair size second first) :=
  listSum_map_congr _ _ _ (fun _ _ => mul_comm _ _)

theorem pair_succ (size : Nat) (first second : Fin (size + 1) → ConstructiveReal) :
    Equiv (pair (size + 1) first second)
      (add (pair size (fun i => first i.castSucc) (fun i => second i.castSucc))
        (mul (first (Fin.last size)) (second (Fin.last size)))) := by
  unfold pair
  rw [List.finRange_succ_last, List.map_append]
  simp only [List.map_map, List.map_cons, List.map_nil]
  exact equiv_trans (sum_append _ _) (add_congr (equiv_refl _) (add_zero _))

private theorem sum_map_add (indices : List ι) (first second : ι → ConstructiveReal) :
    Equiv (listSum (indices.map (fun i => add (first i) (second i))))
      (add (listSum (indices.map first)) (listSum (indices.map second))) := by
  induction indices with
  | nil => exact equiv_symm (zero_add zero)
  | cons i rest ih => exact equiv_trans (add_congr (equiv_refl _) ih) (add_four _ _ _ _)

private theorem sum_map_neg (indices : List ι) (values : ι → ConstructiveReal) :
    Equiv (listSum (indices.map (fun i => neg (values i)))) (neg (listSum (indices.map values))) := by
  induction indices with
  | nil => exact ofSignedRatio_neg SignedRatio.zero
  | cons i rest ih => exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (neg_add _ _))

theorem pair_add_first (size : Nat) (first second values : Fin size → ConstructiveReal) :
    Equiv (pair size (fun i => add (first i) (second i)) values)
      (add (pair size first values) (pair size second values)) :=
  equiv_trans (listSum_map_congr _ _ _ (fun _ _ => add_mul _ _ _)) (sum_map_add _ _ _)

theorem pair_neg_first (size : Nat) (first values : Fin size → ConstructiveReal) :
    Equiv (pair size (fun i => neg (first i)) values) (neg (pair size first values)) :=
  equiv_trans (listSum_map_congr _ _ _ (fun _ _ => neg_mul _ _)) (sum_map_neg _ _)

theorem pair_sub_first (size : Nat) (first second values : Fin size → ConstructiveReal) :
    Equiv (pair size (fun i => sub (first i) (second i)) values)
      (sub (pair size first values) (pair size second values)) :=
  equiv_trans (pair_add_first size first (fun i => neg (second i)) values)
    (add_congr (equiv_refl _) (pair_neg_first size second values))

theorem pair_scale_first (size : Nat) (factor : ConstructiveReal) (first values : Fin size → ConstructiveReal) :
    Equiv (pair size (fun i => mul factor (first i)) values) (mul factor (pair size first values)) :=
  equiv_trans (listSum_map_congr _ _ _ (fun _ _ => mul_assoc _ _ _))
    (equiv_symm (by simpa only [List.map_map] using mul_listSum factor ((List.finRange size).map (fun i => mul (first i) (values i)))))

theorem pair_scale_second (size : Nat) (factor : ConstructiveReal) (first values : Fin size → ConstructiveReal) :
    Equiv (pair size first (fun i => mul factor (values i))) (mul factor (pair size first values)) :=
  equiv_trans (pair_comm _ _ _) (equiv_trans (pair_scale_first _ _ _ _) (mul_congr (equiv_refl _) (pair_comm _ _ _)))

theorem realDot_pair (size : Nat) (coefficients : Fin size → Int) (values : Fin size → ConstructiveReal) :
    Equiv (realDot size coefficients values) (pair size (fun i => realInteger (coefficients i)) values) := by
  induction size with
  | zero => exact equiv_refl zero
  | succ size ih =>
      exact equiv_trans (add_congr (equiv_refl _) (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))
        (equiv_trans (add_comm _ _) (equiv_symm (pair_succ size _ _)))

theorem pair_unit (size : Nat) (index : Fin size) (values : Fin size → ConstructiveReal) :
    Equiv (pair size (fun i => realInteger (if i = index then 1 else 0)) values) (values index) :=
  equiv_trans (equiv_symm (realDot_pair size _ values)) (realDot_unit size index values)

/-- Extension by one explicit coordinate; the state dimension is finite
and its case distinction is decidable, independently of analytic values. -/
def extend (values : Fin size → ConstructiveReal) (last : ConstructiveReal) : Fin (size + 1) → ConstructiveReal :=
  fun index => if beforeLast : index.val < size then values ⟨index.val, beforeLast⟩ else last

theorem extend_castSucc (values : Fin size → ConstructiveReal) (last : ConstructiveReal) (index : Fin size) :
    extend values last index.castSucc = values index := by
  simp only [extend, Fin.val_castSucc, dif_pos index.isLt]

theorem extend_last (values : Fin size → ConstructiveReal) (last : ConstructiveReal) :
    extend values last (Fin.last size) = last := by
  simp only [extend, Fin.val_last, dif_neg (Nat.lt_irrefl size)]

theorem pair_extend (size : Nat) (first : Fin (size + 1) → ConstructiveReal) (values : Fin size → ConstructiveReal) (last : ConstructiveReal) :
    Equiv (pair (size + 1) first (extend values last))
      (add (pair size (fun i => first i.castSucc) values) (mul (first (Fin.last size)) last)) := by
  simpa only [extend_castSucc, extend_last] using pair_succ size first (extend values last)

private def carrier : AdditiveCarrier ConstructiveReal where
  Equiv := Equiv
  equiv_refl := equiv_refl
  equiv_symm := equiv_symm
  equiv_trans := equiv_trans
  add := add
  zero := zero
  add_congr := add_congr
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero

private theorem carrier_sum (values : List ConstructiveReal) : carrier.listSum values = listSum values := by
  induction values with
  | nil => rfl
  | cons value rest ih => exact congrArg (add value) ih

def swap (values : Fin size → ConstructiveReal) (first second : Fin size) : Fin size → ConstructiveReal :=
  fun i => values (IntegerLinearAlgebra.swapIndex first second i)

theorem swap_twice (values : Fin size → ConstructiveReal) (first second : Fin size) :
    swap (swap values first second) first second = values := by
  funext i
  exact congrArg values (IntegerLinearAlgebra.swapIndex_involutive first second i)

theorem pair_swap (size : Nat) (first second : Fin size → ConstructiveReal) (a b : Fin size) :
    Equiv (pair size (swap first a b) (swap second a b)) (pair size first second) := by
  have same := carrier.finSum_reindex size (fun i => mul (first i) (second i))
    (IntegerLinearAlgebra.swapIndex a b) (IntegerLinearAlgebra.swapIndex a b)
    (IntegerLinearAlgebra.swapIndex_involutive a b) (IntegerLinearAlgebra.swapIndex_involutive a b)
  change Equiv
    (carrier.listSum ((List.finRange size).map (fun i => mul (first (IntegerLinearAlgebra.swapIndex a b i)) (second (IntegerLinearAlgebra.swapIndex a b i)))))
    (carrier.listSum ((List.finRange size).map (fun i => mul (first i) (second i)))) at same
  rw [carrier_sum, carrier_sum] at same
  exact same

theorem realDot_swap (size : Nat) (coefficients : Fin size → Int) (values : Fin size → ConstructiveReal) (a b : Fin size) :
    Equiv (realDot size (IntegerLinearAlgebra.swapVector coefficients a b) (swap values a b)) (realDot size coefficients values) :=
  equiv_trans (realDot_pair _ _ _) (equiv_trans (pair_swap size (fun i => realInteger (coefficients i)) values a b)
    (equiv_symm (realDot_pair _ _ _)))

end Thesis.Probability.ConstructiveReal.FiniteLinear
