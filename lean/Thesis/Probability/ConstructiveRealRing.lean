import Thesis.Probability.ConstructiveRealDistributivity
import Thesis.Probability.RationalMonomial

namespace Thesis.Probability.ConstructiveReal

theorem neg_unique (a b : ConstructiveReal) (canceled : Equiv (add a b) zero) : Equiv b (neg a) := by
  have shifted := add_congr (equiv_refl (neg a)) canceled
  have reducedLeft : Equiv (add (neg a) (add a b)) b :=
    equiv_trans (equiv_symm (add_assoc _ _ _))
      (equiv_trans (add_congr (equiv_trans (add_comm _ _) (add_neg a)) (equiv_refl _)) (zero_add b))
  exact equiv_trans (equiv_symm reducedLeft) (equiv_trans shifted (add_zero _))

theorem neg_add (a b : ConstructiveReal) : Equiv (neg (add a b)) (add (neg a) (neg b)) := by
  have canceled : Equiv (add (add a b) (add (neg a) (neg b))) zero :=
    equiv_trans (add_four _ _ _ _) (equiv_trans (add_congr (add_neg a) (add_neg b)) (zero_add zero))
  exact equiv_symm (neg_unique _ _ canceled)

theorem mul_neg (x y : ConstructiveReal) : Equiv (mul x (neg y)) (neg (mul x y)) := by
  have canceled : Equiv (add (mul x y) (mul x (neg y))) zero :=
    equiv_trans (equiv_symm (mul_add _ _ _))
      (equiv_trans (mul_congr (equiv_refl _) (add_neg y)) (mul_zero x))
  exact neg_unique _ _ canceled

theorem neg_mul (x y : ConstructiveReal) : Equiv (mul (neg x) y) (neg (mul x y)) :=
  equiv_trans (mul_comm _ _) (equiv_trans (mul_neg y x) (neg_congr (mul_comm _ _)))

theorem mul_sub (x y z : ConstructiveReal) : Equiv (mul x (sub y z)) (sub (mul x y) (mul x z)) :=
  equiv_trans (mul_add x y (neg z)) (add_congr (equiv_refl _) (mul_neg x z))

theorem sub_mul (x y z : ConstructiveReal) : Equiv (mul (sub x y) z) (sub (mul x z) (mul y z)) :=
  equiv_trans (add_mul x (neg y) z) (add_congr (equiv_refl _) (neg_mul y z))

theorem zero_le_sub_iff (y x : ConstructiveReal) : LE zero (sub y x) ↔ LE x y := by
  calc
    _ ↔ LE (add x (neg x)) (add y (neg x)) := (le_congr (add_neg x) (equiv_refl _)).symm
    _ ↔ _ := add_le_add_right_iff x y (neg x)

theorem sub_le_zero_iff (y x : ConstructiveReal) : LE (sub y x) zero ↔ LE y x := by
  calc
    _ ↔ LE (add y (neg x)) (add x (neg x)) := (le_congr (equiv_refl _) (add_neg x)).symm
    _ ↔ _ := add_le_add_right_iff y x (neg x)

theorem sub_equiv_zero_iff (y x : ConstructiveReal) : Equiv (sub y x) zero ↔ Equiv y x :=
  and_congr (sub_le_zero_iff y x) (zero_le_sub_iff y x)

/-- Natural powers use the constructed multiplication on real values. -/
def pow (x : ConstructiveReal) : Nat → ConstructiveReal
  | 0 => one
  | n + 1 => mul (pow x n) x

theorem pow_congr {x y : ConstructiveReal} (same : Equiv x y) (n : Nat) : Equiv (pow x n) (pow y n) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih => exact mul_congr ih same

theorem pow_add (x : ConstructiveReal) (m n : Nat) : Equiv (pow x (m + n)) (mul (pow x m) (pow x n)) := by
  induction n with
  | zero => exact equiv_symm (mul_one _)
  | succ n ih => exact equiv_trans (mul_congr ih (equiv_refl _)) (mul_assoc _ _ _)

theorem ofSignedRatio_power (value : SignedRatio) (n : Nat) :
    Equiv (pow (ofSignedRatio value) n) (ofSignedRatio (RationalMonomial.power value n)) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih =>
      exact equiv_trans (mul_congr ih (equiv_refl _))
        (equiv_trans (ofSignedRatio_mul _ _)
          ((ofSignedRatio_equiv_iff _ _).mpr (SignedRatio.mul_comm _ _)))

/-- Multiplication distributes over every finite real sum. -/
theorem mul_listSum (x : ConstructiveReal) (values : List ConstructiveReal) :
    Equiv (mul x (listSum values)) (listSum (values.map (mul x))) := by
  induction values with
  | nil => exact mul_zero x
  | cons value rest ih => exact equiv_trans (mul_add _ _ _) (add_congr (equiv_refl _) ih)

theorem listSum_mul (values : List ConstructiveReal) (x : ConstructiveReal) :
    Equiv (mul (listSum values) x) (listSum (values.map (fun value => mul value x))) :=
  equiv_trans (mul_comm _ _) (equiv_trans (mul_listSum x values)
    (listSum_map_congr values _ _ (fun value _ => mul_comm x value)))

end Thesis.Probability.ConstructiveReal
