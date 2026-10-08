import Thesis.Probability.FiniteProductBlocks

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Exact natural-power products for constructive channel coefficients

The channel construction uses a common integer scale and a common row
capacity.  One designated vertex carries a smaller power of the scale;
every other vertex of that channel carries the ordinary amplitude.  Literal
products of those amplitudes must agree with the small-channel coefficient
times the complete outer-background expansion, not merely approximate it.

These symbolic identities retain the existing terminal-coordinate product
order.  They concern natural weights only and impose no cancellation or
nonzero-cell hypothesis.  No concrete channel support is evaluated.
-/

/-- A constant natural factor occurs once at every coordinate. -/
theorem natProduct_const (n : Nat) (value : Nat) : natProduct n (fun _ => value) = value ^ n := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [natProduct, inductionHypothesis, Nat.pow_succ]
      exact Nat.mul_comm _ _

/-- An explicit anchor in a nonempty channel contributes its special
amplitude exactly once; the other coordinates contribute the ordinary one.
There is no chosen anchor or implicit existence premise in this identity. -/
theorem natProduct_one_exception (n : Nat) (ordinary special : Nat) (anchor : Fin (n + 1)) :
    natProduct (n + 1) (fun index => if index = anchor then special else ordinary) = special * ordinary ^ n := by
  induction n with
  | zero =>
      refine Fin.lastCases ?_ (fun index => Fin.elim0 index) anchor
      rfl
  | succ n inductionHypothesis =>
      refine Fin.lastCases ?_ (fun earlier => ?_) anchor
      · rw [natProduct, if_pos rfl]
        have prefixProduct := natProduct_congr (n + 1)
          (fun index => if index.castSucc = Fin.last (n + 1) then special else ordinary)
          (fun _ => ordinary) (fun index => by
            change (if index.castSucc = Fin.last (n + 1) then special else ordinary) = ordinary
            rw [if_neg (castSucc_ne_last index)])
        exact (congrArg (special * ·) prefixProduct).trans (congrArg (special * ·) (natProduct_const (n + 1) ordinary))
      · change (if Fin.last (n + 1) = earlier.castSucc then special else ordinary) *
          natProduct (n + 1) (fun index => if index.castSucc = earlier.castSucc then special else ordinary) = _
        rw [if_neg (last_ne_castSucc earlier)]
        have prefixProduct := natProduct_congr (n + 1)
          (fun index => if index.castSucc = earlier.castSucc then special else ordinary)
          (fun index => if index = earlier then special else ordinary)
          (fun index => by simp only [Fin.castSucc_inj])
        refine (congrArg (ordinary * ·) prefixProduct).trans ?_
        rw [inductionHypothesis earlier, Nat.pow_succ]
        ac_rfl

/-- A complete binary mask contributes its selected factor once per true
coordinate and its background factor once per false coordinate.  The count
is taken on the literal finite-index list, so no subset cardinal is assumed. -/
theorem natProduct_binary_mask (n : Nat) (selected background : Nat) (mask : Fin n -> Bool) :
    natProduct n (fun index => if mask index then selected else background) =
      selected ^ (List.finRange n).countP mask * background ^ (n - (List.finRange n).countP mask) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      have countBound : (List.finRange n).countP (fun index => mask index.castSucc) <= n := by
        simpa only [List.length_finRange] using List.countP_le_length (p := fun index => mask index.castSucc)
          (l := List.finRange n)
      rw [natProduct, inductionHypothesis (fun index => mask index.castSucc), List.finRange_succ_last]
      simp only [List.countP_append, List.countP_map, List.countP_cons, List.countP_nil, Function.comp_def]
      cases chosen : mask (Fin.last n) with
      | false =>
          simp only [Bool.false_eq_true, if_false, Nat.add_zero]
          rw [show n + 1 - (List.finRange n).countP (fun index => mask index.castSucc) =
            (n - (List.finRange n).countP (fun index => mask index.castSucc)) + 1 by omega, Nat.pow_succ]
          ac_rfl
      | true =>
          simp only [if_true, Nat.add_sub_add_right]
          rw [Nat.pow_succ]
          ac_rfl

end FiniteProduct
end Probability
end Thesis
