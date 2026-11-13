import Thesis.Probability.Distros.FactorialRectangle
import Thesis.Probability.Distros.MomentTableAlgebra

namespace Thesis.Probability.Distros
open Combinatorics

/-- Reverse tensor inversion recovers the supplied mixed binomial moments
from signed candidate masses, before any realization is assumed. -/
theorem jointInverseBinomial_reverse_rectangle_kernel (counts target bounds : List Nat)
    (dimension : target.length = counts.length) (bounded : CoordinateBounds counts bounds) :
    SignedRatio.Equiv (SignedRatio.listSum ((factorialRectangle bounds).map (fun orders =>
      SignedRatio.mul ⟨jointInverseBinomial counts orders, 1, Nat.zero_lt_one⟩
        (QProb.ofNat (jointChoose target orders)).toSignedRatio)))
      (if counts = target then SignedRatio.one else SignedRatio.zero) := by
  induction counts generalizing target bounds with
  | nil => cases target with
      | nil => cases bounds with
          | nil => rfl
          | cons bound bounds => exact False.elim bounded
      | cons value target => simp only [List.length_cons, List.length_nil] at dimension; omega
  | cons count counts ih => cases target with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons value target => cases bounds with
          | nil => exact False.elim bounded
          | cons bound bounds =>
              let head := fun order => SignedRatio.mul ⟨inverseBinomial count order, 1, Nat.zero_lt_one⟩
                (QProb.ofNat (binom order value)).toSignedRatio
              let tail := fun orders => SignedRatio.mul ⟨jointInverseBinomial counts orders, 1, Nat.zero_lt_one⟩
                (QProb.ofNat (jointChoose target orders)).toSignedRatio
              let term := fun order orders => SignedRatio.mul
                ⟨jointInverseBinomial (count :: counts) (order :: orders), 1, Nat.zero_lt_one⟩
                (QProb.ofNat (jointChoose (value :: target) (order :: orders))).toSignedRatio
              have separated (order : Nat) (orders : List Nat) :
                  SignedRatio.Equiv (term order orders) (SignedRatio.mul (head order) (tail orders)) := by
                simp only [term, head, tail, jointInverseBinomial, jointChoose, SignedRatio.Equiv,
                  SignedRatio.mul, QProb.ofNat, QProb.toSignedRatio, Nat.mul_one,
                  Int.natCast_one, Int.natCast_mul, Int.mul_one]
                ac_rfl
              have tailKernel := ih target bounds (Nat.succ.inj dimension) bounded.2
              have rows (order : Nat) : SignedRatio.Equiv
                  (SignedRatio.listSum ((factorialRectangle bounds).map (term order)))
                  (SignedRatio.mul (head order) (if counts = target then SignedRatio.one else SignedRatio.zero)) := by
                refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ (separated order)) ?_
                refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
                  simpa only [List.map_map, Function.comp_def] using
                    (SignedRatio.mul_listSum (head order) ((factorialRectangle bounds).map tail)))) ?_
                exact SignedRatio.mul_congr (SignedRatio.equiv_refl _) tailKernel
              have grouped := SignedRatio.listSum_flatMap (List.range (bound + 1))
                (fun order => (factorialRectangle bounds).map (term order))
              refine SignedRatio.equiv_trans (by
                simpa only [List.length_cons, factorialRectangle, List.map_flatMap, List.map_map, Function.comp_def, term] using grouped) ?_
              refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ rows) ?_
              refine SignedRatio.equiv_trans (SignedRatio.equiv_symm (by
                simpa only [List.map_map, Function.comp_def] using
                  (SignedRatio.listSum_mul ((List.range (bound + 1)).map head)
                    (if counts = target then SignedRatio.one else SignedRatio.zero)))) ?_
              refine SignedRatio.equiv_trans (SignedRatio.mul_congr
                (inverseBinomial_reverse_ratio_kernel count value bound bounded.1)
                (SignedRatio.equiv_refl _)) ?_
              by_cases first : count = value <;> by_cases rest : counts = target
              · simp only [first, rest, if_true]
                exact SignedRatio.one_mul _
              · simp only [List.cons.injEq, first, rest, true_and, false_and, if_false, if_true]
                exact SignedRatio.mul_zero _
              · simp only [List.cons.injEq, first, rest, false_and, if_false, if_true]
                exact SignedRatio.zero_mul _
              · simp only [List.cons.injEq, first, rest, false_and, if_false]
                exact SignedRatio.zero_mul _

/-- Coordinate bounds characterize membership in the actual rectangle. -/
theorem factorialRectangle_complete (bounds orders : List Nat) (bounded : CoordinateBounds orders bounds) :
    orders ∈ factorialRectangle bounds := by
  induction bounds generalizing orders with
  | nil => cases orders with
      | nil => exact List.mem_singleton_self _
      | cons value orders => exact False.elim bounded
  | cons bound bounds ih => cases orders with
      | nil => exact False.elim bounded
      | cons order orders =>
          exact List.mem_flatMap.mpr ⟨order, List.mem_range.mpr (Nat.lt_succ_of_le bounded.1),
            List.mem_map.mpr ⟨orders, ih orders bounded.2, rfl⟩⟩

theorem coordinateBounds_zero (bounds : List Nat) : CoordinateBounds (List.replicate bounds.length 0) bounds := by
  induction bounds with
  | nil => exact True.intro
  | cons bound bounds ih => exact ⟨Nat.zero_le _, ih⟩

theorem factorialRectangle_positive (bounds : List Nat) : 0 < (factorialRectangle bounds).length := by
  have member := factorialRectangle_complete bounds _ (coordinateBounds_zero bounds)
  cases same : factorialRectangle bounds with
  | nil => rw [same] at member; exact False.elim (List.not_mem_nil member)
  | cons value values => exact Nat.zero_lt_succ _

/-- The rectangle enumeration contains each bounded multi-index exactly once,
as witnessed by its finite delta-selector identity. -/
theorem factorialRectangle_select (bounds target : List Nat) (f : List Nat → SignedRatio)
    (within : CoordinateBounds target bounds) :
    SignedRatio.Equiv (SignedRatio.listSum ((factorialRectangle bounds).map (fun orders =>
      if orders = target then f target else SignedRatio.zero))) (f target) := by
  induction bounds generalizing target f with
  | nil => cases target with
      | nil => exact SignedRatio.add_zero _
      | cons value target => exact False.elim within
  | cons bound bounds ih => cases target with
      | nil => exact False.elim within
      | cons value target =>
          let term := fun order orders => if order :: orders = value :: target then f (value :: target) else SignedRatio.zero
          have rows (order : Nat) : SignedRatio.Equiv
              (SignedRatio.listSum ((factorialRectangle bounds).map (term order)))
              (if order = value then f (value :: target) else SignedRatio.zero) := by
            by_cases same : order = value
            · subst order
              simpa only [term, List.cons.injEq, true_and, if_true] using
                ih target (fun _ => f (value :: target)) within.2
            · simp only [term, List.cons.injEq, same, false_and, if_false]
              exact SignedRatio.listSum_map_zero _
          have grouped := SignedRatio.listSum_flatMap (List.range (bound + 1))
            (fun order => (factorialRectangle bounds).map (term order))
          refine SignedRatio.equiv_trans (by
            simpa only [factorialRectangle, List.map_flatMap, List.map_map, Function.comp_def, term] using grouped) ?_
          exact SignedRatio.equiv_trans (SignedRatio.listSum_map_congr _ _ _ rows)
            (SignedRatio.listSum_range_select (bound + 1) value (fun _ => f (value :: target)) (Nat.lt_succ_of_le within.1))

theorem jointChoose_zeroOrders (counts : List Nat) : jointChoose (List.replicate counts.length 0) counts = 1 := by
  induction counts with
  | nil => rfl
  | cons count counts ih => simp only [List.length_cons, List.replicate_succ, jointChoose, binom_zero_right, Nat.one_mul, ih]

end Thesis.Probability.Distros
