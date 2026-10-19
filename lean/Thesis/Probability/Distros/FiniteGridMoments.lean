import Thesis.Probability.Distros.ProbabilityList
import Thesis.Probability.Distros.RationalLinearSolve

namespace Thesis.Probability.SignedRatio

/-- A duplicate-free finite list has an exact rational delta selector. -/
theorem listSum_list_select [DecidableEq A] (cells : List A) (target : A) (f : A → SignedRatio)
    (distinct : cells.Nodup) (member : target ∈ cells) :
    Equiv (listSum (cells.map (fun cell => if cell = target then f target else zero))) (f target) := by
  induction cells with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head cells ih =>
      by_cases here : head = target
      · subst head
        have others : Equiv (listSum (cells.map (fun cell => if cell = target then f target else zero))) zero := by
          refine equiv_trans (listSum_map_congr_on_mem cells _ (fun _ => zero) ?_) (listSum_map_zero cells)
          intro cell listed
          have different : cell ≠ target := by intro same; subst cell; exact (List.nodup_cons.mp distinct).1 listed
          rw [if_neg different]
          exact equiv_refl _
        exact equiv_trans (add_congr (equiv_refl _) others) (add_zero _)
      · have later := (List.mem_cons.mp member).resolve_left (Ne.symm here)
        change Equiv (add (if head = target then f target else zero)
          (listSum (cells.map (fun cell => if cell = target then f target else zero)))) (f target)
        rw [if_neg here]
        exact equiv_trans (add_congr (equiv_refl _) (ih (List.nodup_cons.mp distinct).2 later)) (zero_add _)

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.Distros

/-- Finite PMF integration on any explicitly supplied distinct grid. Only
positive-weight atoms must belong to the grid; null outliers remain untouched. -/
theorem Distro.rationalExpectation_grid_pmf [DecidableEq A] (μ : Distro A) (cells : List A)
    (distinct : cells.Nodup) (support : μ.AlmostSurely (fun cell => cell ∈ cells)) (f : A → SignedRatio) :
    SignedRatio.Equiv (μ.rationalExpectation f)
      (SignedRatio.listSum (cells.map (fun cell => SignedRatio.mul (μ.pmf cell).toSignedRatio (f cell)))) := by
  let term := fun cell x => if x = cell then f cell else SignedRatio.zero
  have selected : μ.AlmostSurely (fun x => SignedRatio.Equiv
      (SignedRatio.listSum (cells.map (fun cell => term cell x))) (f x)) := by
    intro atom member weight
    refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr cells _
      (fun cell => if cell = atom.1 then f atom.1 else SignedRatio.zero) ?_)
      (SignedRatio.listSum_list_select cells atom.1 f distinct (support atom member weight))
    intro cell
    by_cases same : cell = atom.1
    · subst cell; simp only [term, if_true]; exact SignedRatio.equiv_refl _
    · simp only [term, if_neg same, if_neg (Ne.symm same)]; exact SignedRatio.equiv_refl _
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr_positive f
    (fun x => SignedRatio.listSum (cells.map (fun cell => term cell x)))
    (fun atom member weight => SignedRatio.equiv_symm (selected atom member weight))) ?_
  refine SignedRatio.equiv_trans (μ.rationalExpectation_listSum cells term) ?_
  apply SignedRatio.listSum_map_congr
  intro cell
  refine SignedRatio.equiv_trans (μ.rationalExpectation_congr (term cell)
    (fun x => SignedRatio.mul (f cell) (if decide (x = cell) then SignedRatio.one else SignedRatio.zero)) ?_) ?_
  · intro x
    by_cases same : x = cell
    · simp only [term, same, if_true, decide_true]; exact SignedRatio.equiv_symm (SignedRatio.mul_one _)
    · simp only [term, same, if_false, decide_false, Bool.false_eq_true]; exact SignedRatio.equiv_symm (SignedRatio.mul_zero _)
  · exact SignedRatio.equiv_trans (μ.rationalExpectation_mul_left _ _)
      (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (μ.rationalExpectation_indicator (FiniteProbRecord.singletonEvent cell))) (SignedRatio.mul_comm _ _))

/-- Bounded natural enumeration and Fin enumeration have the same order. -/
theorem finRange_val_map (n : Nat) (f : Nat → A) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.finRange_succ_last, List.range_succ]
      simpa only [List.map_append, List.map_map, Function.comp_def, Fin.val_castSucc,
        Fin.val_last, List.map_cons, List.map_nil] using congrArg (fun values => values ++ [f n]) ih

theorem finRange_getD_map (cells : List A) (default : A) (f : A → B) :
    (List.finRange cells.length).map (fun i => f (cells.getD i.val default)) = cells.map f :=
  (finRange_val_map cells.length (fun i => f (cells.getD i default))).trans (range_getD_map cells default f)

namespace RationalLinear

theorem dot_sum (variables : Nat) (coefficients : Fin variables → Int) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (dot variables coefficients values)
      (SignedRatio.listSum ((List.finRange variables).map (fun i => SignedRatio.scaleInt (coefficients i) (values i)))) := by
  induction variables with
  | zero => exact SignedRatio.equiv_refl _
  | succ variables ih =>
      rw [List.finRange_succ_last, List.map_append]
      refine SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _)
        (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc))) ?_
      refine SignedRatio.equiv_trans (SignedRatio.add_comm _ _) ?_
      exact SignedRatio.equiv_symm (SignedRatio.equiv_trans (SignedRatio.listSum_append _ _)
        (SignedRatio.add_congr (by simp only [List.map_map, Function.comp_def]; exact SignedRatio.equiv_refl _)
          (SignedRatio.add_zero _)))

theorem dot_unit (variables : Nat) (index : Fin variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (dot variables (fun i => if i = index then 1 else 0) values) (values index) := by
  refine SignedRatio.equiv_trans (dot_sum variables _ values) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr (List.finRange variables) _
    (fun i => if i = index then values index else SignedRatio.zero) ?_)
    (SignedRatio.listSum_list_select _ index values (finRange_nodup variables) (List.mem_finRange index))
  intro i
  change SignedRatio.Equiv (SignedRatio.scaleInt (if i = index then 1 else 0) (values i))
    (if i = index then values index else SignedRatio.zero)
  by_cases same : i = index
  · subst i; simp only [if_true]; exact SignedRatio.one_scaleInt _
  · simp only [if_neg same]; exact SignedRatio.zero_scaleInt _

theorem minus_one_scaleInt (value : SignedRatio) : SignedRatio.Equiv (SignedRatio.scaleInt (-1) value) (SignedRatio.neg value) :=
  SignedRatio.equiv_trans (SignedRatio.neg_scaleInt 1 value) (SignedRatio.neg_congr (SignedRatio.one_scaleInt value))

theorem dot_neg_coefficients (variables : Nat) (coefficients : Fin variables → Int) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (dot variables (fun i => -coefficients i) values) (SignedRatio.neg (dot variables coefficients values)) :=
  SignedRatio.equiv_trans (by simpa only [Int.neg_one_mul] using dot_scale_coefficients variables (-1) coefficients values)
    (minus_one_scaleInt _)

theorem dot_negative_unit (variables : Nat) (index : Fin variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (dot variables (fun i => if i = index then -1 else 0) values) (SignedRatio.neg (values index)) := by
  have coefficients : (fun i : Fin variables => if i = index then (-1 : Int) else 0) =
      (fun i => -(if i = index then (1 : Int) else 0)) := by
    funext i
    by_cases same : i = index <;> simp only [same, if_true, if_false, Int.neg_zero]
  rw [coefficients]
  exact SignedRatio.equiv_trans (dot_neg_coefficients variables _ values) (SignedRatio.neg_congr (dot_unit variables index values))

end RationalLinear
end Thesis.Probability.Distros
