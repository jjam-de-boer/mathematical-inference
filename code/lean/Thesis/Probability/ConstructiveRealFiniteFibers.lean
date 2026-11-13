import Thesis.Probability.ConstructiveRealBilinearFubini
import Thesis.Probability.ConstructiveRealRationalScaling

namespace Thesis.Probability.ConstructiveReal.FiniteFibers
open ConstructiveReal
open Distros.RationalLinear

/-- Fibers contain distinct declared state indices, never occurrences of a
probability record. Equality decisions are finite index equality only. -/
def fiber (label : Fin micro → Fin groups) (j : Fin groups) : List (Fin micro) :=
  (List.finRange micro).filter (fun i => decide (j = label i))

def sumFiber (label : Fin micro → Fin groups) (values : Fin micro → ConstructiveReal) (j : Fin groups) : ConstructiveReal :=
  listSum ((fiber label j).map values)

theorem mem_fiber (label : Fin micro → Fin groups) (j : Fin groups) (i : Fin micro) :
    i ∈ fiber label j ↔ j = label i := by
  simp only [fiber, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

private theorem selector_filter (indices : List A) (selected : A → Bool) (values : A → ConstructiveReal) :
    Equiv (listSum (indices.map (fun i => mul (realInteger (if selected i then 1 else 0)) (values i))))
      (listSum ((indices.filter selected).map values)) := by
  induction indices with
  | nil => exact equiv_refl zero
  | cons i rest ih =>
      cases same : selected i with
      | false =>
          simp only [List.map_cons, List.filter_cons, same, Bool.false_eq_true, if_false, listSum]
          exact equiv_trans (add_congr (zero_mul (values i)) ih) (zero_add _)
      | true =>
          simp only [List.map_cons, List.filter_cons, same, if_true, listSum]
          exact add_congr (one_mul (values i)) ih

theorem sumFiber_pair (label : Fin micro → Fin groups) (values : Fin micro → ConstructiveReal) (j : Fin groups) :
    Equiv (FiniteLinear.pair micro (fun i => realInteger (if j = label i then 1 else 0)) values) (sumFiber label values j) := by
  simpa only [FiniteLinear.pair, sumFiber, fiber, decide_eq_true_eq] using
    selector_filter (List.finRange micro) (fun i => decide (j = label i)) values

/-- Exact finite fiber Fubini. The selector sum over macrostate indices
selects `observable (label i)`, with no choice of a representative. -/
theorem grouped_pair (label : Fin micro → Fin groups) (values : Fin micro → ConstructiveReal)
    (observable : Fin groups → ConstructiveReal) :
    Equiv (FiniteLinear.pair micro (fun i => observable (label i)) values)
      (FiniteLinear.pair groups observable (sumFiber label values)) := by
  let matrix := fun j i => realInteger (if j = label i then 1 else 0)
  have selected (i : Fin micro) : Equiv (FiniteLinear.pair groups observable (fun j => matrix j i)) (observable (label i)) :=
    equiv_trans (FiniteLinear.pair_comm groups _ _) (FiniteLinear.pair_unit groups (label i) observable)
  exact equiv_trans (equiv_symm (FiniteLinear.pair_congr micro _ _ values values selected (fun _ => equiv_refl _)))
    (equiv_trans (FiniteLinear.combination_pair groups micro matrix observable values)
      (FiniteLinear.pair_congr groups observable observable _ _ (fun _ => equiv_refl _) (sumFiber_pair label values)))

/-- Aggregation preserves the actual total sum, including empty index
families whenever a labeling function exists. -/
theorem grouped_sum (label : Fin micro → Fin groups) (values : Fin micro → ConstructiveReal) :
    Equiv (listSum ((List.finRange micro).map values)) (listSum ((List.finRange groups).map (sumFiber label values))) :=
  equiv_trans (equiv_symm (listSum_map_congr (List.finRange micro) _ _ (fun i _ => one_mul (values i))))
    (equiv_trans (grouped_pair label values (fun _ => one))
      (listSum_map_congr (List.finRange groups) _ _ (fun j _ => one_mul _)))

theorem sumFiber_congr (label : Fin micro → Fin groups) (j : Fin groups) (first second : Fin micro → ConstructiveReal)
    (same : ∀ i, j = label i → Equiv (first i) (second i)) : Equiv (sumFiber label first j) (sumFiber label second j) :=
  listSum_map_congr (fiber label j) first second (fun i member => same i ((mem_fiber label j i).mp member))

private theorem sum_constant (indices : List A) (value : ConstructiveReal) :
    Equiv (listSum (indices.map (fun _ => value))) (scaleNat indices.length value) := by
  induction indices with
  | nil => exact equiv_refl zero
  | cons i rest ih => exact equiv_trans (add_congr (equiv_refl value) ih) (add_comm _ _)

/-- On a constant fiber, multiplicity is the cardinality of the actual
finite fiber. It is not a freely supplied or assumed reference weight. -/
theorem sumFiber_constant (label : Fin micro → Fin groups) (j : Fin groups) (values : Fin micro → ConstructiveReal)
    (value : ConstructiveReal) (constant : ∀ i, j = label i → Equiv (values i) value) :
    Equiv (sumFiber label values j) (mul (realInteger ((fiber label j).length : Int)) value) :=
  equiv_trans (sumFiber_congr label j values (fun _ => value) constant)
    (equiv_trans (sum_constant (fiber label j) value) (scaleNat_mul _ _))

theorem sumFiber_mul_right (label : Fin micro → Fin groups) (values : Fin micro → ConstructiveReal)
    (factor : ConstructiveReal) (j : Fin groups) :
    Equiv (sumFiber label (fun i => mul (values i) factor) j) (mul (sumFiber label values j) factor) := by
  simpa only [sumFiber, List.map_map, Function.comp_def] using equiv_symm (listSum_mul ((fiber label j).map values) factor)

end Thesis.Probability.ConstructiveReal.FiniteFibers

namespace Thesis.Probability

/-- A finite grouping with explicit representative data for every retained
macrostate. No representative is selected from an existential proposition. -/
structure FiniteStateGrouping (micro groups : Nat) where
  label : Fin micro → Fin groups
  representative : Fin groups → Fin micro
  covers : ∀ j, label (representative j) = j

namespace FiniteStateGrouping
open ConstructiveReal.FiniteFibers

/-- Representatives can themselves be computed from finite nonempty fibers.
The proof of nonemptiness justifies taking the actual filtered list head. -/
def ofNonemptyFibers (label : Fin micro → Fin groups) (nonempty : ∀ j, fiber label j ≠ []) : FiniteStateGrouping micro groups where
  label := label
  representative j := (fiber label j).head (nonempty j)
  covers j := ((mem_fiber label j _).mp (List.head_mem (nonempty j))).symm

/-- A supplied finite surjectivity proof is sufficient: representative data
are computed by enumeration, without extracting a state from an existential
proposition or using a choice axiom. -/
def ofSurjective (label : Fin micro → Fin groups) (surjective : ∀ j, ∃ i, label i = j) : FiniteStateGrouping micro groups :=
  ofNonemptyFibers label (fun j empty => by
    obtain ⟨i, same⟩ := surjective j
    have member := (mem_fiber label j i).mpr same.symm
    rw [empty] at member
    exact List.not_mem_nil member)

def degeneracy (grouping : FiniteStateGrouping micro groups) (j : Fin groups) : Nat := (fiber grouping.label j).length

theorem degeneracy_positive (grouping : FiniteStateGrouping micro groups) (j : Fin groups) : 0 < grouping.degeneracy j :=
  List.length_pos_of_mem ((mem_fiber grouping.label j (grouping.representative j)).mpr (grouping.covers j).symm)

def reference (grouping : FiniteStateGrouping micro groups) (j : Fin groups) : PositiveRatio :=
  .ofNat (grouping.degeneracy j) (grouping.degeneracy_positive j)

theorem macro_positive (grouping : FiniteStateGrouping micro groups) (nonempty : 0 < micro) : 0 < groups := by
  have member := (grouping.label ⟨0, nonempty⟩).isLt
  omega

end FiniteStateGrouping
end Thesis.Probability
