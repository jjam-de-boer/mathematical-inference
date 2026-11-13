import Thesis.Probability.ConstructiveRealLinearRows

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal

/-- Projection filters inspect integral pivots only. The analytic bounds
are never compared, rounded, or replaced by rational tolerances. -/
def project (rows : List (Inequality (variables + 1))) : List (Inequality variables) :=
  ((rows.filter (fun row => decide (row.pivot = 0))).map Inequality.trim) ++
    (rows.filter (fun row => decide (0 < row.pivot))).flatMap (fun upper =>
      (rows.filter (fun row => decide (row.pivot < 0))).map (fun lower => combine upper lower))

theorem project_zero_mem (rows : List (Inequality (variables + 1))) (row : Inequality (variables + 1))
    (member : row ∈ rows) (zeroPivot : row.pivot = 0) : row.trim ∈ project rows :=
  List.mem_append_left _ (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true zeroPivot⟩, rfl⟩)

theorem project_pair_mem (rows : List (Inequality (variables + 1))) (upper lower : Inequality (variables + 1))
    (upperMember : upper ∈ rows) (lowerMember : lower ∈ rows) (positive : 0 < upper.pivot) (negative : lower.pivot < 0) :
    combine upper lower ∈ project rows :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨upper, List.mem_filter.mpr ⟨upperMember, decide_eq_true positive⟩,
    List.mem_map.mpr ⟨lower, List.mem_filter.mpr ⟨lowerMember, decide_eq_true negative⟩, rfl⟩⟩)

/-- Every actual satisfying assignment satisfies its projection, with
analytic bounds and either sign of integral coefficient. -/
theorem project_sound (rows : List (Inequality (variables + 1))) (values : Fin variables → ConstructiveReal) (last : ConstructiveReal)
    (satisfies : Satisfies rows (FiniteLinear.extend values last)) : Satisfies (project rows) values := by
  intro row member
  rcases List.mem_append.mp member with unchanged | paired
  · obtain ⟨source, listed, same⟩ := List.mem_map.mp unchanged
    cases same
    exact (source.holds_zero_iff values last (of_decide_eq_true (List.mem_filter.mp listed).2)).mp
      (satisfies source (List.mem_filter.mp listed).1)
  · obtain ⟨upper, upperListed, lowerRows⟩ := List.mem_flatMap.mp paired
    obtain ⟨lower, lowerListed, same⟩ := List.mem_map.mp lowerRows
    cases same
    have positive := of_decide_eq_true (List.mem_filter.mp upperListed).2
    have negative := of_decide_eq_true (List.mem_filter.mp lowerListed).2
    exact (combine_holds_iff upper lower values positive negative).mpr
      (le_trans ((lower.holds_lower_iff values last negative).mp (satisfies lower (List.mem_filter.mp lowerListed).1))
        ((upper.holds_upper_iff values last positive).mp (satisfies upper (List.mem_filter.mp upperListed).1)))

def lowerBounds (rows : List (Inequality (variables + 1))) (values : Fin variables → ConstructiveReal) : List ConstructiveReal :=
  (rows.filter (fun row => decide (row.pivot < 0))).map (fun row => row.lowerValue values)

def upperBounds (rows : List (Inequality (variables + 1))) (values : Fin variables → ConstructiveReal) : List ConstructiveReal :=
  (rows.filter (fun row => decide (0 < row.pivot))).map (fun row => row.upperValue values)

/-- Back-substitution constructs the eliminated analytic value by finite
extrema. Compatibility is proved from the actual projected rows; no real
feasibility oracle or nonconstructive witness selection is used. -/
def lift (rows : List (Inequality (variables + 1))) (values : Fin variables → ConstructiveReal)
    (satisfies : Satisfies (project rows) values) :
    {last : ConstructiveReal // Satisfies rows (FiniteLinear.extend values last)} := by
  have compatible : ∀ below ∈ lowerBounds rows values, ∀ above ∈ upperBounds rows values, LE below above := by
    intro below lowerMember above upperMember
    obtain ⟨lower, lowerListed, lowerSame⟩ := List.mem_map.mp lowerMember
    obtain ⟨upper, upperListed, upperSame⟩ := List.mem_map.mp upperMember
    have positive := of_decide_eq_true (List.mem_filter.mp upperListed).2
    have negative := of_decide_eq_true (List.mem_filter.mp lowerListed).2
    rw [← lowerSame, ← upperSame]
    exact (combine_holds_iff upper lower values positive negative).mp
      (satisfies (combine upper lower) (project_pair_mem rows upper lower
        (List.mem_filter.mp upperListed).1 (List.mem_filter.mp lowerListed).1 positive negative))
  let interval := compatibleInterval (lowerBounds rows values) (upperBounds rows values) compatible
  refine ⟨interval.val, ?_⟩
  intro row member
  by_cases positive : 0 < row.pivot
  · exact (row.holds_upper_iff values interval.val positive).mpr (interval.property.2 _
      (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true positive⟩, rfl⟩))
  · by_cases negative : row.pivot < 0
    · exact (row.holds_lower_iff values interval.val negative).mpr (interval.property.1 _
        (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true negative⟩, rfl⟩))
    · have zeroPivot : row.pivot = 0 := by omega
      exact (row.holds_zero_iff values interval.val zeroPivot).mpr (satisfies row.trim (project_zero_mem rows row member zeroPivot))

theorem project_iff (rows : List (Inequality (variables + 1))) (values : Fin variables → ConstructiveReal) :
    Satisfies (project rows) values ↔ ∃ last, Satisfies rows (FiniteLinear.extend values last) :=
  ⟨fun satisfies => ⟨(lift rows values satisfies).val, (lift rows values satisfies).property⟩,
    fun ⟨last, satisfies⟩ => project_sound rows values last satisfies⟩

private theorem extend_restrict (values : Fin (variables + 1) → ConstructiveReal) :
    FiniteLinear.extend (fun i => values i.castSucc) (values (Fin.last variables)) = values := by
  funext i
  exact Fin.lastCases (FiniteLinear.extend_last _ _) (fun j => FiniteLinear.extend_castSucc _ _ j) i

/-- After eliminating every variable only finitely many closed analytic
nonnegativity conditions remain. This is not a decision procedure for
arbitrary real feasibility. -/
def constantConditions : (variables : Nat) → List (Inequality variables) → Prop
  | 0, rows => ∀ row ∈ rows, LE zero row.bound
  | variables + 1, rows => constantConditions variables (project rows)

/-- All original variables are computed from the finite projected constant
conditions. Bounds remain analytic, and no denominator restriction or
independence hypothesis is imposed on the coefficient system. -/
def solve : (variables : Nat) → (rows : List (Inequality variables)) → constantConditions variables rows →
    {values : Fin variables → ConstructiveReal // Satisfies rows values}
  | 0, _rows, consistent => ⟨fun i => Fin.elim0 i, consistent⟩
  | variables + 1, rows, consistent =>
      let prior := solve variables (project rows) consistent
      let next := lift rows prior.val prior.property
      ⟨FiniteLinear.extend prior.val next.val, next.property⟩

theorem constantConditions_of_satisfies (variables : Nat) (rows : List (Inequality variables))
    (values : Fin variables → ConstructiveReal) (satisfies : Satisfies rows values) : constantConditions variables rows := by
  induction variables with
  | zero => exact satisfies
  | succ variables ih =>
      have restored : Satisfies rows (FiniteLinear.extend (fun i => values i.castSucc) (values (Fin.last variables))) := by
        rw [extend_restrict]
        exact satisfies
      exact ih (project rows) (fun i => values i.castSucc) (project_sound rows _ _ restored)

/-- Exact constructive feasibility equivalence. The forward implication
returns the explicit solver above, rather than extracting a real tuple
from an existential proof. -/
theorem satisfies_iff_constants (variables : Nat) (rows : List (Inequality variables)) :
    constantConditions variables rows ↔ ∃ values, Satisfies rows values :=
  ⟨fun consistent => ⟨(solve variables rows consistent).val, (solve variables rows consistent).property⟩,
    fun ⟨values, satisfies⟩ => constantConditions_of_satisfies variables rows values satisfies⟩

end Thesis.Probability.AnalyticLinear
