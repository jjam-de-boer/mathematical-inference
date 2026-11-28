import Thesis.Probability.Distros.RationalLinearProjection
import Thesis.Probability.Distros.MomentTableCheck

/-!
Complete constructive feasibility for finite rational linear inequalities.

Recursive projection eliminates one variable at each step. At dimension
zero a finite scan either certifies every constant bound nonnegative or
returns an actual contradictory row. Feasible projected values are lifted
by computed rational endpoints, yielding a complete satisfying assignment.
Failure carries a finite elimination trace down to a negative constant row,
and its theorem excludes every rational assignment. The algorithm has no
probability-denominator cap and returns checked data on both branches.
-/

namespace Thesis.Probability.Distros.RationalLinear

theorem extend_restrict (values : Fin (variables + 1) → SignedRatio) :
    extend (fun i => values i.castSucc) (values (Fin.last variables)) = values := by
  funext i
  by_cases earlier : i.val < variables
  · let old : Fin variables := ⟨i.val, earlier⟩
    have same : old.castSucc = i := Fin.ext rfl
    rw [← same, extend_castSucc]
  · have same : i = Fin.last variables := Fin.ext (by simp only [Fin.val_last]; have bound := i.isLt; omega)
    rw [same, extend_last]

/-- Removing rows always retains a literal subsystem. For the particular
removals below every satisfying assignment also satisfies the old rows. -/
structure PrunedRows (original : List (Inequality variables)) where
  rows : List (Inequality variables)
  subset : ∀ row ∈ rows, row ∈ original
  restores : ∀ values, Satisfies rows values → Satisfies original values

private def CoefficientZero (row : Inequality variables) : Prop :=
  ∀ i, row.coefficients i = 0

private def Dominates (other row : Inequality variables) : Prop :=
  (∀ i, other.coefficients i = row.coefficients i) ∧ SignedRatio.LE other.bound row.bound

private instance (row : Inequality variables) : Decidable (CoefficientZero row) := by
  unfold CoefficientZero
  infer_instance

private instance (other row : Inequality variables) : Decidable (Dominates other row) := by
  unfold Dominates
  infer_instance

private theorem holds_of_zero_coefficients (row : Inequality variables) (zero : CoefficientZero row)
    (nonnegative : SignedRatio.LE SignedRatio.zero row.bound) (values : Fin variables → SignedRatio) :
    row.Holds values := by
  unfold Inequality.Holds
  rw [funext zero]
  exact (SignedRatio.le_congr (dot_zero variables values) (SignedRatio.equiv_refl _)).mpr nonnegative

private theorem holds_of_dominates {other row : Inequality variables} (tighter : Dominates other row)
    {values : Fin variables → SignedRatio} (holds : other.Holds values) : row.Holds values := by
  unfold Inequality.Holds at holds ⊢
  rw [← funext tighter.1]
  exact SignedRatio.le_trans holds tighter.2

/-- Discard true constant rows and rows implied by a later bound with the
same coefficients. The check uses rational order, including equal bounds
written with different denominators. A negative constant is retained
unless a row with the same coefficients already implies it. -/
def prune : (rows : List (Inequality variables)) → PrunedRows rows
  | [] => ⟨[], fun _ member => member, fun _ holds => holds⟩
  | row :: rest =>
    let tail := prune rest
    if redundant : CoefficientZero row ∧ SignedRatio.LE SignedRatio.zero row.bound then
      ⟨tail.rows, fun other listed => List.mem_cons_of_mem _ (tail.subset other listed),
        fun values holds other listed => (List.mem_cons.mp listed).elim
          (fun same => same.symm ▸ holds_of_zero_coefficients row redundant.1 redundant.2 values)
          (tail.restores values holds other)⟩
    else if redundant : ∃ other ∈ tail.rows, Dominates other row then
      ⟨tail.rows, fun other listed => List.mem_cons_of_mem _ (tail.subset other listed),
        fun values holds other listed => (List.mem_cons.mp listed).elim
          (fun same => same.symm ▸ (by
            obtain ⟨tighter, member, dominates⟩ := redundant
            exact holds_of_dominates dominates (holds tighter member)))
          (tail.restores values holds other)⟩
    else
      ⟨row :: tail.rows,
        fun other listed => (List.mem_cons.mp listed).elim (fun same => same.symm ▸ List.mem_cons_self ..)
          (fun later => List.mem_cons_of_mem _ (tail.subset other later)),
        fun values holds other listed => (List.mem_cons.mp listed).elim
          (fun same => holds other (List.mem_cons.mpr (Or.inl same)))
          (tail.restores values (fun r member => holds r (List.mem_cons_of_mem _ member)) other)⟩

/-- A finite elimination trace ends in an actual contradictory constant
row. This is checked data, not an oracle declaring the system infeasible. -/
inductive Infeasibility : (variables : Nat) → List (Inequality variables) → Type where
  | constant (rows : List (Inequality 0)) (row : Inequality 0) (member : row ∈ rows) (negative : row.bound.num < 0) :
      Infeasibility 0 rows
  | projected (rows : List (Inequality (variables + 1))) (previous : Infeasibility variables (project rows)) :
      Infeasibility (variables + 1) rows
  | subsystem (rows smaller : List (Inequality variables)) (subset : ∀ row ∈ smaller, row ∈ rows)
      (previous : Infeasibility variables smaller) : Infeasibility variables rows

theorem Infeasibility.not_exists (certificate : Infeasibility variables rows) :
    ¬ ∃ values : Fin variables → SignedRatio, Satisfies rows values := by
  induction certificate with
  | constant rows row member negative =>
      rintro ⟨values, valid⟩
      have bound : SignedRatio.LE SignedRatio.zero row.bound := valid row member
      have nonnegative := (SignedRatio.nonnegative_congr (SignedRatio.sub_zero row.bound)).mp bound
      change 0 ≤ row.bound.num at nonnegative
      omega
  | projected rows previous ih =>
      rintro ⟨values, valid⟩
      apply ih
      refine ⟨fun i => values i.castSucc, project_sound rows _ (values (Fin.last _)) ?_⟩
      simpa only [extend_restrict] using valid
  | subsystem rows smaller subset previous ih =>
      rintro ⟨values, valid⟩
      exact ih ⟨values, fun row listed => valid row (subset row listed)⟩

inductive SolveResult (variables : Nat) (rows : List (Inequality variables)) where
  | feasible (values : Fin variables → SignedRatio) (valid : Satisfies rows values)
  | infeasible (certificate : Infeasibility variables rows)

private def solveUsing (usePruning : Bool) :
    (variables : Nat) → (rows : List (Inequality variables)) → SolveResult variables rows
  | 0, rows =>
      match checkFiniteMasses rows (fun row => row.bound) with
      | .negative row member negative => .infeasible (.constant rows row member negative)
      | .nonnegative nonnegative => .feasible (fun i => Fin.elim0 i) (by
          intro row member
          exact (SignedRatio.nonnegative_congr (SignedRatio.sub_zero row.bound)).mpr (nonnegative row member))
  | variables + 1, rows =>
      if usePruning then
        let reduced := prune (project rows)
        match solveUsing usePruning variables reduced.rows with
        | .infeasible certificate =>
            .infeasible (.projected rows (.subsystem _ _ reduced.subset certificate))
        | .feasible values valid =>
            let last := lift rows values (reduced.restores values valid)
            .feasible (extend values last.val) last.property
      else
        match solveUsing usePruning variables (project rows) with
        | .infeasible certificate => .infeasible (.projected rows certificate)
        | .feasible values valid =>
            let last := lift rows values valid
            .feasible (extend values last.val) last.property

/-- Complete constructive rational linear feasibility with fraction-free
elimination. The unpruned recursion also supports small kernel-reduction
fixtures where comparing redundant rows costs more than retaining them. -/
def solve (variables : Nat) (rows : List (Inequality variables)) : SolveResult variables rows :=
  solveUsing false variables rows

/-- On larger systems the solver removes redundant intermediate rows
before eliminating the next variable. The result has the same checked
feasibility or refutation interface. -/
def solvePruned (variables : Nat) (rows : List (Inequality variables)) : SolveResult variables rows :=
  solveUsing true variables rows

theorem solve_success_iff (variables : Nat) (rows : List (Inequality variables)) :
    (match solve variables rows with | .feasible _ _ => True | .infeasible _ => False) ↔
      ∃ values : Fin variables → SignedRatio, Satisfies rows values := by
  cases result : solve variables rows with
  | feasible values valid =>
      constructor
      · intro _; exact ⟨values, valid⟩
      · intro _; trivial
  | infeasible certificate =>
      constructor
      · intro impossible; exact False.elim impossible
      · intro realizable; exact False.elim (certificate.not_exists realizable)

end Thesis.Probability.Distros.RationalLinear
