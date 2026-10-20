import Thesis.Probability.Distros.RationalMassGrid
import Thesis.Probability.Distros.JointMomentTableAlgebra

namespace Thesis.Probability.Distros

/-- Selected integer-valued responses with rational expectation intervals.
Equal endpoints encode exact moments. Factorial kernels and event indicators
are special cases; negative auxiliary bounds and responses are permitted. -/
structure MomentInterval (A : Type u) where
  response : A → Int
  lower : SignedRatio
  upper : SignedRatio

def MomentInterval.exact (response : A → Int) (value : SignedRatio) : MomentInterval A := ⟨response, value, value⟩

def MomentInterval.mean (constraint : MomentInterval A) (μ : Distro A) : SignedRatio :=
  μ.rationalExpectation (fun x => ⟨constraint.response x, 1, Nat.zero_lt_one⟩)

def MomentInterval.LawHolds (constraint : MomentInterval A) (μ : Distro A) : Prop :=
  SignedRatio.LE constraint.lower (constraint.mean μ) ∧ SignedRatio.LE (constraint.mean μ) constraint.upper

def MomentInterval.coefficients (constraint : MomentInterval A) (cells : List A) (default : A) : Fin cells.length → Int :=
  fun i => constraint.response (cells.getD i.val default)

def MomentInterval.rows (constraint : MomentInterval A) (cells : List A) (default : A) : List (RationalLinear.Inequality cells.length) :=
  [⟨constraint.coefficients cells default, constraint.upper⟩,
    ⟨fun i => -constraint.coefficients cells default i, SignedRatio.neg constraint.lower⟩]

def MomentInterval.VectorHolds (constraint : MomentInterval A) (cells : List A) (default : A)
    (values : Fin cells.length → SignedRatio) : Prop :=
  SignedRatio.LE constraint.lower (RationalLinear.dot cells.length (constraint.coefficients cells default) values) ∧
    SignedRatio.LE (RationalLinear.dot cells.length (constraint.coefficients cells default) values) constraint.upper

theorem MomentInterval.rows_iff (constraint : MomentInterval A) (cells : List A) (default : A)
    (values : Fin cells.length → SignedRatio) :
    RationalLinear.Satisfies (constraint.rows cells default) values ↔ constraint.VectorHolds cells default values := by
  constructor
  · intro valid
    have upper := valid _ (List.mem_cons_self ..)
    have lower := valid _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have moved := (SignedRatio.le_congr (RationalLinear.dot_neg_coefficients cells.length (constraint.coefficients cells default) values)
      (SignedRatio.equiv_refl _)).mp lower
    exact ⟨(SignedRatio.neg_le_neg_iff _ _).mp moved, upper⟩
  · rintro ⟨lower, upper⟩ row member
    rcases List.mem_cons.mp member with same | later
    · cases same; exact upper
    · have same := List.mem_singleton.mp later
      cases same
      exact (SignedRatio.le_congr (RationalLinear.dot_neg_coefficients cells.length (constraint.coefficients cells default) values)
        (SignedRatio.equiv_refl _)).mpr ((SignedRatio.neg_le_neg_iff _ _).mpr lower)

/-- The declared grid is finite and distinct. A realizing law is constrained
only almost surely to that grid, retaining presentation invariance for null atoms. -/
structure PartialMomentProblem (A : Type u) where
  cells : List A
  default : A
  nonempty : 0 < cells.length
  distinct : cells.Nodup
  intervals : List (MomentInterval A)

namespace PartialMomentProblem

def rows (problem : PartialMomentProblem A) : List (RationalLinear.Inequality problem.cells.length) :=
  RationalLinear.simplexRows problem.cells.length ++ problem.intervals.flatMap (fun constraint => constraint.rows problem.cells problem.default)

def VectorHolds (problem : PartialMomentProblem A) (values : Fin problem.cells.length → SignedRatio) : Prop :=
  RationalLinear.Simplex values ∧ ∀ constraint ∈ problem.intervals, constraint.VectorHolds problem.cells problem.default values

theorem rows_iff (problem : PartialMomentProblem A) (values : Fin problem.cells.length → SignedRatio) :
    RationalLinear.Satisfies problem.rows values ↔ problem.VectorHolds values := by
  constructor
  · intro valid
    refine ⟨(RationalLinear.satisfies_simplex_iff _ values).mp (fun row member => valid row (List.mem_append_left _ member)), ?_⟩
    intro constraint member
    apply (constraint.rows_iff problem.cells problem.default values).mp
    intro row listed
    exact valid row (List.mem_append_right _ (List.mem_flatMap.mpr ⟨constraint, member, listed⟩))
  · rintro ⟨simplex, intervals⟩ row member
    rcases List.mem_append.mp member with mass | moment
    · exact (RationalLinear.satisfies_simplex_iff _ values).mpr simplex row mass
    · rcases List.mem_flatMap.mp moment with ⟨constraint, listed, belongs⟩
      exact (constraint.rows_iff problem.cells problem.default values).mpr (intervals constraint listed) row belongs

structure CompatibleLaw (problem : PartialMomentProblem A) where
  distro : Distro A
  support : distro.AlmostSurely (fun cell => cell ∈ problem.cells)
  moments : ∀ constraint ∈ problem.intervals, constraint.LawHolds distro
  retains : ∀ cell ∈ problem.cells, ∃ weight, (cell, weight) ∈ distro.record.atoms

/-- Feasible assignments are turned into actual laws, not left as an
external witness obligation. All grid cells remain in the output record. -/
def lawOfVector (problem : PartialMomentProblem A) (values : Fin problem.cells.length → SignedRatio)
    (valid : problem.VectorHolds values) : problem.CompatibleLaw :=
  ⟨simplexGrid problem.cells problem.default values valid.1 problem.nonempty,
    simplexGrid_supported problem.cells problem.default values valid.1 problem.nonempty,
    (by
      intro constraint member
      have bounds := valid.2 constraint member
      have integral := simplexGrid_integer_expectation problem.cells problem.default values valid.1 problem.nonempty constraint.response
      exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) integral).mpr bounds.1,
        (SignedRatio.le_congr integral (SignedRatio.equiv_refl _)).mpr bounds.2⟩),
    simplexGrid_retains problem.cells problem.default values valid.1 problem.nonempty⟩

theorem vectorOfLaw [DecidableEq A] (problem : PartialMomentProblem A) (μ : Distro A)
    (support : μ.AlmostSurely (fun cell => cell ∈ problem.cells))
    (moments : ∀ constraint ∈ problem.intervals, constraint.LawHolds μ) :
    problem.VectorHolds (gridMasses μ problem.cells problem.default) := by
  refine ⟨gridMasses_simplex μ problem.cells problem.default problem.distinct support, ?_⟩
  intro constraint member
  have bounds := moments constraint member
  have integral := gridMasses_integer_expectation μ problem.cells problem.default problem.distinct support constraint.response
  exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) integral).mp bounds.1,
    (SignedRatio.le_congr integral (SignedRatio.equiv_refl _)).mp bounds.2⟩

/-- Elimination refutations exclude every compatible law, including laws
with arbitrary additional zero-weight labels outside the declared grid. -/
theorem refutation_not_realizable [DecidableEq A] (problem : PartialMomentProblem A)
    (certificate : RationalLinear.Infeasibility problem.cells.length problem.rows) :
    ¬ ∃ μ : Distro A, μ.AlmostSurely (fun cell => cell ∈ problem.cells) ∧
      ∀ constraint ∈ problem.intervals, constraint.LawHolds μ := by
  rintro ⟨μ, support, moments⟩
  exact certificate.not_exists ⟨gridMasses μ problem.cells problem.default,
    (problem.rows_iff _).mpr (problem.vectorOfLaw μ support moments)⟩

inductive Result (problem : PartialMomentProblem A) where
  | feasible (law : problem.CompatibleLaw)
  | infeasible (certificate : RationalLinear.Infeasibility problem.cells.length problem.rows)

/-- Complete finite partial-moment decision, with no denominator cap and
no completed full moment table supplied by the caller. -/
def solve (problem : PartialMomentProblem A) : problem.Result :=
  match RationalLinear.solve problem.cells.length problem.rows with
  | .feasible values valid => .feasible (problem.lawOfVector values ((problem.rows_iff values).mp valid))
  | .infeasible certificate => .infeasible certificate

theorem solve_success_iff [DecidableEq A] (problem : PartialMomentProblem A) :
    (match problem.solve with | .feasible _ => True | .infeasible _ => False) ↔
      ∃ μ : Distro A, μ.AlmostSurely (fun cell => cell ∈ problem.cells) ∧
        ∀ constraint ∈ problem.intervals, constraint.LawHolds μ := by
  cases outcome : problem.solve with
  | feasible law =>
      constructor
      · intro _; exact ⟨law.distro, law.support, law.moments⟩
      · intro _; trivial
  | infeasible certificate =>
      constructor
      · intro impossible; exact False.elim impossible
      · intro realizable; exact False.elim (problem.refutation_not_realizable certificate realizable)

end PartialMomentProblem

/-- Constructive duplicate-freeness, reusing the checked finite-index
carrier instead of the standard range lemma's classical dependency. -/
theorem range_nodup_constructive (n : Nat) : (List.range n).Nodup := by
  have same := finRange_val_map n (fun i => i)
  simp only [List.map_id_fun] at same
  rw [← same]
  apply List.pairwise_map.mpr
  apply (finRange_nodup n).imp
  intro first second different equal
  exact different (Fin.ext equal)

/-- Scalar factorial-moment intervals on a known finite count bound. -/
def factorialMomentInterval (order : Nat) (lower upper : QProb) : MomentInterval Nat :=
  ⟨fun value => (fallingFactorial value order : Int), lower.toSignedRatio, upper.toSignedRatio⟩

def scalarPartialMomentProblem (bound : Nat) (intervals : List (MomentInterval Nat)) : PartialMomentProblem Nat :=
  ⟨List.range (bound + 1), 0, by simp only [List.length_range]; omega, range_nodup_constructive (bound + 1), intervals⟩

/-- Rectangle enumeration has no repeated count vectors. This is a finite
list fact and never shrinks the declared outcome domain or positive support. -/
theorem factorialRectangle_nodup (bounds : List Nat) : (factorialRectangle bounds).Nodup := by
  induction bounds with
  | nil => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | cons bound bounds ih =>
      apply List.pairwise_flatMap.mpr
      constructor
      · intro order _
        apply List.pairwise_map.mpr
        apply ih.imp
        intro first second different same
        exact different (List.cons.inj same).2
      · apply (range_nodup_constructive (bound + 1)).imp
        intro first second different x xMember y yMember same
        rcases List.mem_map.mp xMember with ⟨tail, _, xSame⟩
        rcases List.mem_map.mp yMember with ⟨other, _, ySame⟩
        cases xSame
        cases ySame
        exact different (List.cons.inj same).1

def mixedFactorialMomentInterval (orders : List Nat) (lower upper : QProb) : MomentInterval (List Nat) :=
  ⟨fun counts => (jointFalling orders counts : Int), lower.toSignedRatio, upper.toSignedRatio⟩

def jointPartialMomentProblem (bounds : List Nat) (intervals : List (MomentInterval (List Nat))) : PartialMomentProblem (List Nat) :=
  ⟨factorialRectangle bounds, [], factorialRectangle_positive bounds, factorialRectangle_nodup bounds, intervals⟩

end Thesis.Probability.Distros
