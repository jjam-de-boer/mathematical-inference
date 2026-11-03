import Thesis.Probability.Distros.PartialMomentProblem
import Thesis.Probability.Distros.Bernoulli
import Thesis.Probability.Distros.Categorical
import Thesis.Probability.Distros.RationalPolya
import Thesis.Probability.Distros.HypergeometricUrn

/-!
# Recipes for finite node-noise laws

A recipe generates an actual rational table. An SCM may use that table as
its private-noise factor, or a modeller may supply one recipe at each parent
tuple for a local kernel. The structural mechanism and graph remain separate
model data. This module performs neither causal identification nor Bayesian
updating of an identified table.

Constraint recipes decide feasibility. Their success certificate proves
support, moments and the supplied partition equalities; it does not assert
uniqueness or select maximum entropy. Named urn recipes have their explicit
sampling/reinforcement parameters: exchangeability alone does not select a
Pólya law. Auxiliary real Gibbs optima need not be rational tables; callers
can wrap an exactly attained law or an existing certified rational candidate
as a raw recipe without changing its weights.
-/

namespace Thesis.Probability.Distros

/-- Existing named constructors, with an explicit observable relabelling.
Relabelling may aggregate outcomes, and does not require injectivity. Positive
total weights and urn admissibility are supplied before table construction. -/
inductive NamedNodeLaw (A : Type u) where
  | bernoulli (trueWeight falseWeight : Nat) (positive : 0 < falseWeight + trueWeight)
      (decode : Bool → A)
  | categorical (size : Nat) (weights : Fin size → Nat)
      (positive : 0 < Combinatorics.natSum size (finWeight weights)) (decode : Fin size → A)
  | polya (draws : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) (decode : List Nat → A)
  | rationalPolya (draws : Nat) (alphas : List QProb) (positive : 0 < (QProb.listSum alphas).num)
      (decode : List Nat → A)
  | hypergeometric (marked total draws : Nat) (within : marked ≤ total)
      (positive : 0 < Combinatorics.binom total draws) (decode : Fin (draws + 1) → A)

/-- Evaluate only existing family constructors; their probability and urn
proofs are reused rather than assumed again by the recipe interface. -/
def NamedNodeLaw.distro : NamedNodeLaw A → Distro A
  | .bernoulli t f positive decode => (bernoulliDistro t f positive).map decode
  | .categorical size weights positive decode => (categoricalDistro size weights positive).map decode
  | .polya draws alphas positive decode => (multicolourPolyaDistro draws alphas positive).map decode
  | .rationalPolya draws alphas positive decode => (rationalPolyaDistro draws alphas positive).map decode
  | .hypergeometric marked total draws within positive decode =>
      (hypergeometricFromUrn marked total draws within positive).map decode

/-- Finite support and optional moment intervals, with an optional supplied
partition of the alphabet. Equal partition labels require equal singleton
probabilities inside the grid. Labels are data, not inferred symmetries.
Empty interval lists and `none` impose no moments or orbit equalities. -/
structure NodeLawConstraints (A : Type u) where
  problem : PartialMomentProblem A
  partition : Option (A → Nat) := none

namespace NodeLawConstraints
variable [DecidableEq A]

/-- A singleton-mass equality is an exact zero expectation of a signed
indicator difference. Its coefficients may be negative; atom weights cannot. -/
def equalMass (first second : A) : MomentInterval A :=
  .exact (fun x => (if x = first then 1 else 0) - (if x = second then 1 else 0)) SignedRatio.zero

private theorem indicator_mean (law : Distro A) (cell : A) :
    SignedRatio.Equiv
      (law.rationalExpectation (fun x => (⟨if x = cell then 1 else 0, 1, by decide⟩ : SignedRatio)))
      (law.pmf cell).toSignedRatio := by
  refine SignedRatio.equiv_trans (law.rationalExpectation_congr _ _ ?_)
    (law.rationalExpectation_indicator (FiniteProbRecord.singletonEvent cell))
  intro x
  by_cases same : x = cell <;>
    simp only [same, if_true, if_false, FiniteProbRecord.singletonEvent, decide_true,
      decide_false, Bool.false_eq_true] <;> exact SignedRatio.equiv_refl _

/-- The translated interval expresses exactly the intended singleton
probability equality, including zero masses and unreduced fractions. -/
theorem equalMass_iff (first second : A) (law : Distro A) :
    (equalMass first second).LawHolds law ↔ QProb.Equiv (law.pmf first) (law.pmf second) := by
  have mean : SignedRatio.Equiv ((equalMass first second).mean law)
      (SignedRatio.sub (law.pmf first).toSignedRatio (law.pmf second).toSignedRatio) := by
    refine SignedRatio.equiv_trans (law.rationalExpectation_congr _ _ ?_)
      (SignedRatio.equiv_trans (law.rationalExpectation_sub _ _)
        (SignedRatio.add_congr (indicator_mean law first) (SignedRatio.neg_congr (indicator_mean law second))))
    intro x
    simp only [equalMass, MomentInterval.exact, SignedRatio.sub, SignedRatio.add, SignedRatio.neg,
      SignedRatio.Equiv, Nat.mul_one, Int.natCast_one, Int.mul_one]
    omega
  constructor
  · intro bounds
    have zero : SignedRatio.Equiv ((equalMass first second).mean law) SignedRatio.zero :=
      SignedRatio.equiv_of_le_of_le bounds.2 bounds.1
    exact (QProb.toSignedRatio_equiv_iff _ _).mp ((SignedRatio.sub_equiv_zero_iff _ _).mp
      (SignedRatio.equiv_trans (SignedRatio.equiv_symm mean) zero))
  · intro same
    have zero := SignedRatio.equiv_trans mean ((SignedRatio.sub_equiv_zero_iff _ _).mpr
      (QProb.toSignedRatio_congr same))
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm zero)).mp (SignedRatio.le_refl _),
      (SignedRatio.le_congr (SignedRatio.equiv_symm zero) (SignedRatio.equiv_refl _)).mp (SignedRatio.le_refl _)⟩

def pairs (spec : NodeLawConstraints A) : List (A × A) :=
  match spec.partition with
  | none => []
  | some label => spec.problem.cells.flatMap (fun x =>
      (spec.problem.cells.filter (fun y => decide (label x = label y))).map (fun y => (x, y)))

omit [DecidableEq A] in
theorem pairs_iff (spec : NodeLawConstraints A) (first second : A) :
    (first, second) ∈ spec.pairs ↔ first ∈ spec.problem.cells ∧ second ∈ spec.problem.cells ∧
      ∃ label, spec.partition = some label ∧ label first = label second := by
  cases part : spec.partition with
  | none =>
      constructor
      · intro member
        simp only [pairs, part] at member
        exact False.elim (List.not_mem_nil member)
      · rintro ⟨_, _, label, found, _⟩
        cases found
  | some label =>
      constructor
      · intro member
        simp only [pairs, part] at member
        rcases List.mem_flatMap.mp member with ⟨x, hx, listed⟩
        rcases List.mem_map.mp listed with ⟨y, selected, same⟩
        have firstSame := congrArg Prod.fst same
        have secondSame := congrArg Prod.snd same
        cases firstSame
        cases secondSame
        have filtered := List.mem_filter.mp selected
        exact ⟨hx, filtered.1, label, rfl, of_decide_eq_true filtered.2⟩
      · rintro ⟨hf, hs, supplied, found, same⟩
        have equal : label = supplied := Option.some.inj found
        cases equal
        simp only [pairs, part]
        exact List.mem_flatMap.mpr ⟨first, hf, List.mem_map.mpr
          ⟨second, List.mem_filter.mpr ⟨hs, decide_eq_true same⟩, rfl⟩⟩

/-- The original grid is retained, including forced-zero cells. The complete
rational linear solver handles orbit equations and moments together. -/
def toProblem (spec : NodeLawConstraints A) : PartialMomentProblem A :=
  { spec.problem with intervals := spec.problem.intervals ++ spec.pairs.map (fun pair => equalMass pair.1 pair.2) }

def OrbitHolds (spec : NodeLawConstraints A) (law : Distro A) : Prop :=
  ∀ label, spec.partition = some label → ∀ first ∈ spec.problem.cells, ∀ second ∈ spec.problem.cells,
    label first = label second → QProb.Equiv (law.pmf first) (law.pmf second)

def Accepts (spec : NodeLawConstraints A) (law : Distro A) : Prop :=
  law.AlmostSurely (fun x => x ∈ spec.problem.cells) ∧
    (∀ interval ∈ spec.problem.intervals, interval.LawHolds law) ∧ spec.OrbitHolds law

theorem moments_iff (spec : NodeLawConstraints A) (law : Distro A) :
    (∀ interval ∈ spec.toProblem.intervals, interval.LawHolds law) ↔
      (∀ interval ∈ spec.problem.intervals, interval.LawHolds law) ∧ spec.OrbitHolds law := by
  constructor
  · intro valid
    refine ⟨fun interval member => valid interval (List.mem_append_left _ member), ?_⟩
    intro label partition first hf second hs same
    apply (equalMass_iff first second law).mp
    exact valid _ (List.mem_append_right _ (List.mem_map.mpr
      ⟨(first, second), (spec.pairs_iff first second).mpr ⟨hf, hs, label, partition, same⟩, rfl⟩))
  · rintro ⟨moments, orbits⟩ interval member
    rcases List.mem_append.mp member with original | orbit
    · exact moments interval original
    · rcases List.mem_map.mp orbit with ⟨⟨first, second⟩, listed, rfl⟩
      rcases (spec.pairs_iff first second).mp listed with ⟨hf, hs, label, partition, same⟩
      exact (equalMass_iff first second law).mpr (orbits label partition first hf second hs same)

end NodeLawConstraints

/-- A recipe generates model data. Constraint success means certified
feasibility, with no uniqueness or maximum-entropy conclusion. -/
inductive NodeLawRecipe (A : Type u) where
  | raw (table : FiniteProbRecord A)
  | named (family : NamedNodeLaw A)
  | constraints (spec : NodeLawConstraints A)

namespace NodeLawRecipe
variable [DecidableEq A]

def ofDistro (law : Distro A) : NodeLawRecipe A := .raw law.record

def Accepts : NodeLawRecipe A → Distro A → Prop
  | .raw table, law => law.record = table
  | .named family, law => law.record = family.distro.record
  | .constraints spec, law => spec.Accepts law

/-- Every success carries the actual normalized rational record and a proof
of its recipe requirements. Failure refutes every law satisfying the recipe,
including presentations with additional zero-weight labels outside its grid. -/
inductive Result (recipe : NodeLawRecipe A) where
  | success (table : FiniteProbRecord A) (certificate : recipe.Accepts ⟨table⟩)
  | infeasible (refutation : ¬ ∃ law, recipe.Accepts law)

/-- Constructive compilation through the existing complete feasibility
solver. Infeasibility cannot be converted into a default or completed table. -/
def compile (recipe : NodeLawRecipe A) : recipe.Result :=
  match recipe with
  | .raw table => .success table rfl
  | .named family => .success family.distro.record rfl
  | .constraints spec =>
      match spec.toProblem.solve with
      | .feasible law => .success law.distro.record
          ⟨law.support, (spec.moments_iff law.distro).mp law.moments⟩
      | .infeasible certificate => .infeasible (by
          rintro ⟨law, support, moments, orbits⟩
          exact spec.toProblem.refutation_not_realizable certificate
            ⟨law, support, (spec.moments_iff law).mpr ⟨moments, orbits⟩⟩)

def Result.table? {recipe : NodeLawRecipe A} : recipe.Result → Option (FiniteProbRecord A)
  | .success table _ => some table
  | .infeasible _ => none

def Result.succeeded {recipe : NodeLawRecipe A} : recipe.Result → Bool
  | .success _ _ => true
  | .infeasible _ => false

/-- Extract a successful factor table under its checked success proof.
There is no fallback table in the infeasible branch. -/
def Result.table {recipe : NodeLawRecipe A} (result : recipe.Result)
    (success : result.succeeded = true) : FiniteProbRecord A :=
  match result with
  | .success table _ => table
  | .infeasible _ => False.elim (Bool.noConfusion success)

theorem Result.table_accepts {recipe : NodeLawRecipe A} (result : recipe.Result)
    (success : result.succeeded = true) : recipe.Accepts ⟨result.table success⟩ := by
  cases result with
  | success _ certificate => exact certificate
  | infeasible _ => exact False.elim (Bool.noConfusion success)

/-- Success is equivalent to realizability of the stated recipe. This is a
feasibility equivalence, not an identifiability or unique-law theorem. -/
theorem compile_success_iff (recipe : NodeLawRecipe A) :
    recipe.compile.succeeded = true ↔ ∃ law, recipe.Accepts law := by
  cases outcome : recipe.compile with
  | success table certificate => exact ⟨fun _ => ⟨⟨table⟩, certificate⟩, fun _ => rfl⟩
  | infeasible refutation => exact ⟨fun impossible => Bool.noConfusion impossible, fun witness => False.elim (refutation witness)⟩

/-- A constrained success retains a record occurrence of every declared
cell, even when its exact weight is zero. No support is silently shrunk. -/
theorem compile_retains (spec : NodeLawConstraints A) (table : FiniteProbRecord A)
    (returned : (NodeLawRecipe.constraints spec).compile.table? = some table) :
    ∀ cell ∈ spec.problem.cells, ∃ weight, (cell, weight) ∈ table.atoms := by
  unfold compile at returned
  cases outcome : spec.toProblem.solve with
  | feasible law =>
      simp only [outcome, Result.table?, Option.some.injEq] at returned
      cases returned
      exact law.retains
  | infeasible _ => simp only [outcome, Result.table?, reduceCtorEq] at returned

end NodeLawRecipe
end Thesis.Probability.Distros
