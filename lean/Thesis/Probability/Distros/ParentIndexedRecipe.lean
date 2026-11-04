import Thesis.Probability.Distros.NodeLawRecipe
import Thesis.Probability.Distros.Categorical

/-!
# Parent-indexed kernel recipes

A local kernel is a family of child tables, one recipe at each listed parent
tuple. Compilation succeeds only when every tuple is realizable. A failed
tuple yields a refutation, not a default CPT row. Parent lists are data;
orbits and symmetries are not inferred from samples. Maximum entropy is not
installed by compilation.
-/

namespace Thesis.Probability.Distros

open Combinatorics

/-- Finite parent alphabet together with a child-law recipe at each tuple. -/
structure ParentIndexedRecipe (Parent Child : Type u) where
  parents : List Parent
  parents_nodup : parents.Nodup
  recipe : Parent → NodeLawRecipe Child

namespace ParentIndexedRecipe
variable {Parent Child : Type u} [DecidableEq Child]

/-- First listed parent whose recipe fails, if any. -/
structure FailedParent (recipe : Parent → NodeLawRecipe Child)
    (parents : List Parent) where
  parent : Parent
  listed : parent ∈ parents
  failed : (recipe parent).compile.succeeded = false

def findFailure (recipe : Parent → NodeLawRecipe Child) :
    (parents : List Parent) → Option (FailedParent recipe parents)
  | [] => none
  | p :: rest =>
      if h : (recipe p).compile.succeeded = false then
        some {
          parent := p
          listed := List.mem_cons.mpr (Or.inl rfl)
          failed := h }
      else
        match findFailure recipe rest with
        | none => none
        | some q =>
            some {
              parent := q.parent
              listed := List.mem_cons.mpr (Or.inr q.listed)
              failed := q.failed }

theorem findFailure_eq_none_iff (recipe : Parent → NodeLawRecipe Child) :
    ∀ parents,
      findFailure recipe parents = none ↔
        parents.all (fun p => (recipe p).compile.succeeded) = true
  | [] => by simp [findFailure]
  | p :: rest => by
      cases hp : (recipe p).compile.succeeded
      · simp [findFailure, hp, List.all_cons]
      · have notFalse : ¬ (recipe p).compile.succeeded = false := by
          simp [hp]
        simp only [findFailure, notFalse, List.all_cons, Bool.true_and]
        constructor
        · intro hnone
          cases hf : findFailure recipe rest with
          | none => exact (findFailure_eq_none_iff recipe rest).mp hf
          | some _ => simp [hf] at hnone
        · intro hall
          have hf : findFailure recipe rest = none :=
            (findFailure_eq_none_iff recipe rest).mpr hall
          simp [hf]

def allSucceeded (spec : ParentIndexedRecipe Parent Child) : Bool :=
  spec.parents.all fun p => (spec.recipe p).compile.succeeded

theorem allSucceeded_iff (spec : ParentIndexedRecipe Parent Child) :
    spec.allSucceeded = true ↔
      ∀ p ∈ spec.parents, (spec.recipe p).compile.succeeded = true :=
  List.all_eq_true

/-- Successful kernel: every listed parent has a compiled child table. -/
structure KernelTable (spec : ParentIndexedRecipe Parent Child) where
  row : (parent : Parent) → parent ∈ spec.parents → FiniteProbRecord Child
  succeeded :
    ∀ parent ∈ spec.parents, (spec.recipe parent).compile.succeeded = true
  row_eq :
    ∀ parent listed,
      row parent listed =
        (spec.recipe parent).compile.table (succeeded parent listed)

namespace KernelTable
variable {spec : ParentIndexedRecipe Parent Child}

theorem row_accepts (kernel : KernelTable spec) (parent : Parent)
    (listed : parent ∈ spec.parents) :
    (spec.recipe parent).Accepts ⟨kernel.row parent listed⟩ := by
  rw [kernel.row_eq parent listed]
  exact (spec.recipe parent).compile.table_accepts (kernel.succeeded parent listed)

/-- Unlisted parents have no row; the kernel does not invent one. -/
def row? [DecidableEq Parent] (kernel : KernelTable spec) (parent : Parent) :
    Option (FiniteProbRecord Child) :=
  if h : parent ∈ spec.parents then some (kernel.row parent h) else none

theorem row?_none_of_unlisted [DecidableEq Parent]
    (kernel : KernelTable spec) (parent : Parent)
    (missing : parent ∉ spec.parents) : kernel.row? parent = none := by
  simp [row?, missing]

def prob (kernel : KernelTable spec) (parent : Parent)
    (listed : parent ∈ spec.parents) (child : Child) : QProb :=
  (kernel.row parent listed).probVal (FiniteProbRecord.singletonEvent child)

/-- Constraint rows retain every declared cell, including zeros. -/
theorem retains (kernel : KernelTable spec) (parent : Parent)
    (listed : parent ∈ spec.parents) (specConstraints : NodeLawConstraints Child)
    (isConstraints : spec.recipe parent = .constraints specConstraints)
    (cell : Child) (inGrid : cell ∈ specConstraints.problem.cells) :
    ∃ weight, (cell, weight) ∈ (kernel.row parent listed).atoms := by
  refine NodeLawRecipe.compile_retains specConstraints (kernel.row parent listed) ?_
    cell inGrid
  rw [← congrArg (fun r : NodeLawRecipe Child => r.compile.table?) isConstraints]
  rw [kernel.row_eq parent listed]
  exact NodeLawRecipe.Result.table?_eq_some_table _
    (kernel.succeeded parent listed)

end KernelTable

/-- Family compilation: a full kernel, or a concrete failed tuple. -/
inductive KernelResult (spec : ParentIndexedRecipe Parent Child) where
  | success (kernel : KernelTable spec)
  | infeasible (parent : Parent) (listed : parent ∈ spec.parents)
      (failed : (spec.recipe parent).compile.succeeded = false)

namespace KernelResult
variable {spec : ParentIndexedRecipe Parent Child}

def succeeded : KernelResult spec → Bool
  | .success _ => true
  | .infeasible _ _ _ => false

def kernel? : KernelResult spec → Option (KernelTable spec)
  | .success kernel => some kernel
  | .infeasible _ _ _ => none

def kernel (result : KernelResult spec) (ok : result.succeeded = true) :
    KernelTable spec :=
  match result with
  | .success kernel => kernel
  | .infeasible _ _ _ => False.elim (Bool.noConfusion ok)

theorem kernel?_none_of_not_succeeded (result : KernelResult spec)
    (failed : result.succeeded = false) : result.kernel? = none := by
  cases result with
  | success _ => exact Bool.noConfusion failed
  | infeasible _ _ _ => rfl

end KernelResult

def getFailure (spec : ParentIndexedRecipe Parent Child)
    (hall : spec.allSucceeded = false) :
    FailedParent spec.recipe spec.parents :=
  match hf : findFailure spec.recipe spec.parents with
  | some fail => fail
  | none =>
      False.elim (Bool.noConfusion
        (((findFailure_eq_none_iff spec.recipe spec.parents).mp hf).symm.trans hall))

/-- Compile every listed tuple. Infeasibility is not rewritten into a table. -/
def compileKernel (spec : ParentIndexedRecipe Parent Child) :
    KernelResult spec :=
  if h : spec.allSucceeded = true then
    .success {
      row := fun parent listed =>
        (spec.recipe parent).compile.table ((spec.allSucceeded_iff.mp h) parent listed)
      succeeded := fun parent listed => (spec.allSucceeded_iff.mp h) parent listed
      row_eq := fun _ _ => rfl }
  else
    let fail := getFailure spec (by
      cases ht : spec.allSucceeded with
      | true => exact (h ht).elim
      | false => rfl)
    .infeasible fail.parent fail.listed fail.failed

theorem compileKernel_succeeded_eq_all (spec : ParentIndexedRecipe Parent Child) :
    spec.compileKernel.succeeded = spec.allSucceeded := by
  cases h : spec.allSucceeded with
  | true => simp [compileKernel, h, KernelResult.succeeded]
  | false => simp [compileKernel, h, KernelResult.succeeded]

theorem compileKernel_success_iff (spec : ParentIndexedRecipe Parent Child) :
    spec.compileKernel.succeeded = true ↔
      ∀ parent ∈ spec.parents, ∃ law, (spec.recipe parent).Accepts law := by
  rw [compileKernel_succeeded_eq_all, spec.allSucceeded_iff]
  constructor
  · intro hall parent listed
    exact (NodeLawRecipe.compile_success_iff (spec.recipe parent)).mp
      (hall parent listed)
  · intro realizable parent listed
    exact (NodeLawRecipe.compile_success_iff (spec.recipe parent)).mpr
      (realizable parent listed)

/-- A failed tuple has no compiled child table, hence no default CPT row. -/
theorem compileKernel_failed_no_table (spec : ParentIndexedRecipe Parent Child)
    (parent : Parent) (listed : parent ∈ spec.parents)
    (failed : (spec.recipe parent).compile.succeeded = false)
    (outcome : spec.compileKernel = .infeasible parent listed failed) :
    spec.compileKernel.kernel? = none ∧
      (spec.recipe parent).compile.table? = none :=
  ⟨by simp [KernelResult.kernel?, outcome],
    NodeLawRecipe.Result.table?_none_of_not_succeeded _ failed⟩

theorem compileKernel_infeasible_of_failed (spec : ParentIndexedRecipe Parent Child)
    (parent : Parent) (listed : parent ∈ spec.parents)
    (failed : (spec.recipe parent).compile.succeeded = false) :
    spec.compileKernel.succeeded = false := by
  have hall : spec.allSucceeded = false := by
    cases h : spec.allSucceeded with
    | true =>
        have : (spec.recipe parent).compile.succeeded = true :=
          (spec.allSucceeded_iff.mp h) parent listed
        exact Bool.noConfusion (failed.symm.trans this)
    | false => rfl
  rw [compileKernel_succeeded_eq_all, hall]

/-- Inverse-CDF index into the unit-cell expansion. Zeros stay as zero-length
blocks; the denominator is never used as a `0/0` fallback. -/
def unitAt (table : FiniteProbRecord Child) (i : Fin table.den) : Child :=
  (FiniteProbRecord.expand table.atoms).get ⟨i.val, by
    simp [FiniteProbRecord.length_expand, table.total_mass]⟩

def unitAtNat (table : FiniteProbRecord Child) (u : Nat) : Child :=
  unitAt table ⟨u % table.den, Nat.mod_lt u table.den_pos⟩

omit [DecidableEq Child] in
private theorem countP_eq_natSum_get (xs : List Child) (event : Event Child) :
    xs.countP event =
      natSum xs.length (fun i =>
        if h : i < xs.length then
          if event (xs.get ⟨i, h⟩) then 1 else 0
        else 0) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.countP_cons, List.length_cons]
      rw [natSum_head]
      have head :
          (if h : 0 < rest.length + 1 then
            if event ((x :: rest).get ⟨0, h⟩) then 1 else 0
          else 0) = (if event x then 1 else 0) := by
        simp
      have tail :
          natSum rest.length (fun i =>
              if h : i + 1 < rest.length + 1 then
                if event ((x :: rest).get ⟨i + 1, h⟩) then 1 else 0
              else 0) =
            rest.countP event := by
        rw [ih]
        apply natSum_congr
        intro i hi
        have hsucc : i + 1 < rest.length + 1 := Nat.succ_lt_succ hi
        simp [hi, hsucc]
      rw [head, tail, Nat.add_comm]

omit [DecidableEq Child] in
private theorem countP_eq_natSum_of_length (xs : List Child) (event : Event Child)
    (n : Nat) (hn : xs.length = n) :
    xs.countP event =
      natSum n (fun i =>
        if h : i < n then
          if event (xs.get ⟨i, (hn.symm ▸ h)⟩) then 1 else 0
        else 0) := by
  cases hn
  exact countP_eq_natSum_get xs event

omit [DecidableEq Child] in
/-- Uniform inverse-CDF sampling realizes the compiled row on every event,
including zero-mass cells. -/
theorem realizedRow_probVal (table : FiniteProbRecord Child)
    (event : Event Child) :
    QProb.Equiv
      (((discreteUniformDistro table.den table.den_pos).map (unitAt table)).record.probVal event)
      (table.probVal event) := by
  refine QProb.equiv_trans
    (FiniteProbRecord.map_probVal
      (discreteUniformDistro table.den table.den_pos).record (unitAt table) event) ?_
  have denEq :
      (discreteUniformDistro table.den table.den_pos).record.den = table.den :=
    discreteUniform_den table.den table.den_pos
  have mass :
      FiniteProbRecord.eventMass
          (discreteUniformDistro table.den table.den_pos).record.atoms
          (fun i => event (unitAt table i)) =
        (table.probVal event).num := by
    have expanded :
        FiniteProbRecord.eventMass
            (finWeighted table.den (fun _ => 1))
            (fun i => event (unitAt table i)) =
          natSum table.den (fun i =>
            if h : i < table.den then
              if event (unitAt table ⟨i, h⟩) then 1 else 0
            else 0) :=
      eventMass_finWeighted table.den (fun _ => 1) (fun i => event (unitAt table i))
    have counted :
        natSum table.den (fun i =>
            if h : i < table.den then
              if event (unitAt table ⟨i, h⟩) then 1 else 0
            else 0) =
          (FiniteProbRecord.expand table.atoms).countP event := by
      have hlen :
          (FiniteProbRecord.expand table.atoms).length = table.den :=
        (FiniteProbRecord.length_expand table.atoms).trans table.total_mass
      have pull :=
        countP_eq_natSum_of_length (FiniteProbRecord.expand table.atoms) event
          table.den hlen
      refine Eq.trans ?_ pull.symm
      apply natSum_congr
      intro i hi
      simp [hi, unitAt]
    have hrec :
        (discreteUniformDistro table.den table.den_pos).record.atoms =
          finWeighted table.den (fun _ => 1) := by
      simp [discreteUniformDistro, categoricalDistro, ofFinWeights]
    rw [hrec, expanded, counted]
    simp [FiniteProbRecord.probVal]
    exact FiniteProbRecord.count_expand table.atoms event
  simp [FiniteProbRecord.probVal, QProb.Equiv, denEq, mass]

end ParentIndexedRecipe
end Thesis.Probability.Distros
