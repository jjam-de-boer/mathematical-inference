import Thesis.Probability.Distros.ParentIndexedRecipe
import Thesis.Probability.FiniteFunctionTables
import Thesis.Causality.Reductions

/-!
# Local kernels as Markovian SCM mechanisms

A compiled `KernelTable` is the probabilistic content of
`P(child | parents = pa)` at listed parent tuples. Installing those rows as
private response-function seeds yields a Markovian `FiniteLatentSCM`. If any
graph parent configuration is missing from the table, there is no model and
no invented CPT row. Maximum entropy is not selected here; identification is
not invoked.
-/

namespace Thesis
namespace Causality

open Probability Probability.Distros FiniteProduct
open ParentIndexedRecipe

/-- Vacuous parent slots read the signature default; every child has such a
tuple, so a covering parent list is nonempty. -/
def defaultParents (S : ObservedSignature) (child : Fin S.count) :
    S.ParentValues child :=
  fun parent _ => S.defaultValue parent

/-- One parent slot is either a vacuous function or an enumerated parent
value. The Boolean edge test is data, not excluded middle. -/
def parentSlot (S : ObservedSignature) (child parent : Fin S.count) :
    List (S.directed parent child = true → S.Value parent) :=
  ProofFunction.enumeration (S.directed parent child = true)
    (S.valueEnumeration parent)

theorem parentSlot_complete (S : ObservedSignature)
    (child parent : Fin S.count)
    (input : S.directed parent child = true → S.Value parent) :
    input ∈ parentSlot S child parent :=
  ProofFunction.enumeration_complete _ _ (S.value_complete parent) input

/-- Every typed parent configuration of this child, including roots. -/
def parentTuples (S : ObservedSignature) (child : Fin S.count) :
    List (S.ParentValues child) :=
  enumeration S.count
    (fun parent => S.directed parent child = true → S.Value parent)
    (fun parent => parentSlot S child parent)

theorem parentTuples_complete (S : ObservedSignature) (child : Fin S.count)
    (parents : S.ParentValues child) :
    parents ∈ parentTuples S child :=
  enumeration_complete S.count _ _ (parentSlot_complete S child) parents

def parentValuesDecidableEq (S : ObservedSignature) (child : Fin S.count) :
    DecidableEq (S.ParentValues child) :=
  assignmentDecidableEq S.count
    (fun parent => S.directed parent child = true → S.Value parent)
    (fun parent => ProofFunction.decidableEq (S.directed parent child = true))

instance (S : ObservedSignature) (child : Fin S.count) :
    DecidableEq (S.ParentValues child) :=
  parentValuesDecidableEq S child

/-- True exactly when every graph parent tuple appears in the recipe list. -/
def covers (S : ObservedSignature) (child : Fin S.count)
    (spec : ParentIndexedRecipe (S.ParentValues child) (S.Value child)) : Bool :=
  (parentTuples S child).all fun pa => decide (pa ∈ spec.parents)

theorem covers_iff (S : ObservedSignature) (child : Fin S.count)
    (spec : ParentIndexedRecipe (S.ParentValues child) (S.Value child)) :
    covers S child spec = true ↔
      ∀ pa : S.ParentValues child, pa ∈ spec.parents := by
  constructor
  · intro hall pa
    exact of_decide_eq_true
      ((List.all_eq_true.mp hall) pa (parentTuples_complete S child pa))
  · intro hall
    refine List.all_eq_true.mpr ?_
    intro pa hmem
    exact decide_eq_true (hall pa)

/-- A compiled kernel together with a covering of the graph parent alphabet.
Unlisted configurations are excluded before an SCM is built. -/
structure InstalledChildKernel (S : ObservedSignature) (child : Fin S.count) where
  spec : ParentIndexedRecipe (S.ParentValues child) (S.Value child)
  kernel : KernelTable spec
  cover : ∀ pa : S.ParentValues child, pa ∈ spec.parents

namespace InstalledChildKernel

theorem parents_length_pos {S : ObservedSignature} {child : Fin S.count}
    (k : InstalledChildKernel S child) : 0 < k.spec.parents.length :=
  List.length_pos_of_mem (k.cover (defaultParents S child))

def parentWitness {S : ObservedSignature} {child : Fin S.count}
    (k : InstalledChildKernel S child) :
    FiniteWitness (S.ParentValues child) :=
  FiniteWitness.ofList k.spec.parents k.cover k.spec.parents_nodup

def rowAt {S : ObservedSignature} {child : Fin S.count}
    (k : InstalledChildKernel S child)
    (i : Fin k.spec.parents.length) : FiniteProbRecord (S.Value child) :=
  k.kernel.row (k.spec.parents.get i) (List.get_mem k.spec.parents i)

/-- Compile and cover, or `none`. A failed tuple or a missing graph parent
configuration is not rewritten into a table. -/
def tryInstall {S : ObservedSignature} (child : Fin S.count)
    (spec : ParentIndexedRecipe (S.ParentValues child) (S.Value child)) :
    Option (InstalledChildKernel S child) :=
  if hcov : covers S child spec = true then
    if hok : spec.compileKernel.succeeded = true then
      some {
        spec := spec
        kernel := spec.compileKernel.kernel hok
        cover := (covers_iff S child spec).mp hcov }
    else none
  else none

theorem tryInstall_none_of_not_covering {S : ObservedSignature}
    (child : Fin S.count)
    (spec : ParentIndexedRecipe (S.ParentValues child) (S.Value child))
    (missing : covers S child spec = false) :
    tryInstall child spec = none := by
  simp [tryInstall, missing]

theorem tryInstall_none_of_not_compiled {S : ObservedSignature}
    (child : Fin S.count)
    (spec : ParentIndexedRecipe (S.ParentValues child) (S.Value child))
    (failed : spec.compileKernel.succeeded = false) :
    tryInstall child spec = none := by
  cases hcov : covers S child spec with
  | false => simp [tryInstall, hcov]
  | true => simp [tryInstall, hcov, failed]

theorem tryInstall_some_of {S : ObservedSignature} {child : Fin S.count}
    {spec : ParentIndexedRecipe (S.ParentValues child) (S.Value child)}
    (hcov : covers S child spec = true)
    (hok : spec.compileKernel.succeeded = true) :
    tryInstall child spec = some {
      spec := spec
      kernel := spec.compileKernel.kernel hok
      cover := (covers_iff S child spec).mp hcov } := by
  simp [tryInstall, hcov, hok]

end InstalledChildKernel

/-- Independent response-function seeds, one table coordinate per listed
parent tuple. The joint seed law is the product of the compiled rows. -/
def ofInstalled {S : ObservedSignature}
    (kernels : (child : Fin S.count) → InstalledChildKernel S child) :
    FunctionalCBN S where
  Seed := fun child =>
    Assignment (kernels child).spec.parents.length fun _ => S.Value child
  seedEnumeration := fun child =>
    enumeration (kernels child).spec.parents.length
      (fun _ => S.Value child) (fun _ => S.valueEnumeration child)
  seed_complete := fun child seed =>
    enumeration_complete (kernels child).spec.parents.length
      (fun _ => S.Value child) (fun _ => S.valueEnumeration child)
      (fun _ value => S.value_complete child value) seed
  seedDecidableEq := fun child =>
    assignmentDecidableEq (kernels child).spec.parents.length
      (fun _ => S.Value child) (fun _ => S.valueDecidableEq child)
  factor := fun child =>
    record (kernels child).spec.parents.length (fun _ => S.Value child)
      (InstalledChildKernel.rowAt (kernels child))
  prior :=
    record S.count
      (fun child =>
        Assignment (kernels child).spec.parents.length fun _ => S.Value child)
      (fun child =>
        record (kernels child).spec.parents.length (fun _ => S.Value child)
          (InstalledChildKernel.rowAt (kernels child)))
  product_law := by
    intro events
    exact record_rectangular_probVal S.count _ _ events
  mechanism := fun child parents seed =>
    seed ((kernels child).parentWitness.encode parents)

def toSCM {S : ObservedSignature}
    (kernels : (child : Fin S.count) → InstalledChildKernel S child) :
    FiniteLatentSCM S :=
  (ofInstalled kernels).toSCM

theorem toSCM_isMarkovian {S : ObservedSignature}
    (kernels : (child : Fin S.count) → InstalledChildKernel S child) :
    (toSCM kernels).IsMarkovian :=
  (ofInstalled kernels).toSCM_isMarkovian

private theorem kernel_row_eq_of_parent_eq {Parent Child : Type u}
    [DecidableEq Child] {spec : ParentIndexedRecipe Parent Child}
    (kernel : KernelTable spec) {p q : Parent}
    (hp : p ∈ spec.parents) (hq : q ∈ spec.parents) (heq : p = q) :
    kernel.row p hp = kernel.row q hq := by
  cases heq
  rfl

/-- The installed mechanism realizes the compiled row at every listed parent
tuple, zeros included. This is the local kernel, not an identification
formula. -/
theorem mechanism_realizes_row {S : ObservedSignature}
    (kernels : (child : Fin S.count) → InstalledChildKernel S child)
    (child : Fin S.count) (parents : S.ParentValues child)
    (event : S.Value child → Bool) :
    QProb.Equiv
      (((ofInstalled kernels).factor child).probVal
        (fun seed => event ((ofInstalled kernels).mechanism child parents seed)))
      (((kernels child).kernel.row parents ((kernels child).cover parents)).probVal
        event) := by
  have hcoord :=
    record_coordinate_probVal
      (kernels child).spec.parents.length (S.Value child)
      (InstalledChildKernel.rowAt (kernels child))
      ((kernels child).parentWitness.encode parents) event
  refine QProb.equiv_trans hcoord ?_
  simp only [InstalledChildKernel.rowAt]
  have hpa :
      (kernels child).spec.parents.get
          ((kernels child).parentWitness.encode parents) = parents :=
    (kernels child).parentWitness.decode_encode parents
  have hrow :=
    kernel_row_eq_of_parent_eq (kernels child).kernel
      (List.get_mem (kernels child).spec.parents
        ((kernels child).parentWitness.encode parents))
      ((kernels child).cover parents) hpa
  rw [hrow]
  exact QProb.equiv_refl _

/-- Same-orbit child labels have equal compiled mass on a constraint row. -/
theorem kernel_orbit_prob {Parent Child : Type u} [DecidableEq Child]
    {spec : ParentIndexedRecipe Parent Child} (kernel : KernelTable spec)
    (parent : Parent) (listed : parent ∈ spec.parents)
    (cstr : NodeLawConstraints Child)
    (isConstraints : spec.recipe parent = .constraints cstr)
    (label : Child → Nat) (hpart : cstr.partition = some label)
    (first second : Child)
    (hf : first ∈ cstr.problem.cells) (hs : second ∈ cstr.problem.cells)
    (same : label first = label second) :
    QProb.Equiv (kernel.prob parent listed first)
      (kernel.prob parent listed second) := by
  have accepts := kernel.row_accepts parent listed
  rw [isConstraints] at accepts
  exact accepts.2.2 label hpart first hf second hs same

/-- Installed mechanism masses of orbit-equivalent child labels agree. -/
theorem mechanism_orbit_prob {S : ObservedSignature}
    (kernels : (child : Fin S.count) → InstalledChildKernel S child)
    (child : Fin S.count) (parents : S.ParentValues child)
    (cstr : NodeLawConstraints (S.Value child))
    (isConstraints :
      (kernels child).spec.recipe parents = .constraints cstr)
    (label : S.Value child → Nat) (hpart : cstr.partition = some label)
    (first second : S.Value child)
    (hf : first ∈ cstr.problem.cells) (hs : second ∈ cstr.problem.cells)
    (same : label first = label second) :
    QProb.Equiv
      (((ofInstalled kernels).factor child).probVal
        (fun seed =>
          FiniteProbRecord.singletonEvent first
            ((ofInstalled kernels).mechanism child parents seed)))
      (((ofInstalled kernels).factor child).probVal
        (fun seed =>
          FiniteProbRecord.singletonEvent second
            ((ofInstalled kernels).mechanism child parents seed))) := by
  refine QProb.equiv_trans
    (mechanism_realizes_row kernels child parents
      (FiniteProbRecord.singletonEvent first)) ?_
  refine QProb.equiv_trans
    (kernel_orbit_prob (kernels child).kernel parents
      ((kernels child).cover parents) cstr isConstraints label hpart
      first second hf hs same) ?_
  exact QProb.equiv_symm
    (mechanism_realizes_row kernels child parents
      (FiniteProbRecord.singletonEvent second))

end Causality
end Thesis
