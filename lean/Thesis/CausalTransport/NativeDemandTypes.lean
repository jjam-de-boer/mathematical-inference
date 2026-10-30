import Thesis.CausalTransport.NativeSupportGuard
import Thesis.Probability.FiniteFunctionTables

namespace Thesis.Causality.NativeDemandTyping

open Probability ProbabilityResult

/-!
# Finite term types indexed by the references actually demanded

A cell retains both its causal-profile index and its complete declared
reference. A demand mask says which cells must be checked. A successful
type records zero or positive there and `unused` elsewhere; unused is not
a probability zero and supplies no support witness.

The structural checker moves demands through the expression constructors.
Marginalization requests every substituted reference, fixed evaluation
requests its fixed reference, and a weighted factor is requested precisely
where its weight is positive. The weight itself must always be defined.
Division additionally requires a positive denominator. Kernel leaves read
the actual profile models; composite arithmetic uses only finite statuses.

The exactness theorem compares this checker with the native evaluator at
every demanded cell. The explicit type catalogue proves finiteness without
bounding term size, choosing a representative proof, or merging endpoints
that merely have the same type. No rewrite solver or stopping theorem is
introduced, and an empty profile list alone certifies no original model.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

abbrev Demand (profiles : List (NativeTemplateInstance P)) := Fin profiles.length → S.Assignment → Bool

inductive Grade where
  | unused
  | zero
  | positive
  deriving DecidableEq, Repr

abbrev TermType (profiles : List (NativeTemplateInstance P)) := Fin profiles.length → S.Assignment → Grade

def allNeeded (profiles : List (NativeTemplateInstance P)) (demand test : Demand profiles) : Bool :=
  finAll profiles.length (fun index => S.assignmentEnumeration.all (fun reference =>
    !demand index reference || test index reference))

theorem allNeeded_exact (profiles : List (NativeTemplateInstance P)) (demand test : Demand profiles) :
    allNeeded profiles demand test = true ↔ ∀ index reference, demand index reference = true → test index reference = true := by
  simp only [allNeeded, finAll_eq_true_iff, List.all_eq_true]
  constructor
  · intro checked index reference needed
    have tested := checked index reference (S.assignmentEnumeration_complete reference)
    simpa only [needed, Bool.not_true, Bool.false_or] using tested
  · intro checked index reference _listed
    cases needed : demand index reference with
    | false => rfl
    | true => simpa only [Bool.not_true, Bool.false_or] using checked index reference needed

theorem allNeeded_true (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles) :
    allNeeded profiles demand (fun _ _ => true) = true :=
  (allNeeded_exact ..).mpr (fun _ _ _ => rfl)

theorem allNeeded_and (profiles : List (NativeTemplateInstance P)) (demand first second : Demand profiles) :
    allNeeded profiles demand (fun index reference => first index reference && second index reference) =
      (allNeeded profiles demand first && allNeeded profiles demand second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [allNeeded_exact, Bool.and_eq_true_iff]
  constructor
  · intro checked
    exact ⟨fun index reference needed => (checked index reference needed).1,
      fun index reference needed => (checked index reference needed).2⟩
  · rintro ⟨first, second⟩ index reference needed
    exact ⟨first index reference needed, second index reference needed⟩

/-- Pull a demand back through every marginal substitution. The existential
is implemented by finite `any`, including substitutions at null values. -/
def marginalDemand (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles) (nodes : NodeSet S) : Demand profiles :=
  fun index variant => S.assignmentEnumeration.any (fun reference =>
    demand index reference && decide (variant ∈ ProbabilityTerm.marginalAssignments S nodes reference))

theorem marginalDemand_exact (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles) (nodes : NodeSet S)
    (index : Fin profiles.length) (variant : S.Assignment) :
    marginalDemand profiles demand nodes index variant = true ↔
      ∃ reference, demand index reference = true ∧ variant ∈ ProbabilityTerm.marginalAssignments S nodes reference := by
  simp only [marginalDemand, List.any_eq_true, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨reference, _listed, needed, member⟩
    exact ⟨reference, needed, member⟩
  · rintro ⟨reference, needed, member⟩
    exact ⟨reference, S.assignmentEnumeration_complete reference, needed, member⟩

theorem allNeeded_marginal (profiles : List (NativeTemplateInstance P)) (demand test : Demand profiles) (nodes : NodeSet S) :
    allNeeded profiles demand (fun index reference =>
      (ProbabilityTerm.marginalAssignments S nodes reference).all (test index)) =
        allNeeded profiles (marginalDemand profiles demand nodes) test := by
  apply Bool.eq_iff_iff.mpr
  simp only [allNeeded_exact, List.all_eq_true]
  constructor
  · intro checked index variant needed
    rcases (marginalDemand_exact ..).mp needed with ⟨reference, requested, member⟩
    exact checked index reference requested variant member
  · intro checked index reference needed variant member
    exact checked index variant ((marginalDemand_exact ..).mpr ⟨reference, needed, member⟩)

def fixedDemand (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles) (fixed : S.Assignment) : Demand profiles :=
  fun index reference => decide (reference = fixed) && S.assignmentEnumeration.any (demand index)

theorem allNeeded_fixed (profiles : List (NativeTemplateInstance P)) (demand test : Demand profiles) (fixed : S.Assignment) :
    allNeeded profiles demand (fun index _ => test index fixed) = allNeeded profiles (fixedDemand profiles demand fixed) test := by
  apply Bool.eq_iff_iff.mpr
  simp only [allNeeded_exact]
  constructor
  · intro checked index reference needed
    have both := Bool.and_eq_true_iff.mp needed
    have same : reference = fixed := of_decide_eq_true both.1
    rcases List.any_eq_true.mp both.2 with ⟨original, _listed, requested⟩
    subst reference
    exact checked index original requested
  · intro checked index reference needed
    apply checked index fixed
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl,
      List.any_eq_true.mpr ⟨reference, S.assignmentEnumeration_complete reference, needed⟩⟩

def positiveDemand (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    (status : Fin profiles.length → S.Assignment → ProbabilityResult.Status) : Demand profiles :=
  fun index reference => demand index reference && decide (status index reference = .positive)

theorem allNeeded_positive (profiles : List (NativeTemplateInstance P)) (demand test : Demand profiles)
    (status : Fin profiles.length → S.Assignment → ProbabilityResult.Status) :
    allNeeded profiles demand (fun index reference => if status index reference = .positive then test index reference else true) =
      allNeeded profiles (positiveDemand profiles demand status) test := by
  apply Bool.eq_iff_iff.mpr
  simp only [allNeeded_exact]
  constructor
  · intro checked index reference needed
    have both := Bool.and_eq_true_iff.mp needed
    simpa only [if_pos (of_decide_eq_true both.2)] using checked index reference both.1
  · intro checked index reference needed
    split
    next positive => exact checked index reference (Bool.and_eq_true_iff.mpr ⟨needed, decide_eq_true positive⟩)
    next => rfl

/-- Composite types use only the three-state arithmetic. Numerical native
evaluation appears solely in the finite kernel-leaf table. -/
def termStatus (profiles : List (NativeTemplateInstance P)) : ProbabilityTerm S → Fin profiles.length → S.Assignment → ProbabilityResult.Status
  | .zero, _, _ => .zero
  | .kernel kernel, index, reference => status ((profiles.get index).model.kernelDenote kernel reference)
  | .marginalize nodes inner, index, reference =>
      ProbabilityResult.Status.sum ((ProbabilityTerm.marginalAssignments S nodes reference).map (termStatus profiles inner index))
  | .evaluateAt fixed inner, index, _ => termStatus profiles inner index fixed
  | .add first second, index, reference => ProbabilityResult.Status.add (termStatus profiles first index reference) (termStatus profiles second index reference)
  | .multiply first second, index, reference => ProbabilityResult.Status.multiply (termStatus profiles first index reference) (termStatus profiles second index reference)
  | .weightedMultiply weight factor, index, reference => ProbabilityResult.Status.weightedMultiply (termStatus profiles weight index reference) (termStatus profiles factor index reference)
  | .divide numerator denominator, index, reference => ProbabilityResult.Status.divide (termStatus profiles numerator index reference) (termStatus profiles denominator index reference)

theorem termStatus_exact (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (index : Fin profiles.length)
    (reference : S.Assignment) : termStatus profiles term index reference = status ((profiles.get index).model.termDenote term reference) := by
  induction term generalizing reference with
  | zero => rfl
  | kernel => rfl
  | marginalize nodes inner ih =>
      simp only [termStatus, FiniteHiddenDAGSCM.termDenote, status_sum, List.map_map]
      exact congrArg ProbabilityResult.Status.sum (List.map_congr_left (fun variant _ => ih variant))
  | evaluateAt fixed inner ih => exact ih fixed
  | add first second firstIH secondIH => simp only [termStatus, FiniteHiddenDAGSCM.termDenote, status_add, firstIH, secondIH]
  | multiply first second firstIH secondIH => simp only [termStatus, FiniteHiddenDAGSCM.termDenote, status_multiply, firstIH, secondIH]
  | weightedMultiply weight factor weightIH factorIH => simp only [termStatus, FiniteHiddenDAGSCM.termDenote, status_weightedMultiply, weightIH, factorIH]
  | divide numerator denominator numeratorIH denominatorIH => simp only [termStatus, FiniteHiddenDAGSCM.termDenote, status_divide, numeratorIH, denominatorIH]

private theorem add_defined (first second : ProbabilityResult.Status) : (ProbabilityResult.Status.add first second).isDefined = (first.isDefined && second.isDefined) := by
  cases first <;> cases second <;> rfl
private theorem multiply_defined (first second : ProbabilityResult.Status) : (ProbabilityResult.Status.multiply first second).isDefined = (first.isDefined && second.isDefined) := by
  cases first <;> cases second <;> rfl
private theorem weighted_defined (weight factor : ProbabilityResult.Status) : (ProbabilityResult.Status.weightedMultiply weight factor).isDefined =
    (weight.isDefined && if weight = .positive then factor.isDefined else true) := by
  cases weight <;> cases factor <;> rfl
private theorem divide_defined (numerator denominator : ProbabilityResult.Status) : (ProbabilityResult.Status.divide numerator denominator).isDefined =
    ((numerator.isDefined && denominator.isDefined) && decide (denominator = .positive)) := by
  cases numerator <;> cases denominator <;> rfl
private theorem sum_defined (values : List ProbabilityResult.Status) : (ProbabilityResult.Status.sum values).isDefined = values.all ProbabilityResult.Status.isDefined := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [ProbabilityResult.Status.sum, add_defined, ih, List.all_cons]

def check (profiles : List (NativeTemplateInstance P)) : ProbabilityTerm S → Demand profiles → Bool
  | .zero, _ => true
  | .kernel kernel, demand => allNeeded profiles demand (fun index reference => (termStatus profiles (.kernel kernel) index reference).isDefined)
  | .marginalize nodes inner, demand => check profiles inner (marginalDemand profiles demand nodes)
  | .evaluateAt fixed inner, demand => check profiles inner (fixedDemand profiles demand fixed)
  | .add first second, demand => check profiles first demand && check profiles second demand
  | .multiply first second, demand => check profiles first demand && check profiles second demand
  | .weightedMultiply weight factor, demand => check profiles weight demand &&
      check profiles factor (positiveDemand profiles demand (termStatus profiles weight))
  | .divide numerator denominator, demand => (check profiles numerator demand && check profiles denominator demand) &&
      allNeeded profiles demand (fun index reference => decide (termStatus profiles denominator index reference = .positive))

theorem check_status (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles) :
    check profiles term demand = allNeeded profiles demand (fun index reference => (termStatus profiles term index reference).isDefined) := by
  induction term generalizing demand with
  | zero => exact (allNeeded_true profiles demand).symm
  | kernel => rfl
  | marginalize nodes inner ih =>
      simp only [check, termStatus, sum_defined, List.all_map, Function.comp_def, ih, allNeeded_marginal]
  | evaluateAt fixed inner ih =>
      rw [check, ih]
      exact (allNeeded_fixed profiles demand (fun index reference => (termStatus profiles inner index reference).isDefined) fixed).symm
  | add first second firstIH secondIH => simp only [check, termStatus, add_defined, firstIH, secondIH, allNeeded_and]
  | multiply first second firstIH secondIH => simp only [check, termStatus, multiply_defined, firstIH, secondIH, allNeeded_and]
  | weightedMultiply weight factor weightIH factorIH =>
      simp only [check, termStatus, weighted_defined, weightIH, factorIH, allNeeded_and, allNeeded_positive]
  | divide numerator denominator numeratorIH denominatorIH =>
      simp only [check, termStatus, divide_defined, numeratorIH, denominatorIH, allNeeded_and]

/-- Exact agreement with the native evaluator at every demanded cell. -/
theorem check_exact (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles) :
    check profiles term demand = allNeeded profiles demand (fun index reference => ((profiles.get index).model.termDenote term reference).isSome) := by
  rw [check_status]
  simp only [termStatus_exact, status_isDefined]

def typeOf (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles) : TermType profiles :=
  fun index reference => if demand index reference then
    match termStatus profiles term index reference with
    | .undefined => .unused
    | .zero => .zero
    | .positive => .positive
  else .unused

theorem typeOf_zero_iff (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles)
    (index : Fin profiles.length) (reference : S.Assignment) :
    typeOf profiles term demand index reference = .zero ↔
      demand index reference = true ∧ termStatus profiles term index reference = .zero := by
  cases needed : demand index reference <;> cases evaluated : termStatus profiles term index reference <;>
    simp only [typeOf, needed, evaluated, Bool.false_eq_true, if_false, if_true, reduceCtorEq, false_and, true_and]

theorem typeOf_positive_iff (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles)
    (index : Fin profiles.length) (reference : S.Assignment) :
    typeOf profiles term demand index reference = .positive ↔
      demand index reference = true ∧ termStatus profiles term index reference = .positive := by
  cases needed : demand index reference <;> cases evaluated : termStatus profiles term index reference <;>
    simp only [typeOf, needed, evaluated, Bool.false_eq_true, if_false, if_true, reduceCtorEq, false_and, true_and]

def infer (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles) : Option (TermType profiles) :=
  if check profiles term demand then some (typeOf profiles term demand) else none

theorem infer_isSome (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles) :
    (infer profiles term demand).isSome = check profiles term demand := by
  cases checked : check profiles term demand <;> simp only [infer, checked, Bool.false_eq_true, if_false, if_true, Option.isSome_none, Option.isSome_some]

/-- An accepted type marks exactly the demanded cells. Undefined demanded
terms cannot acquire the `unused` grade by passing inference. -/
theorem typeOf_unused_iff (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (demand : Demand profiles)
    (accepted : check profiles term demand = true) (index : Fin profiles.length) (reference : S.Assignment) :
    typeOf profiles term demand index reference = .unused ↔ demand index reference = false := by
  cases needed : demand index reference with
  | false => simp only [typeOf, needed, Bool.false_eq_true, if_false]
  | true =>
      have defined := (allNeeded_exact profiles demand _).mp ((check_status profiles term demand).symm.trans accepted) index reference needed
      cases evaluated : termStatus profiles term index reference <;>
        simp only [typeOf, needed, if_true, evaluated, ProbabilityResult.Status.isDefined, Bool.false_eq_true, reduceCtorEq] at defined ⊢

def referenceWitness (signature : ObservedSignature) : FiniteWitness signature.Assignment :=
  .ofList signature.assignmentEnumeration signature.assignmentEnumeration_complete signature.assignmentEnumeration_nodup

def referenceTypes (signature : ObservedSignature) : List (signature.Assignment → Grade) :=
  (FiniteFunctionTable.enumeration (referenceWitness signature) [.unused, .zero, .positive]).map
    (FiniteFunctionTable.lookup (referenceWitness signature))

theorem mem_referenceTypes (signature : ObservedSignature) (table : signature.Assignment → Grade) : table ∈ referenceTypes signature := by
  apply List.mem_map.mpr
  refine ⟨FiniteFunctionTable.tabulate (referenceWitness signature) table, ?_, FiniteFunctionTable.lookup_tabulate _ _⟩
  apply FiniteFunctionTable.enumeration_complete
  intro grade
  cases grade <;> simp only [List.mem_cons, true_or, or_true, reduceCtorEq]

/-- A finite catalogue of all grade tables. It depends on profile/reference
counts, not expression or proof depth. It is not a quotient of proof endpoints. -/
def typeCatalogue (profiles : List (NativeTemplateInstance P)) : List (TermType profiles) :=
  FiniteProduct.enumeration profiles.length (fun _ => S.Assignment → Grade) (fun _ => referenceTypes S)

theorem mem_typeCatalogue (profiles : List (NativeTemplateInstance P)) (table : TermType profiles) : table ∈ typeCatalogue profiles :=
  FiniteProduct.enumeration_complete _ _ _ (fun _ => mem_referenceTypes S) table

end Thesis.Causality.NativeDemandTyping
