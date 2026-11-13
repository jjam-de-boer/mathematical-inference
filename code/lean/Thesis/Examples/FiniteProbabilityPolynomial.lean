import Thesis.Probability.FiniteProbabilityPolynomial

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteProbabilityPolynomial

open FiniteProduct RationalPolynomial Probability.FiniteProbabilityPolynomial

/-!
# A mixed-event probability is the value of its compiled polynomial

Two independent biased bits have probabilities two thirds and one quarter.
The xor event has probability seven twelfths.  Coordinate enumerations repeat
false deliberately; the compiler must deduplicate assignments rather than
counting those states repeatedly.

A second binding contains a genuine zero source cell.  An empty-source case
tests the constant event on the unique empty assignment.  These use actual
probability records and product laws, not a supplied polynomial-likelihood
correspondence or a numerical optimization answer.
-/

def first : Fin 2 := ⟨0, by decide⟩
def second : Fin 2 := ⟨1, by decide⟩
def leading : FiniteProbRecord Bool := ⟨[(false, 1), (true, 2)], 3, by decide, rfl⟩
def trailing : FiniteProbRecord Bool := ⟨[(false, 3), (true, 1)], 4, by decide, rfl⟩
def factors (index : Fin 2) : FiniteProbRecord Bool := if index = first then leading else trailing
def law : IndependentLaw (fun _ : Fin 2 => Bool) :=
  ⟨factors, record 2 (fun _ => Bool) factors, record_rectangular_probVal 2 (fun _ => Bool) factors⟩
def enumeration (_ : Fin 2) := [false, true, false]
theorem complete (_ : Fin 2) (value : Bool) : value ∈ [false, true, false] := by cases value <;> simp
def code (index : Fin 2) (value : Bool) : Fin 4 :=
  ⟨2 * index.val + (if value then 1 else 0), by have bounded := index.isLt; cases value <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega⟩
def parameters : Fin 4 → SignedRatio := fun index =>
  if index.val = 0 then ⟨1, 3, by decide⟩ else if index.val = 1 then ⟨2, 3, by decide⟩
  else if index.val = 2 then ⟨3, 4, by decide⟩ else ⟨1, 4, by decide⟩
theorem binding : forall index value, SignedRatio.Equiv (parameters (code index value))
    (cellProbability law (fun _ => inferInstance) index value).toSignedRatio := by decide +kernel
def event : Event (Fin 2 → Bool) := fun unit => Bool.xor (unit first) (unit second)
def polynomial := compile enumeration (fun _ => inferInstance) code event
theorem compiler_sound : SignedRatio.Equiv (evaluate polynomial parameters) (law.prior.probVal event).toSignedRatio :=
  compile_sound law enumeration complete (fun _ => inferInstance) code parameters binding event
theorem computed_value : SignedRatio.Equiv (evaluate polynomial parameters) ⟨7, 12, by decide⟩ := by decide +kernel

def certain : FiniteProbRecord Bool := ⟨[(false, 0), (true, 1)], 1, by decide, rfl⟩
def zeroLaw : IndependentLaw (fun _ : Fin 2 => Bool) := law.replace first certain
def zeroParameters : Fin 4 → SignedRatio := fun index =>
  if index.val = 0 then SignedRatio.zero else if index.val = 1 then SignedRatio.one
  else if index.val = 2 then ⟨3, 4, by decide⟩ else ⟨1, 4, by decide⟩
theorem zero_binding : forall index value, SignedRatio.Equiv (zeroParameters (code index value))
    (cellProbability zeroLaw (fun _ => inferInstance) index value).toSignedRatio := by decide +kernel
theorem zero_cell_sound : SignedRatio.Equiv (evaluate polynomial zeroParameters) (zeroLaw.prior.probVal event).toSignedRatio :=
  compile_sound zeroLaw enumeration complete (fun _ => inferInstance) code zeroParameters zero_binding event
theorem zero_cell_value : SignedRatio.Equiv (evaluate polynomial zeroParameters) ⟨3, 4, by decide⟩ := by decide +kernel

def emptyFactors : (index : Fin 0) → FiniteProbRecord Bool := fun index => Fin.elim0 index
def emptyLaw : IndependentLaw (fun _ : Fin 0 => Bool) :=
  ⟨emptyFactors, record 0 (fun _ => Bool) emptyFactors, record_rectangular_probVal 0 (fun _ => Bool) emptyFactors⟩
def emptyCode : (index : Fin 0) → Bool → Fin 0 := fun index => Fin.elim0 index
def emptyParameters : Fin 0 → SignedRatio := fun index => Fin.elim0 index
def emptyPolynomial := compile (fun _ : Fin 0 => [false, true]) (fun _ => inferInstance) emptyCode topEvent
theorem empty_value : SignedRatio.Equiv (evaluate emptyPolynomial emptyParameters) SignedRatio.one := by decide +kernel

end FiniteProbabilityPolynomial
end Examples
end Probability
end Thesis
