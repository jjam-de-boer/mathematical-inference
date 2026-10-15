import Thesis.Probability.FiniteProductSourceCompression

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteProductSourceCompression

open FiniteProduct Probability.FiniteProductSourceCompression

/-!
# Iterated source compression preserves a genuinely mixed event

Two independent natural-valued coordinates have unequal denominators and
listed zero atoms.  The event's probability is five ninths and depends on
both coordinates.  Compression bounds every factor by two positive atom
occurrences while retaining that probability and the full product law.

A repeated coordinate list checks that previously obtained bounds survive
both revisits and intervening updates.  With no queries, every factor is
compressed to a single positive atom; this is permitted because no event
value other than normalization is then requested for preservation.
-/

def first : Fin 2 := ⟨0, by decide⟩
def second : Fin 2 := ⟨1, by decide⟩
def leading : FiniteProbRecord Nat := ⟨[(0, 0), (0, 1), (1, 1), (2, 1)], 3, by decide, rfl⟩
def trailing : FiniteProbRecord Nat := ⟨[(0, 1), (1, 2), (9, 0)], 3, by decide, rfl⟩
def factors (index : Fin 2) : FiniteProbRecord Nat := if index = first then leading else trailing
def law : IndependentLaw (fun _ : Fin 2 => Nat) :=
  ⟨factors, record 2 (fun _ => Nat) factors, record_rectangular_probVal 2 (fun _ => Nat) factors⟩
def values (_ : Fin 2) : List Nat := []

/-- The original ambient type Nat is deliberately not finitely enumerated.
To use whole-law coordinate extensionality we instead supply a finite domain
for the actual fixture below.  Arbitrary ambient-type record compression is
covered separately by the lower-level rational-response examples. -/
def finiteValue (_ : Fin 2) := Fin 3
def finiteLeading : FiniteProbRecord (Fin 3) :=
  ⟨[(0, 0), (0, 1), (1, 1), (2, 1)], 3, by decide, rfl⟩
def finiteTrailing : FiniteProbRecord (Fin 3) :=
  ⟨[(0, 1), (1, 2), (2, 0)], 3, by decide, rfl⟩
def finiteFactors (index : Fin 2) : FiniteProbRecord (Fin 3) := if index = first then finiteLeading else finiteTrailing
def finiteLaw : IndependentLaw finiteValue :=
  ⟨finiteFactors, record 2 finiteValue finiteFactors, record_rectangular_probVal 2 finiteValue finiteFactors⟩
def enumeration (_ : Fin 2) := List.finRange 3
theorem complete (index : Fin 2) (value : finiteValue index) : value ∈ enumeration index := List.mem_finRange value
def event : Event (Assignment 2 finiteValue) := fun unit =>
  if (unit first).val = 0 then false else if (unit first).val = 1 then decide ((unit second).val = 1) else true
def events : Fin 1 → Event (Assignment 2 finiteValue) := fun _ => event
def reduced := compress finiteLaw enumeration complete (fun _ => inferInstance) events

theorem all_bounds (index : Fin 2) : (reduced.law.factor index).atoms.length ≤ 2 := reduced.bounded index
theorem every_weight_positive (index : Fin 2) (atom : Fin 3 × Nat) (member : atom ∈ (reduced.law.factor index).atoms) :
    0 < atom.2 := reduced.positive index atom member
theorem event_preserved : QProb.Equiv (reduced.law.prior.probVal event) (finiteLaw.prior.probVal event) := reduced.preserved 0
theorem computed_event : QProb.Equiv (reduced.law.prior.probVal event) ⟨5, 9, by decide⟩ := by decide +kernel
theorem computed_first_support : (reduced.law.factor first).atoms.length = 2 := by decide +kernel

def revisited := compressOn finiteLaw enumeration complete (fun _ => inferInstance) [first, second, first] events
theorem revisited_first_bound : (revisited.law.factor first).atoms.length ≤ 2 := revisited.bounded first (by simp)
theorem revisited_second_bound : (revisited.law.factor second).atoms.length ≤ 2 := revisited.bounded second (by simp)
theorem revisited_preserved : QProb.Equiv (revisited.law.prior.probVal event) (finiteLaw.prior.probVal event) := revisited.preserved 0

def noEvents : Fin 0 → Event (Assignment 2 finiteValue) := fun index => Fin.elim0 index
def normalizedOnly := compress finiteLaw enumeration complete (fun _ => inferInstance) noEvents
theorem no_queries_first : (normalizedOnly.law.factor first).atoms.length = 1 := by decide +kernel
theorem no_queries_second : (normalizedOnly.law.factor second).atoms.length = 1 := by decide +kernel

end FiniteProductSourceCompression
end Examples
end Probability
end Thesis
