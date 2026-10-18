import Thesis.Probability.FiniteEnumerationBounds

namespace Thesis.Probability

/-!
# Explicit finite tables and proof-indexed coordinate choices

A supplied finite witness gives actual row codes and a two-sided decoder.
Enumerate all output vectors on those codes. Tabulation and lookup are inverse
operations, so completeness ranges over every function on the stated finite
domain, not only a preselected collection of examples or computable functions.
No search through proofs or equality of arbitrary functions is required.

Native parent inputs have type `edge = true → Value`. When the edge is absent
there is exactly one such input function, even if the unused value type is
empty. Enumerating that slot as an ordinary node value would incorrectly erase
valid root rows. The explicit decidable-condition construction below retains
the vacuous function and uses only the supplied condition decision.
-/

namespace FiniteWitness

def fin (card : Nat) : FiniteWitness (Fin card) :=
  ⟨card, id, id, fun _ => rfl, fun _ => rfl⟩

/-- Decide equality by the supplied injective finite codes, without adding a
global function-equality instance or selecting representatives by choice. -/
def decidableEq (witness : FiniteWitness X) : DecidableEq X := fun left right =>
  match inferInstanceAs (Decidable (witness.encode left = witness.encode right)) with
  | isTrue equal => isTrue ((witness.decode_encode left).symm.trans
      ((congrArg witness.decode equal).trans (witness.decode_encode right)))
  | isFalse different => isFalse (fun equal => different (congrArg witness.encode equal))

def enumeration (witness : FiniteWitness X) : List X :=
  (List.finRange witness.card).map witness.decode

theorem enumeration_complete (witness : FiniteWitness X) (value : X) : value ∈ witness.enumeration :=
  List.mem_map.mpr ⟨witness.encode value, List.mem_finRange _, witness.decode_encode value⟩

/-- A product witness is constructed from decoded row pairs. Its equality
decisions also come from the original explicit witnesses. Duplicate removal
is harmless and needs no choice of an inverse for a merely surjective map. -/
def product (left : FiniteWitness X) (right : FiniteWitness Y) : FiniteWitness (X × Y) := by
  letI : DecidableEq X := left.decidableEq
  letI : DecidableEq Y := right.decidableEq
  let values := left.enumeration.flatMap (fun first => right.enumeration.map (fun second => (first, second)))
  exact FiniteWitness.ofList (deduplicate values)
    (fun pair => (mem_deduplicate pair values).mpr
      (List.mem_flatMap_of_mem (left.enumeration_complete pair.1)
        (List.mem_map_of_mem (f := fun second => (pair.1, second)) (right.enumeration_complete pair.2))))
    (deduplicate_nodup values)

end FiniteWitness

namespace ProofFunction

/-- A genuinely decidable condition is data; no general excluded middle is
used. The false branch is the unique function out of an impossible proof. -/
def enumeration (condition : Prop) [Decidable condition] (values : List X) : List (condition → X) :=
  if holds : condition then values.map (fun value _ => value)
  else [fun impossible => False.elim (holds impossible)]

theorem enumeration_complete (condition : Prop) [Decidable condition] (values : List X)
    (complete : ∀ value, value ∈ values) (function : condition → X) :
    function ∈ enumeration condition values := by
  by_cases holds : condition
  · rw [enumeration, dif_pos holds]
    exact List.mem_map.mpr ⟨function holds, complete _, funext (fun _ => rfl)⟩
  · rw [enumeration, dif_neg holds]
    exact List.mem_cons.mpr (Or.inl (funext (fun proof => False.elim (holds proof))))

/-- This special function equality decision inspects one value only when
the proof domain is inhabited; an absent parent has no values to inspect. -/
def decidableEq (condition : Prop) [Decidable condition] [DecidableEq X] : DecidableEq (condition → X) :=
  fun left right =>
    if holds : condition then
      match inferInstanceAs (Decidable (left holds = right holds)) with
      | isTrue equal => isTrue (funext (fun _ => equal))
      | isFalse different => isFalse (fun equal => different (congrFun equal holds))
    else isTrue (funext (fun impossible => False.elim (holds impossible)))

end ProofFunction

namespace FiniteFunctionTable

abbrev Table (domain : FiniteWitness X) (Y : Type v) := Fin domain.card → Y

def tabulate (domain : FiniteWitness X) (function : X → Y) : Table domain Y :=
  fun row => function (domain.decode row)

def lookup (domain : FiniteWitness X) (table : Table domain Y) : X → Y :=
  fun input => table (domain.encode input)

/-- All inputs, including null-probability inputs, recover the original
function. This is not an almost-everywhere or retained-trajectory statement. -/
theorem lookup_tabulate (domain : FiniteWitness X) (function : X → Y) :
    lookup domain (tabulate domain function) = function := by
  funext input
  exact congrArg function (domain.decode_encode input)

theorem tabulate_lookup (domain : FiniteWitness X) (table : Table domain Y) :
    tabulate domain (lookup domain table) = table := by
  funext row
  exact congrArg table (domain.encode_decode row)

def enumeration (domain : FiniteWitness X) (values : List Y) : List (Table domain Y) :=
  FiniteProduct.enumeration domain.card (fun _ => Y) (fun _ => values)

/-- Complete exhaustive search on the stated finite row and output domains.
There is still one empty table when both row and output domains are empty. -/
theorem enumeration_complete (domain : FiniteWitness X) (values : List Y)
    (complete : ∀ value, value ∈ values) (table : Table domain Y) :
    table ∈ enumeration domain values :=
  FiniteProduct.enumeration_complete _ _ _ (fun _ => complete) table

theorem tabulation_mem_enumeration (domain : FiniteWitness X) (values : List Y)
    (complete : ∀ value, value ∈ values) (function : X → Y) :
    tabulate domain function ∈ enumeration domain values :=
  enumeration_complete domain values complete _

/-- Decode all enumerated vectors to actual functions on the declared
input domain. The witness supplies an inverse, not just a surjection. -/
def functionEnumeration (domain : FiniteWitness X) (values : List Y) : List (X → Y) :=
  (enumeration domain values).map (lookup domain)

theorem functionEnumeration_complete (domain : FiniteWitness X) (values : List Y)
    (complete : ∀ value, value ∈ values) (function : X → Y) :
    function ∈ functionEnumeration domain values :=
  List.mem_map.mpr ⟨tabulate domain function, tabulation_mem_enumeration domain values complete function,
    lookup_tabulate domain function⟩

end FiniteFunctionTable
end Thesis.Probability
