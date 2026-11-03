import Thesis.Probability.FiniteFunctionTables

namespace Thesis.Probability

/-!
# Explicit finite presentations of materialized vectors

Finite coordinate functions already have exhaustive product enumerations.
Mapping them to vectors gives actual stored coordinates, suitable for a
dynamic path table whose entries should not recompute earlier tables. The
duplicate-free presentation constructs both finite codes and their decoder;
it never selects an inverse from an abstract finiteness proposition.

An empty coordinate family still has one vector. An empty value type has
no positive-length vector. The construction retains both cases without an
inhabitedness assumption or a chosen default entry.
-/

/-- Construct stored coordinates through the constructive list constructor.
The pinned standard library's `Vector.getElem_ofFn` reaches a classical
array lemma, so its otherwise equivalent constructor/lookup proof cannot
be used under this project's transitive axiom policy. List lookup and the
list-to-array conversion retain the same computed data without that proof. -/
def vectorOfFn (values : Fin size → α) : Vector α size :=
  ⟨(List.ofFn values).toArray, by rw [List.size_toArray, List.length_ofFn]⟩

theorem getElem_vectorOfFn (values : Fin size → α) (bounded : index < size) :
    (vectorOfFn values)[index] = values ⟨index, bounded⟩ := by
  simp only [vectorOfFn, Vector.getElem_mk, List.getElem_toArray, List.getElem_ofFn]

theorem vectorOfFn_getElem (vector : Vector α size) :
    vectorOfFn (fun index : Fin size => vector[index.val]) = vector := by
  apply Vector.ext
  intro index bounded
  exact getElem_vectorOfFn _ bounded

def vectorEnumeration (size : Nat) (values : List α) : List (Vector α size) :=
  (FiniteProduct.enumeration size (fun _ => α) (fun _ => values)).map vectorOfFn

theorem mem_vectorEnumeration (size : Nat) (values : List α)
    (complete : ∀ value, value ∈ values) (vector : Vector α size) :
    vector ∈ vectorEnumeration size values := by
  apply List.mem_map.mpr
  refine ⟨fun index => vector[index], FiniteProduct.enumeration_complete _ _ _ (fun _ => complete) _, ?_⟩
  exact vectorOfFn_getElem vector

def FiniteWitness.vector [DecidableEq α] (size : Nat) (values : List α)
    (complete : ∀ value, value ∈ values) : FiniteWitness (Vector α size) :=
  FiniteWitness.ofList (deduplicate (vectorEnumeration size values))
    (fun vector => (mem_deduplicate vector _).mpr (mem_vectorEnumeration size values complete vector))
    (deduplicate_nodup _)

end Thesis.Probability
