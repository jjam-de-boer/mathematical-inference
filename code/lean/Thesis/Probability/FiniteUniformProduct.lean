import Thesis.Probability.Construction
import Thesis.Probability.ConstructivePermutation
import Thesis.Probability.FiniteSignedMass

namespace Thesis
namespace Probability

/-!
# Exact unit-weight presentations of independent finite products

Pair-root channel sources group a finite Boolean matrix by root, whereas the
orthogonality proof groups the same entries by channel.  Both presentations
must be the actual independent product records.  Completeness of their support
alone would not identify their weights, multiplicities or denominators.

This module proves that a product of explicitly unit-weight factors has
exactly the unit-weight Cartesian enumeration as its atoms.  Repetition-free
coordinate lists give a repetition-free product list, by the terminal and
initial coordinates of `extend`.  An explicit permutation of these lists
then preserves arbitrary event masses and integer-valued integrals, not only
rectangular marginals.  Normalization retains the literal record denominator.

The proofs recurse on finite lists and coordinate counts.  They neither
evaluate an exponential concrete support nor select representatives, and
they do not assert a reindexing for nonuniform factors without weight data.
-/

namespace FiniteProduct

/-- Distinct initial assignments remain distinct after adjoining the same
terminal coordinate.  Equality is recovered by reading each initial slot. -/
private theorem extend_initial_injective {n : Nat} {Value : Fin (n + 1) -> Type u}
    (last : Value (Fin.last n)) :
    Function.Injective (fun initial : Assignment n (fun index => Value index.castSucc) => extend last initial) := by
  intro left right equal
  funext index
  have coordinate := congrFun equal index.castSucc
  simpa only [extend_castSucc] using coordinate

/-- A dependent Cartesian enumeration has no repetitions when its local
lists have none.  No equality of functions is decided classically: the
provided coordinate equality decisions give the finite assignment decision. -/
theorem enumeration_nodup (n : Nat) (Value : Fin n -> Type u)
    (values : (index : Fin n) -> List (Value index))
    (decEq : (index : Fin n) -> DecidableEq (Value index))
    (nodup : forall index, (values index).Nodup) :
    (enumeration n Value values).Nodup := by
  induction n with
  | zero => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | succ n inductionHypothesis =>
      letI : DecidableEq (Assignment (n + 1) Value) := assignmentDecidableEq (n + 1) Value decEq
      rw [enumeration]
      apply List.pairwise_flatMap.mpr
      constructor
      · intro last _member
        exact ConstructivePermutation.nodup_map_of_injective_on (fun initial => extend last initial)
          (enumeration n (fun index => Value index.castSucc) (fun index => values index.castSucc))
          (fun left _leftMem right _rightMem equal => extend_initial_injective last equal)
          (inductionHypothesis (fun index => Value index.castSucc) (fun index => values index.castSucc)
            (fun index => decEq index.castSucc) (fun index => nodup index.castSucc))
      · apply (nodup (Fin.last n)).imp
        intro left right different first firstMem second secondMem equal
        rcases List.mem_map.mp firstMem with ⟨initial, _member, firstEq⟩
        rcases List.mem_map.mp secondMem with ⟨other, _member, secondEq⟩
        have terminal := congrFun (firstEq.trans (equal.trans secondEq.symm)) (Fin.last n)
        exact different (by simpa only [extend_last] using terminal)

/-- Unit-weight factors give the literal unit-weight product enumeration.
This statement keeps repeated labels if they were present in a local list;
duplicate-freeness is a separate hypothesis only when a permutation needs it. -/
theorem atoms_eq_unit (n : Nat) (Value : Fin n -> Type u)
    (factors : (index : Fin n) -> FiniteProbRecord (Value index))
    (values : (index : Fin n) -> List (Value index))
    (unit : forall index, (factors index).atoms = (values index).map (fun value => (value, 1))) :
    atoms n Value factors = (enumeration n Value values).map (fun assignment => (assignment, 1)) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [atoms, unit (Fin.last n), inductionHypothesis (fun index => Value index.castSucc)
        (fun index => factors index.castSucc) (fun index => values index.castSucc)
        (fun index => unit index.castSucc)]
      simp only [FiniteProbRecord.weightedCartesian, enumeration, List.flatMap_map,
        List.map_flatMap, List.map_map, Function.comp_def, Nat.one_mul]

/-- The actual product record, rather than just its support, has these atoms. -/
theorem record_atoms_eq_unit (n : Nat) (Value : Fin n -> Type u)
    (factors : (index : Fin n) -> FiniteProbRecord (Value index))
    (values : (index : Fin n) -> List (Value index))
    (unit : forall index, (factors index).atoms = (values index).map (fun value => (value, 1))) :
    (record n Value factors).atoms = (enumeration n Value values).map (fun assignment => (assignment, 1)) :=
  atoms_eq_unit n Value factors values unit

/-- Unit weights identify the literal denominator with the product list's
length.  This follows from the actual record's normalization, not from an
assumed equality of cardinalities or a cancelled probability fraction. -/
theorem record_den_eq_length (n : Nat) (Value : Fin n -> Type u)
    (factors : (index : Fin n) -> FiniteProbRecord (Value index))
    (values : (index : Fin n) -> List (Value index))
    (unit : forall index, (factors index).atoms = (values index).map (fun value => (value, 1))) :
    (record n Value factors).den = (enumeration n Value values).length := by
  have normalized := (record n Value factors).total_mass
  rw [record_atoms_eq_unit n Value factors values unit, FiniteProbRecord.totalMass_unit] at normalized
  exact normalized.symm

end FiniteProduct

namespace FiniteProbRecord

/-- A complete repetition-free unit support assigns literal numerator one
to each of its listed values.  This is the source density needed by the CPT
likelihood; positivity alone would not determine that numerator. -/
theorem eventMass_unit_singleton [DecidableEq Ω] (values : List Ω) (nodup : values.Nodup)
    (value : Ω) (member : value ∈ values) :
    eventMass (values.map (fun sample => (sample, 1))) (singletonEvent value) = 1 := by
  rw [eventMass_unit]
  have predicate : singletonEvent value = (fun candidate => candidate == value) := by
    funext candidate
    apply Bool.eq_iff_iff.mpr
    simp only [singletonEvent, decide_eq_true_eq, beq_iff_eq]
  rw [predicate]
  change List.count value values = 1
  rw [nodup.count, if_pos member]

/-- An explicit permutation of unit supports preserves every event mass
under the displayed relabelling, including mixed events between coordinates. -/
theorem eventMass_unit_reindex (left : List Ω) (right : List X) (forward : Ω -> X)
    (permutation : (left.map forward).Perm right) (event : Event X) :
    eventMass (left.map (fun value => (value, 1))) (fun value => event (forward value)) =
      eventMass (right.map (fun value => (value, 1))) event := by
  rw [eventMass_unit, eventMass_unit, count, count, List.countP_eq_length_filter, List.countP_eq_length_filter]
  have filtered := (permutation.filter event).length_eq
  rw [List.filter_map, List.length_map] at filtered
  exact filtered

private theorem int_sum_perm {left right : List Int} (permutation : left.Perm right) : left.sum = right.sum := by
  induction permutation with
  | nil => rfl
  | cons value _ inductionHypothesis => simp only [List.sum_cons, inductionHypothesis]
  | swap left right rest => exact Int.add_left_comm _ _ _
  | trans _ _ leftEqual rightEqual => exact leftEqual.trans rightEqual

/-- The same support permutation preserves any integer-valued integrand.
Negative characters remain auxiliary functions over ordinary unit weights. -/
theorem signedAtomMass_unit_reindex (left : List Ω) (right : List X) (forward : Ω -> X)
    (permutation : (left.map forward).Perm right) (integrand : X -> Int) :
    signedAtomMass (left.map (fun value => (value, 1))) (fun value => integrand (forward value)) =
      signedAtomMass (right.map (fun value => (value, 1))) integrand := by
  have sums := int_sum_perm (permutation.map integrand)
  simpa only [signedAtomMass, List.map_map, Function.comp_def, Int.natCast_one, Int.one_mul] using sums

end FiniteProbRecord
end Probability
end Thesis
