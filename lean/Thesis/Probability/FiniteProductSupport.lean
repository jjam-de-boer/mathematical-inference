import Thesis.Probability.Construction

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Exact membership in restricted dependent product enumerations

An allowed local list need not contain every value of its coordinate type.
Outer masks, for example, permit only `false` off the outer forest.  The
ordinary unrestricted completeness theorem therefore cannot justify such a
list directly.  This module proves the converse of coordinate membership:
a supplied assignment is listed exactly when each supplied coordinate is.

The assignment is already Type-level data.  The proof does not select it
from a proposition, require nonempty lists, or enlarge restricted supports.
-/

/-- Each permitted coordinate puts the whole supplied assignment in the
literal dependent product list, including empty and restricted boundaries. -/
theorem enumeration_mem_of_coordinate_mem (n : Nat) (Value : Fin n -> Type u)
    (values : (index : Fin n) -> List (Value index)) (assignment : Assignment n Value)
    (listed : forall index, assignment index ∈ values index) :
    assignment ∈ enumeration n Value values := by
  induction n with
  | zero =>
      have equal : assignment = (fun index => Fin.elim0 index) :=
        funext (fun index => Fin.elim0 index)
      rw [equal]
      exact List.mem_cons_self
  | succ n inductionHypothesis =>
      let last := assignment (Fin.last n)
      let initial := fun index : Fin n => assignment index.castSucc
      have initialMember := inductionHypothesis (fun index => Value index.castSucc)
        (fun index => values index.castSucc) initial (fun index => listed index.castSucc)
      have member : extend last initial ∈
          (values (Fin.last n)).flatMap (fun final =>
            (enumeration n (fun index => Value index.castSucc)
              (fun index => values index.castSucc)).map (fun initialAssignment => extend final initialAssignment)) :=
        List.mem_flatMap_of_mem (listed (Fin.last n))
          (List.mem_map_of_mem (f := fun initialAssignment => extend last initialAssignment) initialMember)
      have equal : extend last initial = assignment := by
        funext index
        refine Fin.lastCases ?_ (fun earlier => ?_) index
        · exact extend_last last initial
        · exact extend_castSucc last initial earlier
      exact equal ▸ member

/-- A complete local-choice test, retaining repetitions and empty lists.
Duplicate-freeness of the product is a separate theorem and hypothesis. -/
theorem enumeration_mem_iff_coordinate_mem (n : Nat) (Value : Fin n -> Type u)
    (values : (index : Fin n) -> List (Value index)) (assignment : Assignment n Value) :
    assignment ∈ enumeration n Value values ↔ forall index, assignment index ∈ values index :=
  ⟨fun member index => enumeration_coordinate_mem n Value values assignment member index,
    enumeration_mem_of_coordinate_mem n Value values assignment⟩

end FiniteProduct
end Probability
end Thesis
