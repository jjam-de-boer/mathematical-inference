import Thesis.Probability.FiniteSignedProduct
import Thesis.Probability.FiniteProductSupport
import Thesis.Probability.FiniteUniformProduct
import Thesis.Probability.FiniteSupportedSum

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Boolean characters projected onto a false-valued coordinate cylinder

A homogeneous XOR-linear character can have negative values at individual
assignments.  Those values must not be declared positive merely because one
distinguished assignment has positive sign.  This module instead sums the
whole character over a literal product of free Boolean coordinates and
coordinates fixed to `false`.

At a free terminal coordinate, the two character fibres either agree or
have opposite signs.  Their sum is therefore twice the earlier sum or zero.
At a fixed terminal coordinate, only the earlier sum remains.  Induction
proves nonnegativity without searching for a nonzero coefficient, selecting
an assignment from an existential proposition, or enumerating a concrete
exponential cube during elaboration.

The restricted product is also related by an explicit constructive
permutation to filtering the complete Boolean assignment enumeration.  Thus
the result applies to the actual projected event sum, not only to a proposed
replacement support.  Homogeneity matters: adding a constant `true` phase
can negate the entire sum and is deliberately not permitted by the theorem.
-/

/-! ## Literal cylinder support -/

/-- A fixed coordinate has one allowed value; a free coordinate has both.
No masking of a complete assignment list introduces repeated fixed values. -/
def falseCylinderChoices (n : Nat) (fixed : Fin n -> Bool) (index : Fin n) : List Bool :=
  if fixed index then [false] else [false, true]

/-- Complete, nonredundant assignments for the specified false cylinder. -/
def falseCylinderEnumeration (n : Nat) (fixed : Fin n -> Bool) : List (Fin n -> Bool) :=
  enumeration n (fun _ => Bool) (falseCylinderChoices n fixed)

/-- The same cylinder as a decidable event on full Boolean assignments. -/
def falseCylinder (n : Nat) (fixed : Fin n -> Bool) (assignment : Fin n -> Bool) : Bool :=
  (List.finRange n).all (fun index => if fixed index then !(assignment index) else true)

/-- The Boolean cylinder test says exactly that every designated fixed
coordinate is false; free coordinates are not tested or replaced. -/
theorem falseCylinder_eq_true_iff (n : Nat) (fixed assignment : Fin n -> Bool) :
    falseCylinder n fixed assignment = true ↔
      forall index, fixed index = true -> assignment index = false := by
  constructor
  · intro selected index atIndex
    have tested := (List.all_eq_true.mp selected) index (List.mem_finRange index)
    cases value : assignment index with
    | false => rfl
    | true =>
        simp only [atIndex, if_true, value, Bool.not_true] at tested
        cases tested
  · intro consistent
    apply List.all_eq_true.mpr
    intro index _listed
    cases atIndex : fixed index with
    | false => simp only [Bool.false_eq_true, if_false]
    | true => simp only [if_true, consistent index atIndex, Bool.not_false]

/-- Coordinate consistency is both necessary and sufficient for membership
in the literal restricted product, including the empty-coordinate boundary. -/
theorem falseCylinderEnumeration_member_iff (n : Nat) (fixed assignment : Fin n -> Bool) :
    assignment ∈ falseCylinderEnumeration n fixed ↔
      forall index, fixed index = true -> assignment index = false := by
  rw [falseCylinderEnumeration, enumeration_mem_iff_coordinate_mem]
  constructor
  · intro listed index atIndex
    have coordinate := listed index
    simpa only [falseCylinderChoices, atIndex, if_true, List.mem_singleton] using coordinate
  · intro consistent index
    cases atIndex : fixed index with
    | false => cases assignment index <;>
        simp only [falseCylinderChoices, atIndex, Bool.false_eq_true, if_false,
          List.mem_cons, List.not_mem_nil] <;> simp
    | true => simp only [falseCylinderChoices, atIndex, if_true,
        List.mem_singleton, consistent index atIndex]

/-- Restricting a coordinate to its sole false value does not repeat that
value.  Explicit local Boolean equality gives global repetition-freeness. -/
theorem falseCylinderEnumeration_nodup (n : Nat) (fixed : Fin n -> Bool) :
    (falseCylinderEnumeration n fixed).Nodup := by
  apply enumeration_nodup n (fun _ => Bool) (falseCylinderChoices n fixed)
    (fun _ => inferInstance)
  intro index
  cases selected : fixed index <;>
    simp only [falseCylinderChoices, selected, Bool.false_eq_true, if_false, if_true] <;> decide

/-- Filtering actual complete assignments lists exactly the restricted
product, once each.  The permutation proof uses only explicit finite Boolean
equality and the proved coordinate membership tests. -/
theorem falseCylinderEnumeration_perm_filter (n : Nat) (fixed : Fin n -> Bool) :
    (falseCylinderEnumeration n fixed).Perm
      ((enumeration n (fun _ => Bool) (fun _ => [false, true])).filter (falseCylinder n fixed)) := by
  letI : DecidableEq (Fin n -> Bool) := assignmentDecidableEq n (fun _ => Bool) (fun _ => inferInstance)
  apply ConstructivePermutation.perm_of_nodup_mem_iff
    _ _ (falseCylinderEnumeration_nodup n fixed)
    (List.Pairwise.filter _ (enumeration_nodup n (fun _ => Bool) (fun _ => [false, true])
      (fun _ => inferInstance) (fun _ => by change ([false, true] : List Bool).Nodup; decide)))
  intro assignment
  rw [falseCylinderEnumeration_member_iff, List.mem_filter, falseCylinder_eq_true_iff]
  constructor
  · intro consistent
    exact ⟨enumeration_complete n (fun _ => Bool) (fun _ => [false, true])
      (fun _ bit => by cases bit <;> simp) assignment, consistent⟩
  · exact fun listed => listed.2

/-! ## Coordinate-wise XOR and symbolic character summation -/

/-- Addition of Boolean assignments in their finite XOR group. -/
def xorAssignment (n : Nat) (left right : Fin n -> Bool) : Fin n -> Bool :=
  fun index => Bool.xor (left index) (right index)

private theorem extend_xor (n : Nat) (leftLast rightLast : Bool) (left right : Fin n -> Bool) :
    xorAssignment (n + 1) (extend leftLast left) (extend rightLast right) =
      extend (Bool.xor leftLast rightLast) (xorAssignment n left right) := by
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · simp only [xorAssignment, extend_last]
  · simp only [xorAssignment, extend_castSucc]

private theorem extend_false (n : Nat) :
    extend (Value := fun _ : Fin (n + 1) => Bool) false (fun _ => false) = (fun _ => false) := by
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · exact extend_last _ _
  · exact extend_castSucc _ _ earlier

private theorem sum_flatMap (values : List α) (choices : α -> List β) (term : β -> Int) :
    ((values.flatMap choices).map term).sum =
      (values.map (fun value => ((choices value).map term).sum)).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, inductionHypothesis]

private theorem sum_mul_left (values : List α) (term : α -> Int) (factor : Int) :
    (values.map (fun value => factor * term value)).sum = factor * (values.map term).sum := by
  induction values with
  | nil => exact (Int.mul_zero factor).symm
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis, Int.mul_add]

/-- Projection of a homogeneous XOR-linear phase onto a false cylinder has
a nonnegative complete character sum.  Both homogeneity and additivity are
explicit hypotheses; arbitrary parent functions cannot use this result. -/
theorem falseCylinder_characterSum_nonneg (n : Nat) (fixed : Fin n -> Bool)
    (phase : (Fin n -> Bool) -> Bool)
    (zero : phase (fun _ => false) = false)
    (additive : forall left right,
      phase (xorAssignment n left right) = Bool.xor (phase left) (phase right)) :
    0 <= ((falseCylinderEnumeration n fixed).map
      (fun assignment => FiniteProbRecord.characterSign (phase assignment))).sum := by
  induction n with
  | zero =>
      have unique : (fun index : Fin 0 => Fin.elim0 index) = (fun _ => false) :=
        funext (fun index => Fin.elim0 index)
      simp only [falseCylinderEnumeration, enumeration, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, unique, zero, FiniteProbRecord.characterSign,
        Bool.false_eq_true, if_false, Int.add_zero]
      decide
  | succ n inductionHypothesis =>
      let earlierFixed := fun index : Fin n => fixed index.castSucc
      let earlierPhase := fun assignment : Fin n -> Bool => phase (extend false assignment)
      have earlierZero : earlierPhase (fun _ => false) = false := by
        dsimp only [earlierPhase]
        rw [extend_false]
        exact zero
      have earlierAdditive : forall left right,
          earlierPhase (xorAssignment n left right) = Bool.xor (earlierPhase left) (earlierPhase right) := by
        intro left right
        exact (congrArg phase (extend_xor n false false left right).symm).trans (additive _ _)
      have earlierNonneg := inductionHypothesis earlierFixed earlierPhase earlierZero earlierAdditive
      let lastPhase := phase (extend true (fun _ : Fin n => false))
      have trueFibre : forall assignment : Fin n -> Bool,
          FiniteProbRecord.characterSign (phase (extend true assignment)) =
            FiniteProbRecord.characterSign lastPhase *
              FiniteProbRecord.characterSign (earlierPhase assignment) := by
        intro assignment
        have decomposition : extend (Value := fun _ : Fin (n + 1) => Bool) true assignment =
            xorAssignment (n + 1) (extend true (fun _ : Fin n => false)) (extend false assignment) := by
          rw [extend_xor]
          congr 1
          funext index
          exact (Bool.false_xor (assignment index)).symm
        rw [decomposition, additive, FiniteProbRecord.characterSign_xor]
      have trueSum :
          ((falseCylinderEnumeration n earlierFixed).map
            (fun assignment => FiniteProbRecord.characterSign (phase (extend true assignment)))).sum =
          FiniteProbRecord.characterSign lastPhase *
            ((falseCylinderEnumeration n earlierFixed).map
              (fun assignment => FiniteProbRecord.characterSign (earlierPhase assignment))).sum := by
        have pointwise := List.map_congr_left (l := falseCylinderEnumeration n earlierFixed)
          (fun assignment _listed => trueFibre assignment)
        exact (congrArg List.sum pointwise).trans (sum_mul_left _ _ _)
      change 0 <= (((falseCylinderChoices (n + 1) fixed (Fin.last n)).flatMap
        (fun last => (falseCylinderEnumeration n earlierFixed).map (fun initial => extend last initial))).map
          (fun assignment => FiniteProbRecord.characterSign (phase assignment))).sum
      rw [sum_flatMap]
      simp only [List.map_map, Function.comp_def]
      cases atLast : fixed (Fin.last n) with
      | true =>
          simp only [falseCylinderChoices, atLast, if_true, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Int.add_zero]
          exact earlierNonneg
      | false =>
          simp only [falseCylinderChoices, atLast, Bool.false_eq_true, if_false, List.map_cons,
            List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero, trueSum]
          cases phaseAtLast : lastPhase with
          | false =>
              simp only [FiniteProbRecord.characterSign, Bool.false_eq_true,
                if_false, Int.one_mul]
              exact Int.add_nonneg earlierNonneg earlierNonneg
          | true =>
              simp only [FiniteProbRecord.characterSign, if_true, Int.neg_mul, Int.one_mul]
              change 0 <=
                ((falseCylinderEnumeration n earlierFixed).map
                  (fun assignment => FiniteProbRecord.characterSign (earlierPhase assignment))).sum +
                -((falseCylinderEnumeration n earlierFixed).map
                  (fun assignment => FiniteProbRecord.characterSign (earlierPhase assignment))).sum
              omega

/-- The nonnegativity theorem on the actual filtered complete enumeration.
The permutation transfers the entire sum, retaining every free assignment. -/
theorem filtered_falseCylinder_characterSum_nonneg (n : Nat) (fixed : Fin n -> Bool)
    (phase : (Fin n -> Bool) -> Bool) (zero : phase (fun _ => false) = false)
    (additive : forall left right,
      phase (xorAssignment n left right) = Bool.xor (phase left) (phase right)) :
    0 <= (((enumeration n (fun _ => Bool) (fun _ => [false, true])).filter
      (falseCylinder n fixed)).map (fun assignment => FiniteProbRecord.characterSign (phase assignment))).sum := by
  have same := FiniteSupportedSum.sum_eq_of_perm
    ((falseCylinderEnumeration_perm_filter n fixed).map
      (fun assignment => FiniteProbRecord.characterSign (phase assignment)))
  rw [← same]
  exact falseCylinder_characterSum_nonneg n fixed phase zero additive

end FiniteProduct
end Probability
end Thesis
