import Thesis.Probability.FiniteBooleanCharacter

namespace Thesis
namespace Probability
namespace FiniteProduct
namespace BooleanBlocks

/-!
# Complete Boolean cylinders as two explicitly indexed blocks

A finite model can present its assignments as an environment followed by an
observed sample, while a character theorem uses one Boolean cube.  Merely
identifying the sizes of those supports is not enough: the integrand can mix
both blocks, and fixed observed coordinates must remain fixed exactly once.

The prefix and suffix reads below have a displayed inverse.  Their support
permutation identifies the complete false cylinder with the Cartesian product
of its two restricted blocks.  The integer sum identity therefore applies to
arbitrary mixed integrands, including likelihoods with several shared latent
inputs.  It does not assume factorization of those integrands.

All equality decisions are the existing explicit decisions for finite Boolean
assignments.  Zero-sized blocks and empty masks are included.  This module
changes only the indexing of supplied assignments: it does not create a
probability record, a new latent source, or an inverse selected using choice.
-/

/-- Read the first block without changing any of its coordinate values. -/
def leftBlock (left right : Nat) (sample : Fin (left + right) -> Bool) : Fin left -> Bool :=
  fun index => sample (index.castAdd right)

/-- Read the second block at its literal offset after the first block. -/
def rightBlock (left right : Nat) (sample : Fin (left + right) -> Bool) : Fin right -> Bool :=
  fun index => sample (Fin.natAdd left index)

/-- Assemble the two supplied blocks at their original finite indices.
The index test is decidable arithmetic, including either empty boundary. -/
def join (left right : Nat) (first : Fin left -> Bool) (second : Fin right -> Bool) :
    Fin (left + right) -> Bool :=
  fun index => if earlier : index.val < left then first ⟨index.val, earlier⟩
    else second ⟨index.val - left, by omega⟩

/-- The prefix read of the displayed inverse restores the whole first
assignment, not merely its designated fixed coordinates. -/
theorem leftBlock_join (left right : Nat) (first : Fin left -> Bool) (second : Fin right -> Bool) :
    leftBlock left right (join left right first second) = first := by
  funext index
  unfold leftBlock join
  have earlier : (index.castAdd right).val < left := index.isLt
  rw [dif_pos earlier]
  congr 1

/-- The suffix read restores the whole second assignment at its offset. -/
theorem rightBlock_join (left right : Nat) (first : Fin left -> Bool) (second : Fin right -> Bool) :
    rightBlock left right (join left right first second) = second := by
  funext index
  unfold rightBlock join
  have later : ¬ (Fin.natAdd left index).val < left := by
    change ¬ left + index.val < left
    omega
  rw [dif_neg later]
  congr 1
  apply Fin.ext
  change left + index.val - left = index.val
  omega

/-- Every combined assignment is recovered by joining its actual reads.
The proof exhibits both finite index cases, so no inverse is chosen. -/
theorem join_split (left right : Nat) (sample : Fin (left + right) -> Bool) :
    join left right (leftBlock left right sample) (rightBlock left right sample) = sample := by
  funext index
  unfold join
  by_cases earlier : index.val < left
  · rw [dif_pos earlier]
    change sample _ = sample index
    apply congrArg sample
    exact Fin.ext rfl
  · rw [dif_neg earlier]
    change sample _ = sample index
    apply congrArg sample
    apply Fin.ext
    change left + (index.val - left) = index.val
    omega

/-- Present one supplied cube assignment as its two actual block reads. -/
def split (left right : Nat) (sample : Fin (left + right) -> Bool) :
    (Fin left -> Bool) × (Fin right -> Bool) :=
  (leftBlock left right sample, rightBlock left right sample)

/-- Splitting the explicit join restores both supplied assignments. -/
theorem split_join (left right : Nat) (first : Fin left -> Bool) (second : Fin right -> Bool) :
    split left right (join left right first second) = (first, second) := by
  unfold split
  rw [leftBlock_join, rightBlock_join]

/-- Joining two zero assignments gives the zero of the complete cube.
This identity is the homogeneity boundary used by character applications. -/
theorem join_zero (left right : Nat) :
    join left right (fun _ => false) (fun _ => false) = (fun _ => false) := by
  funext index
  unfold join
  split <;> rfl

/-- The explicit assembly respects pointwise XOR, rather than merely being
a finite bijection.  Homogeneous local phases can therefore be transported
through this change of indexing without changing their characters. -/
theorem join_xor (left right : Nat)
    (first otherFirst : Fin left -> Bool) (second otherSecond : Fin right -> Bool) :
    join left right (xorAssignment left first otherFirst) (xorAssignment right second otherSecond) =
      xorAssignment (left + right) (join left right first second) (join left right otherFirst otherSecond) := by
  funext index
  by_cases earlier : index.val < left
  · simp only [join, xorAssignment, dif_pos earlier]
  · simp only [join, xorAssignment, dif_neg earlier]

/-- Coordinate consistency in the complete cylinder is exactly consistency
in both actual blocks.  No full-support completeness assumption is used for
a block that has some coordinates restricted to false. -/
theorem cylinder_member_iff (left right : Nat) (fixed sample : Fin (left + right) -> Bool) :
    sample ∈ falseCylinderEnumeration (left + right) fixed ↔
      leftBlock left right sample ∈ falseCylinderEnumeration left (leftBlock left right fixed) ∧
        rightBlock left right sample ∈ falseCylinderEnumeration right (rightBlock left right fixed) := by
  rw [falseCylinderEnumeration_member_iff, falseCylinderEnumeration_member_iff,
    falseCylinderEnumeration_member_iff]
  constructor
  · intro consistent
    exact ⟨fun index selected => consistent (index.castAdd right) selected,
      fun index selected => consistent (Fin.natAdd left index) selected⟩
  · intro consistent index selected
    by_cases earlier : index.val < left
    · let localIndex : Fin left := ⟨index.val, earlier⟩
      have embedded : localIndex.castAdd right = index := Fin.ext rfl
      have localFixed : leftBlock left right fixed localIndex = true := by
        simpa only [leftBlock, embedded] using selected
      simpa only [leftBlock, embedded] using consistent.1 localIndex localFixed
    · let localIndex : Fin right := ⟨index.val - left, by omega⟩
      have embedded : Fin.natAdd left localIndex = index := by
        apply Fin.ext
        dsimp only [localIndex, Fin.natAdd]
        omega
      have localFixed : rightBlock left right fixed localIndex = true := by
        simpa only [rightBlock, embedded] using selected
      simpa only [rightBlock, embedded] using consistent.2 localIndex localFixed

/-- The complete restricted cube is a permutation of the Cartesian support
after the explicit split.  Both lists contain every permitted assignment once;
in particular the split never masks a full list into repeated fixed values. -/
theorem cylinder_split_perm (left right : Nat) (fixed : Fin (left + right) -> Bool) :
    ((falseCylinderEnumeration (left + right) fixed).map (split left right)).Perm
      (ConstructivePermutation.pairList
        (falseCylinderEnumeration left (leftBlock left right fixed))
        (falseCylinderEnumeration right (rightBlock left right fixed))) := by
  letI : DecidableEq (Fin left -> Bool) := assignmentDecidableEq left (fun _ => Bool) (fun _ => inferInstance)
  letI : DecidableEq (Fin right -> Bool) := assignmentDecidableEq right (fun _ => Bool) (fun _ => inferInstance)
  apply ConstructivePermutation.perm_of_nodup_mem_iff
  · apply ConstructivePermutation.nodup_map_of_injective_on
    · intro first _firstListed second _secondListed equal
      exact (join_split left right first).symm.trans
        ((congrArg (fun pair => join left right pair.1 pair.2) equal).trans (join_split left right second))
    · exact falseCylinderEnumeration_nodup (left + right) fixed
  · exact ConstructivePermutation.pairList_nodup _ _
      (falseCylinderEnumeration_nodup left _) (falseCylinderEnumeration_nodup right _)
  · intro pair
    rw [ConstructivePermutation.mem_pairList]
    constructor
    · intro listed
      rcases List.mem_map.mp listed with ⟨sample, sampleListed, equal⟩
      have consistent := (cylinder_member_iff left right fixed sample).mp sampleListed
      change (split left right sample).1 ∈ _ ∧ (split left right sample).2 ∈ _ at consistent
      rw [equal] at consistent
      exact consistent
    · intro consistent
      refine List.mem_map.mpr ⟨join left right pair.1 pair.2, ?_, split_join left right pair.1 pair.2⟩
      apply (cylinder_member_iff left right fixed _).mpr
      rw [leftBlock_join, rightBlock_join]
      exact consistent

private theorem sum_pairList (left : List α) (right : List β) (term : α -> β -> Int) :
    ((ConstructivePermutation.pairList left right).map (fun pair => term pair.1 pair.2)).sum =
      (left.map (fun first => (right.map (term first)).sum)).sum := by
  induction left with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [ConstructivePermutation.pairList, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.map_cons, List.sum_cons, inductionHypothesis]

/-- Split the complete cylinder sum of an arbitrary mixed integer integrand.
The exact support permutation precedes summation; no independence of the
integrand, equal evidence mass, or positive summand is assumed. -/
theorem cylinder_sum_split (left right : Nat) (fixed : Fin (left + right) -> Bool)
    (term : (Fin (left + right) -> Bool) -> Int) :
    ((falseCylinderEnumeration (left + right) fixed).map term).sum =
      ((falseCylinderEnumeration left (leftBlock left right fixed)).map (fun first =>
        ((falseCylinderEnumeration right (rightBlock left right fixed)).map (fun second =>
          term (join left right first second))).sum)).sum := by
  have reordered := FiniteSupportedSum.sum_eq_of_perm ((cylinder_split_perm left right fixed).map
    (fun pair => term (join left right pair.1 pair.2)))
  simp only [List.map_map, Function.comp_def, split, join_split] at reordered
  exact reordered.trans (sum_pairList _ _ (fun first second => term (join left right first second)))

end BooleanBlocks
end FiniteProduct
end Probability
end Thesis
