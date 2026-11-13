import Thesis.Causality.PairRootChannels
import Thesis.Probability.ConstructivePermutation

namespace Thesis
namespace Causality
namespace PairRootChannels
namespace Environment

open Probability

/-!
# An independent environment block at the original pair roots

The main character channels and the latent bits used by a local parent
signal must be independent.  Reading another main channel as an environment
would invalidate the cancellation argument.  This module reserves a new
terminal bit at each actual pair root and proves the full prior separation.

There is still one source per original bidirected pair, with exactly its
original two children.  The word "environment" names the collection of
terminal coordinates for a proof; it does not install one source incident
to every observed node.  A mechanism receives only its incident root vectors.

The displayed split and join are explicit inverse matrix reads.  They turn
the complete, unit-weight shared support into a permutation of an independent
environment-by-main Cartesian support.  Consequently arbitrary finite row
integrands can be summed first over the main channels at a fixed environment.
This is a whole-prior statement, not merely fairness of individual bits.

Empty main channel families and graphs with no pair roots are included.  The
actual denominator is retained in both boundaries, and no hidden assignment,
coupling or inverse is selected using choice.
-/

variable {S : ObservedSignature}

/-- One terminal bit at each original pair root.  This is an indexing type
for the proof, not an additional globally shared latent source. -/
abbrev Assignment (G : ObservedGraph S) := BitVector (pairRootCount G)

/-- Forget only the reserved terminal coordinate of each actual root. -/
def main (G : ObservedGraph S) (channels : Nat)
    (shared : (extension G (channels + 1)).Assignment) : (extension G channels).Assignment :=
  fun root channel => shared root channel.castSucc

/-- Read the independent reserved coordinate from each original root. -/
def bits (G : ObservedGraph S) (channels : Nat)
    (shared : (extension G (channels + 1)).Assignment) : Assignment G :=
  fun root => shared root (Fin.last channels)

/-- Restore the actual root-major assignment from the two displayed blocks.
The constructive terminal-coordinate extension retains each original root. -/
def join (G : ObservedGraph S) (channels : Nat) (environment : Assignment G)
    (shared : (extension G channels).Assignment) : (extension G (channels + 1)).Assignment :=
  fun root => FiniteProduct.extend (environment root) (shared root)

/-- Reading the main coordinates of a joined assignment restores them. -/
theorem main_join (G : ObservedGraph S) (channels : Nat) (environment : Assignment G)
    (shared : (extension G channels).Assignment) : main G channels (join G channels environment shared) = shared := by
  funext root channel
  exact FiniteProduct.extend_castSucc (Value := fun _ => Bool) (environment root) (shared root) channel

/-- Reading the terminal coordinates restores the supplied environment. -/
theorem bits_join (G : ObservedGraph S) (channels : Nat) (environment : Assignment G)
    (shared : (extension G channels).Assignment) : bits G channels (join G channels environment shared) = environment := by
  funext root
  exact FiniteProduct.extend_last (Value := fun _ => Bool) (environment root) (shared root)

/-- The two blocks reconstruct every actual shared assignment.  Finite
index elimination, rather than a selected inverse, covers the empty prefix. -/
theorem join_split (G : ObservedGraph S) (channels : Nat)
    (shared : (extension G (channels + 1)).Assignment) :
    join G channels (bits G channels shared) (main G channels shared) = shared := by
  funext root channel
  refine Fin.lastCases ?_ (fun earlier => ?_) channel
  · exact FiniteProduct.extend_last _ _
  · exact FiniteProduct.extend_castSucc _ _ earlier

/-- The environment varies first in the Cartesian presentation, so each
inner integral uses the complete main prior at a fixed environment. -/
def split (G : ObservedGraph S) (channels : Nat)
    (shared : (extension G (channels + 1)).Assignment) : Assignment G × (extension G channels).Assignment :=
  (bits G channels shared, main G channels shared)

/-- Joining and splitting restores both displayed coordinates literally. -/
theorem split_join (G : ObservedGraph S) (channels : Nat) (environment : Assignment G)
    (shared : (extension G channels).Assignment) :
    split G channels (join G channels environment shared) = (environment, shared) := by
  unfold split
  rw [bits_join, main_join]

/-- The complete environment support contains every original root-bit
assignment exactly once, even when there are no original pair roots. -/
def enumeration (G : ObservedGraph S) : List (Assignment G) := bitEnumeration (pairRootCount G)

theorem enumeration_complete (G : ObservedGraph S) (environment : Assignment G) :
    environment ∈ enumeration G := bitEnumeration_complete _ environment

theorem enumeration_nodup (G : ObservedGraph S) : (enumeration G).Nodup := bitEnumeration_nodup _

/-- The reserved block has a positive literal support size.  No nonempty
list equivalence or classically selected member is needed for this proof. -/
theorem enumeration_length_positive (G : ObservedGraph S) : 0 < (enumeration G).length := by
  change 0 < (bitEnumeration (pairRootCount G)).length
  rw [← factor_den]
  exact (factor (pairRootCount G)).den_pos

/-- The actual enlarged support is a permutation of the full independent
Cartesian support after the explicit split.  Neither block loses a repeated
weight or gains a dummy root in this change of indexing. -/
theorem enumeration_split_perm (G : ObservedGraph S) (channels : Nat) :
    ((PairRootChannels.enumeration G (channels + 1)).map (split G channels)).Perm
      (ConstructivePermutation.pairList (enumeration G) (PairRootChannels.enumeration G channels)) := by
  letI : DecidableEq (Assignment G) :=
    FiniteProduct.assignmentDecidableEq (pairRootCount G) (fun _ => Bool) (fun _ => inferInstance)
  letI : DecidableEq (extension G channels).Assignment :=
    FiniteProduct.assignmentDecidableEq (pairRootCount G) (fun _ => BitVector channels)
      (fun _ => FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance))
  apply ConstructivePermutation.perm_of_nodup_mem_iff
  · apply ConstructivePermutation.nodup_map_of_injective_on
    · intro first _firstListed second _secondListed same
      exact (join_split G channels first).symm.trans
        ((congrArg (fun pair => join G channels pair.1 pair.2) same).trans (join_split G channels second))
    · exact PairRootChannels.enumeration_nodup G (channels + 1)
  · exact ConstructivePermutation.pairList_nodup _ _ (enumeration_nodup G)
      (PairRootChannels.enumeration_nodup G channels)
  · intro pair
    constructor
    · intro _listed
      exact (ConstructivePermutation.mem_pairList _ _ _ _).mpr
        ⟨enumeration_complete G pair.1, PairRootChannels.enumeration_complete G channels pair.2⟩
    · intro _listed
      exact List.mem_map.mpr ⟨join G channels pair.1 pair.2,
        PairRootChannels.enumeration_complete G (channels + 1) _, split_join G channels pair.1 pair.2⟩

private theorem natural_sum_eq_of_perm {left right : List Nat} (permutation : left.Perm right) :
    left.sum = right.sum := by
  induction permutation with
  | nil => rfl
  | cons value _ inductionHypothesis => simp only [List.sum_cons, inductionHypothesis]
  | swap left right rest => exact Nat.add_left_comm _ _ _
  | trans _ _ leftEqual rightEqual => exact leftEqual.trans rightEqual

private theorem natural_sum_pairList (left : List α) (right : List β) (term : α -> β -> Nat) :
    ((ConstructivePermutation.pairList left right).map (fun pair => term pair.1 pair.2)).sum =
      (left.map (fun first => (right.map (term first)).sum)).sum := by
  induction left with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [ConstructivePermutation.pairList, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.map_cons, List.sum_cons, inductionHypothesis]

/-- Every actual natural-valued row integrand separates into the complete
main integral at each independent environment.  This applies to mixed,
nonrectangular integrands, not just products of coordinate events. -/
theorem enumeration_sum_split (G : ObservedGraph S) (channels : Nat)
    (term : (extension G (channels + 1)).Assignment -> Nat) :
    ((PairRootChannels.enumeration G (channels + 1)).map term).sum =
      ((enumeration G).map (fun environment =>
        ((PairRootChannels.enumeration G channels).map (fun shared => term (join G channels environment shared))).sum)).sum := by
  have reordered := natural_sum_eq_of_perm ((enumeration_split_perm G channels).map
    (fun pair => term (join G channels pair.1 pair.2)))
  simp only [List.map_map, Function.comp_def, split, join_split] at reordered
  exact reordered.trans (natural_sum_pairList (enumeration G) (PairRootChannels.enumeration G channels)
    (fun environment shared => term (join G channels environment shared)))

/-- The denominator of the actual enlarged prior is the product of both
complete support sizes.  This proves normalization on the same source space
used by the row integral, rather than assuming an independent mixing law. -/
theorem prior_den_split (G : ObservedGraph S) (channels : Nat) :
    (prior G (channels + 1)).den = (enumeration G).length * (prior G channels).den := by
  rw [PairRootChannels.prior_den, PairRootChannels.prior_den]
  have lengths := (enumeration_split_perm G channels).length_eq
  simp only [List.length_map, ConstructivePermutation.pairList_length] at lengths
  exact lengths

end Environment
end PairRootChannels
end Causality
end Thesis
