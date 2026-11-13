import Thesis.Causality.PairRoot

namespace Thesis
namespace Causality

/-!
# Uniqueness of the original reserved pair inputs

The pair-root expansion reserves one input for each ordered bidirected
pair.  Membership alone does not justify replacing an input fold by one
coordinate: a repeated entry would give two different indices with the
same label.  This module proves that the actual finite enumeration has no
repetitions, and hence that equality of stored pairs identifies their
original indices.  Nothing is deduplicated after model construction.

The argument uses the two explicit `finRange` enumerations and their
injective pairing maps.  All input indices remain the original graph's
indices; no representative, choice function, or classical decision is used.
-/

variable {S : ObservedSignature}

private theorem finRange_nodup (count : Nat) : (List.finRange count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count inductionHypothesis =>
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_map.mp member with ⟨index, _listed, equal⟩
        have values := congrArg Fin.val equal
        change index.val + 1 = 0 at values
        omega
      · exact inductionHypothesis.map Fin.succ
          (fun left right different equal => different (Fin.succ_inj.mp equal))

/-- Every observed pair occurs at most once in the literal Cartesian
enumeration.  Different outer indices have different first projections. -/
theorem allObservedPairs_nodup (S : ObservedSignature) :
    (allObservedPairs S).Nodup := by
  unfold allObservedPairs
  apply List.pairwise_flatMap.mpr
  constructor
  · intro first _member
    exact (finRange_nodup S.count).map (fun second => (first, second))
      (fun left right different same => different (congrArg Prod.snd same))
  · apply (finRange_nodup S.count).imp
    intro left right different first firstMem second secondMem same
    rcases List.mem_map.mp firstMem with ⟨firstChild, _listed, firstEq⟩
    rcases List.mem_map.mp secondMem with ⟨secondChild, _listed, secondEq⟩
    exact different (congrArg Prod.fst (firstEq.trans (same.trans secondEq.symm)))

/-- Filtering for ordered bidirected pairs retains the proved uniqueness
of the actual enumeration.  This certifies the reserved inputs themselves. -/
theorem pairRoots_nodup (G : ObservedGraph S) : (pairRoots G).Nodup :=
  (allObservedPairs_nodup S).filter _

/-- Two original input indices with the same stored pair are equal.
In particular an alias-normalization proof cannot secretly select another
input carrying the same endpoint label. -/
theorem pairRoots_get_injective (G : ObservedGraph S)
    (left right : Fin (pairRootCount G))
    (same : (pairRoots G).get left = (pairRoots G).get right) : left = right := by
  apply Fin.ext
  apply (List.getElem_inj (pairRoots_nodup G)).mp
  exact same

end Causality
end Thesis
