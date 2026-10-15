import Thesis.Probability.RationalMixture

namespace Thesis
namespace Probability
namespace Examples
namespace RationalMixture

open FiniteProbRecord

/-!
# Exact mixtures with unrelated denominators and zero endpoints

The two input records have denominators three and five.  Their mixture
retains a zero atom and repeated labels, and uses the natural mixing masses
two and one.  The resulting event probability is exactly nineteen over
forty-five.  The zero-weight and collapsed-interval checks ensure that the
general interpolation theorem does not require strict endpoint separation.
-/

def left : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1), (true, 0)], 3, by decide, rfl⟩
def right : FiniteProbRecord Bool := ⟨[(true, 3), (false, 2)], 5, by decide, rfl⟩
def mixed := left.mixture right 2 1 (by decide)

theorem mixed_value : QProb.Equiv (mixed.probVal id) ⟨19, 45, by decide⟩ := by decide +kernel
theorem additive_atom_count : mixed.atoms.length = left.atoms.length + right.atoms.length := rfl
theorem zero_right_weight : QProb.Equiv ((left.mixture right 1 0 (by decide)).probVal id) (left.probVal id) := by
  decide +kernel

theorem interior_interpolation :
    ∃ a b, ∃ positive : 0 < a + b,
      QProb.Equiv (QProb.weightedPair a b positive ⟨1, 3, by decide⟩ ⟨3, 5, by decide⟩) ⟨1, 2, by decide⟩ :=
  QProb.exists_weightedPair_equiv _ _ _ (by decide +kernel) (by decide +kernel)

theorem collapsed_presentations :
    ∃ a b, ∃ positive : 0 < a + b,
      QProb.Equiv (QProb.weightedPair a b positive ⟨1, 2, by decide⟩ ⟨2, 4, by decide⟩) ⟨3, 6, by decide⟩ :=
  QProb.exists_weightedPair_equiv _ _ _ (by decide +kernel) (by decide +kernel)

end RationalMixture
end Examples
end Probability
end Thesis
