import Thesis.Probability.RationalValues

namespace Thesis
namespace Probability
namespace Examples
namespace RationalValues

/-!
# Exact arithmetic bridge, not signed probability records

Different natural fraction presentations embed as the same rational value.
The auxiliary field can represent negative *differences* of probabilities,
without altering either input probability or any finite record's atom weights.
The final rejection uses the bidirectional equality bridge, so an equality in
the auxiliary algebra cannot conceal unequal original probability values.
-/

def third : QProb := ⟨1, 3, by decide⟩
def half : QProb := ⟨1, 2, by decide⟩
def anotherThird : QProb := ⟨2, 6, by decide⟩

theorem equal_presentations : third.toRat = anotherThird.toRat := QProb.toRat_congr (by decide +kernel)

theorem signed_difference : third.toRat - half.toRat = mkRat (-1) 6 := by decide +kernel

theorem addition_preserved : (QProb.add third half).toRat = third.toRat + half.toRat := QProb.toRat_add _ _
theorem multiplication_preserved : (QProb.mul third half).toRat = third.toRat * half.toRat := QProb.toRat_mul _ _
theorem probabilities_nonnegative : 0 ≤ third.toRat ∧ 0 ≤ half.toRat :=
  ⟨QProb.toRat_nonnegative _, QProb.toRat_nonnegative _⟩

theorem distinct_probabilities_stay_distinct : third.toRat ≠ half.toRat := by
  intro same
  have invalid : ¬ QProb.Equiv third half := by decide +kernel
  exact invalid ((QProb.toRat_eq_iff third half).mp same)

end RationalValues
end Examples
end Probability
end Thesis
