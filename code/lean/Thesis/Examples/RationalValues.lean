import Thesis.Probability.RationalValues

namespace Thesis
namespace Probability
namespace Examples
namespace RationalValues

/-!
# Exact signed fractions without normalized-rational dependencies

Different probability presentations embed as equivalent signed fractions.
Their difference can have a negative numerator while the source probabilities
and all actual atom weights remain nonnegative.  No normalized-rational
constructor, real arithmetic or global decision principle is involved.
-/

def third : QProb := ⟨1, 3, by decide⟩
def half : QProb := ⟨1, 2, by decide⟩
def anotherThird : QProb := ⟨2, 6, by decide⟩

theorem equal_presentations : SignedRatio.Equiv third.toSignedRatio anotherThird.toSignedRatio :=
  QProb.toSignedRatio_congr (by decide +kernel)

theorem signed_difference : SignedRatio.Equiv (SignedRatio.sub third.toSignedRatio half.toSignedRatio)
    ⟨-1, 6, by decide⟩ := by decide +kernel

theorem addition_preserved : (QProb.add third half).toSignedRatio =
    SignedRatio.add third.toSignedRatio half.toSignedRatio := QProb.toSignedRatio_add _ _
theorem multiplication_preserved : (QProb.mul third half).toSignedRatio =
    SignedRatio.mul third.toSignedRatio half.toSignedRatio := QProb.toSignedRatio_mul _ _
theorem probabilities_nonnegative : 0 ≤ third.toSignedRatio.num ∧ 0 ≤ half.toSignedRatio.num :=
  ⟨QProb.toSignedRatio_nonnegative _, QProb.toSignedRatio_nonnegative _⟩

theorem distinct_probabilities_stay_distinct : ¬ SignedRatio.Equiv third.toSignedRatio half.toSignedRatio := by
  intro same
  have invalid : ¬ QProb.Equiv third half := by decide +kernel
  exact invalid ((QProb.toSignedRatio_equiv_iff third half).mp same)

end RationalValues
end Examples
end Probability
end Thesis
