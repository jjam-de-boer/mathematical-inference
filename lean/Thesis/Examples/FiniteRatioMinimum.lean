import Thesis.Probability.FiniteRatioMinimum

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteRatioMinimum

/-!
# Finite exact-ratio selection without reduced representatives

The tests include equal but differently presented fractions and ratios above
one, as occur in a support-reduction step.  The literal candidate chosen at a
tie is allowed to change; the universal bound is on represented fractions.
-/

def half : QProb := ⟨1, 2, by decide⟩
def twoThirds : QProb := ⟨2, 3, by decide⟩
def threeQuarters : QProb := ⟨3, 4, by decide⟩

theorem selected_half : QProb.Equiv
    (Probability.FiniteRatioMinimum.select id twoThirds [threeQuarters, half]) half := by decide +kernel

theorem tie_keeps_actual_candidate :
    (Probability.FiniteRatioMinimum.select id QProb.one [⟨2, 2, by decide⟩]).den = 2 := by decide +kernel

theorem ratios_above_one : QProb.Equiv
    (Probability.FiniteRatioMinimum.select id ⟨2, 1, by decide⟩ [⟨3, 2, by decide⟩]) ⟨3, 2, by decide⟩ := by decide +kernel

theorem empty_tail : Probability.FiniteRatioMinimum.select id half [] = half := rfl

end FiniteRatioMinimum
end Examples
end Probability
end Thesis
