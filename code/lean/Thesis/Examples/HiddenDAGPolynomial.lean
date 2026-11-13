import Thesis.CausalTransport.HiddenDAGPolynomial
import Thesis.Examples.HiddenDAGCollapse

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGPolynomial

open Probability HiddenDAGCollapse

/-!
# A checked native structural zero, uniformly over its source laws

In the hidden-relay fixture, factual `X = U` and `Y = U xor X`, so `Y = true`
is impossible whatever independent probabilities are placed on the original
private-noise types.  The compiled native event is tested against zero with
empty certificates in both directions, then the source-law theorem transfers
the checked bound to every independent law on this same structural template.

Only the small fixture's Boolean checker is executed.  The universal new-law
claim uses the semantic compiler and bound soundness theorem, not tests of
selected probabilities.  It is not advertised as a zero for every mechanism
on this graph; the unchanged relay equations are essential.
-/

def query : NativeProbabilityQuery signature := ⟨HardIntervention.empty signature, fun assignment => assignment y⟩
def certificate : model.ProbabilityBoundCertificate query := ⟨[], []⟩
theorem lower_checked : model.checkProbabilityLower query SignedRatio.zero certificate = true := by decide +kernel
theorem upper_checked : model.checkProbabilityUpper query SignedRatio.zero certificate = true := by decide +kernel
theorem native_compiler_sound : SignedRatio.Equiv
    (RationalPolynomial.evaluate (model.probabilityProgram query).polynomial (model.probabilityProgram query).parameters)
    (model.interventionalValue query.intervention query.event).toSignedRatio := model.probabilityProgram_sound query

theorem every_source_law_zero (law : FiniteProduct.IndependentLaw model.Noise) :
    ((model.withSourceLaw law).interventionalValue query.intervention query.event).num = 0 := by
  have upper := model.checkProbabilityUpper_sound_forSourceLaw query SignedRatio.zero certificate upper_checked law
  have originalOrder := (SignedRatio.toSignedRatio_le_iff _ QProb.zero).mp upper
  have massBound : ((model.withSourceLaw law).interventionalValue query.intervention query.event).num ≤ 0 := by
    simpa only [QProb.LE, QProb.zero, Nat.mul_one, Nat.zero_mul] using originalOrder
  exact Nat.le_zero.mp massBound

end HiddenDAGPolynomial
end Examples
end Causality
end Thesis
