import Thesis.CausalTransport.NativeDerivationTyping
import Thesis.CausalTransport.HiddenDAGSoundness

namespace Thesis.Causality.NativeDemandTyping

open Probability

/-!
# Supported derivations preserve their demanded types on the matching graph

Support typing is not numerical equality. Here equality follows from the
existing native soundness theorem, using the full support tree reconstructed
by the demand checker. The proof graph is the profiles' actual observed
graph; an unrelated graph is not silently accepted as a semantic premise.

At every demanded cell the two actual values agree, hence both are zero or
both positive. Outside the demand both type tables retain `unused`. This
also fixes the positive-factor mask when a supported proof changes a weight.
No expression quotient, rewrite encoding or completion algorithm follows
from these preservation facts.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

private theorem status_eq_of_equivalent {left right : ProbabilityResult.Result}
    (same : ProbabilityResult.Equivalent left right) : ProbabilityResult.status left = ProbabilityResult.status right := by
  cases same with
  | unsupported => rfl
  | value same => exact ProbabilityResult.valueStatus_equiv same

/-- The types agree because the original native values agree wherever the
demand is active, not because a finite table supplies a new causal equation. -/
theorem status_eq_of_checked (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (accepted : checkDerivation profiles demand derivation = true)
    (index : Fin profiles.length) (reference : S.Assignment) (needed : demand index reference = true) :
    termStatus profiles left index reference = termStatus profiles right index reference := by
  rw [termStatus_exact, termStatus_exact]
  exact status_eq_of_equivalent (derivation.hiddenDAG_denotational_soundAt
    (supportAt profiles demand derivation accepted index reference needed))

theorem typeOf_eq_of_checked (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (accepted : checkDerivation profiles demand derivation = true) :
    typeOf profiles left demand = typeOf profiles right demand := by
  funext index reference
  cases needed : demand index reference with
  | false => simp only [typeOf, needed, Bool.false_eq_true, if_false]
  | true =>
      simp only [typeOf, needed, if_true, status_eq_of_checked profiles demand derivation accepted index reference needed]

/-- Rewriting a supported weight preserves which factor cells are demanded.
This retains the defined-zero branch without giving undefined weights support. -/
theorem positiveDemand_eq_of_checked (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (accepted : checkDerivation profiles demand derivation = true) :
    positiveDemand profiles demand (termStatus profiles left) = positiveDemand profiles demand (termStatus profiles right) := by
  funext index reference
  cases needed : demand index reference with
  | false => simp only [positiveDemand, needed, Bool.false_and]
  | true =>
      simp only [positiveDemand, needed, status_eq_of_checked profiles demand derivation accepted index reference needed]

end Thesis.Causality.NativeDemandTyping
