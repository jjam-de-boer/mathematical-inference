import Thesis.CausalTransport.NativePathEncoding
import Thesis.CausalTransport.NativeDerivationLinearization

namespace Thesis.Causality.NativeDemandEncoding.Path

open Probability NativeDemandTyping

/-!
# Full supported derivations assemble into one typed finite path

The existing linearizer fixes a raw path from the original proof syntax.
Its modelwise support theorem is aggregated over exactly the supplied demand
cells, then the typed path encoder is applied once to that common path.
Neither a path nor a numerical value is selected separately for each model.

Accepted applications and both literal endpoint terms are preserved, without
a proof-depth bound or extra positivity. Erasure recovers the linearized path;
it does not claim that the original transitivity/congruence tree is unchanged.
Only forward preservation of the original proof's support is used. Failure
of that proof does not rule out a different proof with a larger domain.

This assembly introduces no new equation, certificate guard, normalization,
or search. The separate native `actionOne` theorem is not a derivation atom.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

theorem linearize_checked (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (accepted : checkDerivation profiles requested derivation = true) :
    rawCheck profiles derivation.linearize requested = true := by
  have native := (checkDerivation_exact profiles requested derivation).symm.trans accepted
  apply (allNeeded_exact ..).mpr
  intro index reference needed
  exact derivation.linearize_checkVertices (profiles.get index).model reference
    ((allNeeded_exact ..).mp native index reference needed)

def ofDerivation (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (accepted : checkDerivation profiles requested derivation = true) :
    Path profiles (Term.encode profiles left requested) (Term.encode profiles right requested) :=
  encode profiles derivation.linearize requested (linearize_checked profiles requested derivation accepted)

theorem ofDerivation_checked (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (accepted : checkDerivation profiles requested derivation = true) :
    (ofDerivation profiles requested derivation accepted).check requested = true :=
  encode_checked profiles derivation.linearize requested (linearize_checked profiles requested derivation accepted)

theorem eraseData_ofDerivation (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (accepted : checkDerivation profiles requested derivation = true) :
    (ofDerivation profiles requested derivation accepted).eraseData = ⟨left, right, derivation.linearize⟩ :=
  eraseData_encode profiles derivation.linearize requested (linearize_checked profiles requested derivation accepted)

/-- Check the original supplied proof before conversion. Its rejection is
not an assertion that every path or every alternative proof is unsupported. -/
def ofDerivation? (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right) :
    Option (Path profiles (Term.encode profiles left requested) (Term.encode profiles right requested)) :=
  if accepted : checkDerivation profiles requested derivation = true then
    some (ofDerivation profiles requested derivation accepted)
  else none

theorem ofDerivation?_isSome (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right) :
    (ofDerivation? profiles requested derivation).isSome = checkDerivation profiles requested derivation := by
  unfold ofDerivation?
  split
  · next accepted => simp only [Option.isSome_some, accepted]
  · next rejected =>
      cases checked : checkDerivation profiles requested derivation with
      | false => rfl
      | true => exact False.elim (rejected checked)

end Thesis.Causality.NativeDemandEncoding.Path
