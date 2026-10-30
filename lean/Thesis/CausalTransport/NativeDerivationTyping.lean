import Thesis.CausalTransport.NativeDemandTypes
import Thesis.CausalTransport.NativeDerivationSupportCheck

namespace Thesis.Causality.NativeDemandTyping

open Probability

/-!
# Demand-indexed typing agrees with the full native proof-support checker

Types of the two printed endpoints alone do not justify a derivation.
The checker below also visits intermediate proofs, pulling the active mask
through marginal and fixed-reference contexts and retaining the asymmetric
zero-weight factor obligation. Exactness ranges over every demanded cell
of the supplied profile family, including references absent observationally.

The type pair returned for a supplied proof is finite data. The proof itself
remains the input: two proofs with the same pair cannot be substituted merely
because those data agree. No proof enumeration, finite congruence quotient,
ground-rewrite completion algorithm or universal stopping result is asserted.
Reconstruction uses the existing support recursor and each model's actual
values; its noncomputability annotation introduces no selected witness.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S} {G : ObservedGraph S}

def checkDerivation (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) : Bool :=
  (check profiles left demand && check profiles right demand) &&
    match derivation with
    | .refl _ => true
    | .symm inner => checkDerivation profiles demand inner
    | .trans first second => checkDerivation profiles demand first && checkDerivation profiles demand second
    | .doRule _ => true
    | .marginalization _ _ _ _ _ => true
    | .conditioning _ _ _ _ _ => true
    | .chain _ _ _ _ _ => true
    | .weightedChain _ _ _ _ _ => true
    | .multiplyComm _ _ => true
    | .multiplyAssoc _ _ _ => true
    | .marginalizeCongr nodes inner => checkDerivation profiles (marginalDemand profiles demand nodes) inner
    | .evaluateAtCongr fixed inner => checkDerivation profiles (fixedDemand profiles demand fixed) inner
    | .addCongr first second => checkDerivation profiles demand first && checkDerivation profiles demand second
    | .multiplyCongr first second => checkDerivation profiles demand first && checkDerivation profiles demand second
    | @DoCalculusDerivation.weightedMultiplyCongr _ _ _ weight _ _ _ first second =>
        checkDerivation profiles demand first &&
          checkDerivation profiles (positiveDemand profiles demand (termStatus profiles weight)) second
    | .divideCongr numerator denominator => checkDerivation profiles demand numerator && checkDerivation profiles demand denominator
    | .eqCongr _ _ inner => checkDerivation profiles demand inner

/-- Agreement with every original recursive check, rather than a check of
one representative, one root reference, or just the final expression. -/
theorem checkDerivation_exact (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) :
    checkDerivation profiles demand derivation = allNeeded profiles demand
      (fun index reference => HiddenDAGLocalDerivationSupport.check (profiles.get index).model reference derivation) := by
  induction derivation generalizing demand
  all_goals
    change (_ && _ && _) = allNeeded profiles demand (fun index reference => (_ && _) && _)
    rw [allNeeded_and, allNeeded_and]
    simp only [← check_exact]
  case refl => rw [allNeeded_true]
  case symm inner ih => rw [ih]
  case trans first second firstIH secondIH => rw [allNeeded_and, firstIH, secondIH]
  case doRule => rw [allNeeded_true]
  case marginalization => rw [allNeeded_true]
  case conditioning => rw [allNeeded_true]
  case chain => rw [allNeeded_true]
  case weightedChain => rw [allNeeded_true]
  case multiplyComm => rw [allNeeded_true]
  case multiplyAssoc => rw [allNeeded_true]
  case marginalizeCongr nodes inner ih => rw [allNeeded_marginal, ih]
  case evaluateAtCongr fixed left right inner ih =>
    rw [ih, allNeeded_fixed profiles demand
      (fun index reference => HiddenDAGLocalDerivationSupport.check (profiles.get index).model reference inner) fixed]
  case addCongr first second firstIH secondIH => rw [allNeeded_and, firstIH, secondIH]
  case multiplyCongr first second firstIH secondIH => rw [allNeeded_and, firstIH, secondIH]
  case weightedMultiplyCongr weight weight' factor factor' first second firstIH secondIH =>
    rw [allNeeded_and, firstIH, secondIH]
    simp only [← termStatus_exact, allNeeded_positive]
  case divideCongr numerator denominator numeratorIH denominatorIH => rw [allNeeded_and, numeratorIH, denominatorIH]
  case eqCongr _ _ inner ih => rw [ih]

def inferDerivation (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) :
    Option (TermType profiles × TermType profiles) :=
  if checkDerivation profiles demand derivation then
    some (typeOf profiles left demand, typeOf profiles right demand)
  else none

theorem inferDerivation_isSome (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) :
    (inferDerivation profiles demand derivation).isSome = allNeeded profiles demand
      (fun index reference => HiddenDAGLocalDerivationSupport.check (profiles.get index).model reference derivation) := by
  rw [← checkDerivation_exact]
  cases checked : checkDerivation profiles demand derivation <;>
    simp only [inferDerivation, checked, Bool.false_eq_true, if_false, if_true, Option.isSome_none, Option.isSome_some]

/-- Recover the old complete support tree at any requested cell. This
keeps numerical values in the original model, not in the finite type table. -/
noncomputable def supportAt (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right)
    (accepted : checkDerivation profiles demand derivation = true)
    (index : Fin profiles.length) (reference : S.Assignment) (needed : demand index reference = true) :
    HiddenDAGLocalDerivationSupport (profiles.get index).model reference derivation :=
  HiddenDAGLocalDerivationSupport.ofCheck _ _ derivation
    ((allNeeded_exact ..).mp ((checkDerivation_exact profiles demand derivation).symm.trans accepted) index reference needed)

end Thesis.Causality.NativeDemandTyping
