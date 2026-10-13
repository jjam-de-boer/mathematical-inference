import Thesis.CausalTransport.GuardedHostChainCompilation

namespace Thesis
namespace Causality

open Probability

/-!
# Read the actual support obligations of a defined guarded expression

The paper's restriction to defined conditionals must be connected to the
computed observational expression, not replaced by an assumption of the
compiler's complete support tree.  This module reads primitive evaluation
support in the opposite direction: a defined guarded fold supports every
earlier printed prefix and every factor demanded by a positive printed
weight.  A defined quotient supplies its positive denominator, and a defined
finite marginal supports precisely its listed summands.

These are model-independent partial-expression facts.  They use neither
do-calculus soundness nor a causal-prefix equality, and they do not ask for
an inner derivation tree.  The factor may remain undefined on a zero-weight
branch.  The finite sum remains strict in its genuinely listed summands;
no absent summand is completed with an arbitrary rational value.

As with the public ID/IDC certificate APIs, the carrier universe here is
zero.  This puts no bound on the finite observed, hidden or noise alphabets.
The remaining recursive compiler proof must use these evaluation facts to
construct its inner data and connect the causal/displayed prefix guards.
That conclusion is not asserted by this module.
-/

variable {S : ObservedSignature.{0}}

namespace ProbabilityTerm

/-- Read support of the actual numerator of a defined printed quotient.
The witness is obtained by inspecting partial results, without choosing a
value from propositional existence. -/
noncomputable def divide_numerator_supportedAt
    {model : ExactModel S} {reference : S.Assignment} {numerator denominator : ProbabilityTerm S}
    (supported : (ProbabilityTerm.divide numerator denominator).SupportedAt model reference) :
    numerator.SupportedAt model reference :=
  ProbabilityResult.supported_numerator_of_divide supported

/-- A genuinely defined quotient exposes its displayed denominator's
positive value.  A supported zero numerator is permitted, whereas `0/0`
does not supply this witness. -/
noncomputable def divide_denominator_positiveAt
    {model : ExactModel S} {reference : S.Assignment} {numerator denominator : ProbabilityTerm S}
    (supported : (ProbabilityTerm.divide numerator denominator).SupportedAt model reference) :
    ProbabilityResult.PositiveSupportedValue (denominator.denote model reference) :=
  ProbabilityResult.positiveDenominatorOfSupportedDivide supported

/-- Every actually enumerated summand of a defined strict marginal is
defined.  Explicit finite-coordinate equality keeps list inspection
constructive; equality of arbitrary functions is not assumed. -/
noncomputable def marginal_summand_supportedAt
    {model : ExactModel S} {reference : S.Assignment} (nodes : NodeSet S) (term : ProbabilityTerm S)
    (variant : S.Assignment) (listed : variant ∈ marginalAssignments S nodes reference)
    (supported : (ProbabilityTerm.marginalize nodes term).SupportedAt model reference) : term.SupportedAt model variant := by
  letI : DecidableEq S.Assignment :=
    FiniteProduct.assignmentDecidableEq S.count S.Value S.valueDecidableEq
  exact ProbabilityResult.supported_map_of_mem_sum (marginalAssignments S nodes reference)
    (fun assignment => term.denote model assignment) variant listed supported

end ProbabilityTerm

namespace GuardedHostChain

/-- A defined successor fold always has a defined previous weight, including
when that weight is zero and the appended factor is genuinely undefined. -/
noncomputable def previous_supportedAt
    (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S)
    (model : ExactModel S) (reference : S.Assignment) (n : Nat) (bound : n + 1 ≤ S.count)
    (supported : (prefixTerm remaining factor (n + 1) bound).SupportedAt model reference) :
    (prefixTerm remaining factor n (Nat.le_trans (Nat.le_succ n) bound)).SupportedAt model reference := by
  let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
  cases selected : remaining node with
  | false =>
      simpa only [prefixTerm, node, selected, Bool.false_eq_true, if_false] using supported
  | true =>
      have weighted : (ProbabilityTerm.weightedMultiply
          (prefixTerm remaining factor n (Nat.le_trans (Nat.le_succ n) bound)) (factor node)).SupportedAt
            model reference := by
        simpa only [prefixTerm, node, selected, if_true] using supported
      exact ProbabilityResult.supported_weight_of_weightedMultiply weighted

/-- Read any earlier prefix of a defined fold by finite backward recursion.
Only printed-expression support is read: no causal kernel, global
positivity or compiler-data witness is an input to this construction. -/
noncomputable def prefix_supportedAt_of_supported_later
    (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S)
    (model : ExactModel S) (reference : S.Assignment) :
    (n : Nat) → (bound : n ≤ S.count) → (prefixTerm remaining factor n bound).SupportedAt model reference →
    (m : Nat) → (before : m ≤ n) →
      (prefixTerm remaining factor m (Nat.le_trans before bound)).SupportedAt model reference
  | 0, _bound, supported, m, before => by
      have empty : m = 0 := Nat.eq_zero_of_le_zero before
      subst m
      exact supported
  | n + 1, bound, supported, m, before => by
      by_cases last : m = n + 1
      · subst m
        exact supported
      · have earlier : m ≤ n := by omega
        let previous := previous_supportedAt remaining factor model reference n bound supported
        exact prefix_supportedAt_of_supported_later remaining factor model reference n
          (Nat.le_trans (Nat.le_succ n) bound) previous m earlier

/-- The full returned expression supports every one of its printed prefixes.
Proof-carrying bounds retain the exact original prefix syntax. -/
noncomputable def prefix_supportedAt_of_term_supported
    (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S)
    (model : ExactModel S) (reference : S.Assignment)
    (supported : (term remaining factor).SupportedAt model reference) (n : Nat) (bound : n ≤ S.count) :
    (prefixTerm remaining factor n bound).SupportedAt model reference :=
  prefix_supportedAt_of_supported_later remaining factor model reference S.count (Nat.le_refl _) supported n bound

/-- A positive printed predecessor weight cannot hide an undefined appended
factor.  On a zero weight there is intentionally no factor-support theorem. -/
noncomputable def factor_supportedAt_of_supported_successor
    (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S)
    (model : ExactModel S) (reference : S.Assignment) (node : Fin S.count) (selected : remaining node = true)
    (positive : ProbabilityResult.PositiveSupportedValue
      ((prefixTerm remaining factor node.val (Nat.le_of_lt node.isLt)).denote model reference))
    (supported : (prefixTerm remaining factor (node.val + 1) (Nat.succ_le_of_lt node.isLt)).SupportedAt model reference) :
    (factor node).SupportedAt model reference := by
  have weighted : (ProbabilityTerm.weightedMultiply
      (prefixTerm remaining factor node.val (Nat.le_of_lt node.isLt)) (factor node)).SupportedAt model reference := by
    simpa only [prefixTerm, selected, if_true] using supported
  exact ProbabilityResult.supported_factor_of_weightedMultiply positive weighted

/-- Read a demanded factor directly from support of the full printed output.
The positive-prefix premise is local and does not strengthen defined zeros
to a strictly positive complete observational distribution. -/
noncomputable def factor_supportedAt_of_term_supported
    (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S)
    (model : ExactModel S) (reference : S.Assignment) (node : Fin S.count) (selected : remaining node = true)
    (positive : ProbabilityResult.PositiveSupportedValue
      ((prefixTerm remaining factor node.val (Nat.le_of_lt node.isLt)).denote model reference))
    (supported : (term remaining factor).SupportedAt model reference) : (factor node).SupportedAt model reference :=
  factor_supportedAt_of_supported_successor remaining factor model reference node selected positive
    (prefix_supportedAt_of_term_supported remaining factor model reference supported (node.val + 1)
      (Nat.succ_le_of_lt node.isLt))

end GuardedHostChain

end Causality
end Thesis
