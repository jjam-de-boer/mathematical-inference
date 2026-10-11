import Thesis.CausalTransport.ChainCompilation
import Thesis.CausalTransport.SupportAwareChain

namespace Thesis
namespace Causality

open Probability

/-!
# Whole-host observational chain compilation without global positivity

The strict chain compiler requires every displayed conditional factor to be
supported.  That is too strong on zero-containing distributions: an earlier
prefix may have zero mass, although the complete joint cell has the valid
value zero.  Here the already compiled prefix is the *weight* of the next
conditional factor.  An undefined next factor is skipped only when that
prefix is a defined zero.

The induction uses the same `chainPrefix` and topological host enumeration as
the established compiler, including arbitrary gaps.  Its guarded product
order is deliberately different from the later-first strict product.  A
guarded product cannot be commuted or regrouped by the old strict algebra
rules, and this module makes no such identification of syntax.

The result is an action-free formula for the whole observational host joint,
valid in every finite latent SCM, with constructive support at every cell.
This is not c-component extraction or a completed zero-aware ID compiler:
extracting selected factors without their prefix weights still needs the
appropriate query-local overlap and graph-dependent derivation.
-/

/-- Compile the selected host positions below a finite numeric bound.  The
unit kernel seeds the empty prefix.  Each included vertex uses the preceding
compiled prefix as its weight; excluded vertices leave that prefix unchanged.
Every index is constructed from the explicit bound, never selected by choice. -/
def guardedChainPrefixTerm (remaining : NodeSet S) :
    (n : Nat) -> n ≤ S.count -> ProbabilityTerm S
  | 0, _ => unitProbabilityTerm S
  | n + 1, bound =>
      let previous := guardedChainPrefixTerm remaining n
        (Nat.le_trans (Nat.le_succ n) bound)
      let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
      if remaining node then
        .weightedMultiply previous (.kernel (chainKernel remaining node))
      else previous

/-- The complete guarded chain uses all signature positions while retaining
the exact selected host, even when that host has missing positions. -/
def guardedChainTerm (remaining : NodeSet S) : ProbabilityTerm S :=
  guardedChainPrefixTerm remaining S.count (Nat.le_refl _)

/-- Every displayed factor is observational, including factors whose
conditioner has zero mass.  The guard changes support, not causal syntax. -/
theorem guardedChainPrefixTerm_actionFree (remaining : NodeSet S)
    (n : Nat) (bound : n ≤ S.count) :
    (guardedChainPrefixTerm remaining n bound).ActionFree := by
  induction n with
  | zero => exact unitProbabilityTerm_actionFree S
  | succ n inductionHypothesis =>
      simp only [guardedChainPrefixTerm]
      split
      · exact ⟨inductionHypothesis _, fun _ => rfl⟩
      · exact inductionHypothesis _

theorem guardedChainTerm_actionFree (remaining : NodeSet S) :
    (guardedChainTerm remaining).ActionFree :=
  guardedChainPrefixTerm_actionFree remaining S.count (Nat.le_refl _)

/-- Each guarded prefix denotes its actual joint cylinder, including zero
joint cells.  The induction step first applies the kernel chain identity and
then replaces only its weight by the previously compiled prefix.  No support
of the next conditional is requested at a zero weight. -/
noncomputable def guardedChainPrefixTerm_soundAt
    (model : FiniteLatentSCM S) (remaining : NodeSet S)
    (reference : S.Assignment) (n : Nat) (bound : n ≤ S.count) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩)
      (guardedChainPrefixTerm remaining n bound) reference := by
  induction n with
  | zero =>
      simpa only [chainPrefix_zero, guardedChainPrefixTerm, unitProbabilityTerm] using
        ProbabilityResult.refl
          ((Kernel.mk (NodeSet.empty : NodeSet S) NodeSet.empty
            NodeSet.empty).denote model reference)
  | succ n inductionHypothesis =>
      let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
      let previousBound : n ≤ S.count := Nat.le_trans (Nat.le_succ n) bound
      let previous := guardedChainPrefixTerm remaining n previousBound
      have prefixStep := chainPrefix_succ remaining n (Nat.lt_of_succ_le bound)
      cases selected : remaining node with
      | false =>
          have samePrefix : chainPrefix remaining (n + 1) = chainPrefix remaining n := by
            simpa only [node, selected, Bool.false_eq_true, if_false] using prefixStep
          rw [samePrefix]
          simpa only [guardedChainPrefixTerm, node, selected,
            Bool.false_eq_true, if_false] using inductionHypothesis previousBound
      | true =>
          have nextPrefix : chainPrefix remaining (n + 1) =
              NodeSet.union (NodeSet.singleton node) (chainPrefix remaining n) := by
            simpa only [node, selected, if_true] using prefixStep
          have split : ProbabilityTerm.EquivalentAt model
              (.kernel ⟨NodeSet.union (NodeSet.singleton node)
                (chainPrefix remaining n), NodeSet.empty, NodeSet.empty⟩)
              (.weightedMultiply
                (.kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩)
                (.kernel (chainKernel remaining node))) reference := by
            simpa only [chainKernel, chainCondition_eq_prefix,
              NodeSet.union_empty_right, node] using
              ProbabilityTerm.weightedChain_soundAt model NodeSet.empty
                (NodeSet.singleton node) (chainPrefix remaining n) NodeSet.empty reference
          have weightsEquivalent := inductionHypothesis previousBound
          have assembled : ProbabilityTerm.EquivalentAt model
              (.kernel ⟨NodeSet.union (NodeSet.singleton node)
                (chainPrefix remaining n), NodeSet.empty, NodeSet.empty⟩)
              (.weightedMultiply previous
                (.kernel (chainKernel remaining node))) reference :=
            ProbabilityResult.trans split
              (ProbabilityResult.weightedMultiply_congr weightsEquivalent
                (ProbabilityResult.refl _))
          rw [nextPrefix]
          simpa only [guardedChainPrefixTerm, node, selected, if_true,
            previous, previousBound] using assembled

/-- The whole finite host joint has an observational guarded-chain formula
at every assignment, without observational positivity or a model-class
regularity assumption. -/
noncomputable def guardedChainTerm_soundAt (model : FiniteLatentSCM S)
    (remaining : NodeSet S) (reference : S.Assignment) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨remaining, NodeSet.empty, NodeSet.empty⟩)
      (guardedChainTerm remaining) reference := by
  simpa only [guardedChainTerm, chainPrefix_count] using
    guardedChainPrefixTerm_soundAt model remaining reference S.count (Nat.le_refl _)

/-- Read the actual host-cylinder probability from the compiled formula.
This constructs its rational value explicitly, so null cells need neither
global positivity nor a choice of conditional representative. -/
noncomputable def guardedChainTerm_supportedAt (model : FiniteLatentSCM S)
    (remaining : NodeSet S) (reference : S.Assignment) :
    (guardedChainTerm remaining).SupportedAt model reference :=
  ProbabilityTerm.SupportedAt.of_equivalent
    (guardedChainTerm_soundAt model remaining reference)
    ⟨((Kernel.mk remaining NodeSet.empty NodeSet.empty).distribution
        model reference).probVal (Kernel.agreesOn remaining reference),
      Kernel.unconditionalDenote model remaining NodeSet.empty reference⟩

end Causality
end Thesis
