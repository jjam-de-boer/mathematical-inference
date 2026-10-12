import Thesis.CausalTransport.SupportAwareKernelCompilation

namespace Thesis
namespace Causality
namespace GuardedHostChain

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}

/-!
# Shared bounded compilation of a guarded host chain

This fold consumes independently derived host conditional factors.  They may
read one current host input or different recursively compiled component
inputs; the chain construction does not assume a reduction of the host joint.
Each selected vertex is appended in the observed topological order, with the
already compiled prefix as its weight.  Missing host positions leave the
prefix unchanged.  No strict-product permutation or quotient cancellation
is used, including when selected components interleave.

The support constructor keeps its two obligations distinct.  A positive
causal prefix demands the next factor's complete derivation tree.  A positive
displayed prefix demands support of its displayed next factor.  Neither is
required on a defined zero branch.  These callbacks are local ingredients;
the constructor itself builds the whole chain tree and every intermediate
unconditional prefix.  No semantic equality or global positivity is assumed.
-/

/-- Prefix-first fold over exactly the selected host positions. -/
def prefixTerm (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S) :
    (n : Nat) → n ≤ S.count → ProbabilityTerm S
  | 0, _ => unitProbabilityTerm S
  | n + 1, bound =>
      let previous := prefixTerm remaining factor n (Nat.le_trans (Nat.le_succ n) bound)
      let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
      if remaining node then .weightedMultiply previous (factor node) else previous

def term (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S) : ProbabilityTerm S :=
  prefixTerm remaining factor S.count (Nat.le_refl _)

/-- Only factors belonging to the host need action-free syntax. -/
theorem prefixTerm_actionFree (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S)
    (free : forall node, remaining node = true → (factor node).ActionFree)
    (n : Nat) (bound : n ≤ S.count) : (prefixTerm remaining factor n bound).ActionFree := by
  induction n with
  | zero => exact unitProbabilityTerm_actionFree S
  | succ n inductionHypothesis =>
      simp only [prefixTerm]
      split
      · rename_i selected
        exact ⟨inductionHypothesis _, free _ selected⟩
      · exact inductionHypothesis _

theorem term_actionFree (remaining : NodeSet S) (factor : Fin S.count → ProbabilityTerm S)
    (free : forall node, remaining node = true → (factor node).ActionFree) :
    (term remaining factor).ActionFree :=
  prefixTerm_actionFree remaining factor free S.count (Nat.le_refl _)

/-- Assemble actual factor derivations without postulating a host-joint
certificate.  The only probability split is the proved guarded chain rule;
the factor substitutions remain ordinary inspectable congruence nodes. -/
noncomputable def prefixDerivation
    (remaining action : NodeSet S) (outside : NodeSet.Disjoint action remaining)
    (factor : Fin S.count → ProbabilityTerm S)
    (factorDerivation : forall node, remaining node = true → PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩) (factor node)) :
    (n : Nat) → (bound : n ≤ S.count) → PathDoCalculusDerivation G
      (.kernel ⟨chainPrefix remaining n, action, NodeSet.empty⟩) (prefixTerm remaining factor n bound)
  | 0, _ => by
      let query : JointKernelQuery S := ⟨NodeSet.empty, action, NodeSet.disjoint_empty_right _⟩
      let separated := PathSpecification.PathDSeparated.of_isEmpty_left G (.bar action)
        NodeSet.empty action NodeSet.empty NodeSet.isEmpty_empty
      exact DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
        (by rw [chainPrefix_zero]; rfl) rfl (deleteActionRule3Derivation query separated)
  | n + 1, bound => by
      let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
      let previousBound : n ≤ S.count := Nat.le_trans (Nat.le_succ n) bound
      let previous := prefixDerivation remaining action outside factor factorDerivation n previousBound
      have prefixStep := chainPrefix_succ remaining n (Nat.lt_of_succ_le bound)
      -- This finite Boolean decision keeps the result type fixed.  In
      -- particular the support induction can expose the chosen constructor
      -- without a stuck dependent case-transport around the derivation.
      if selected : remaining node = true then
        have prefixSubset : NodeSet.Subset (chainPrefix remaining n) remaining :=
          fun _vertex member => (Bool.and_eq_true_iff.mp member).1
        let split : PathDoCalculusDerivation G
            (.kernel ⟨NodeSet.union (NodeSet.singleton node) (chainPrefix remaining n), action, NodeSet.empty⟩)
            (.weightedMultiply (.kernel ⟨chainPrefix remaining n, action, NodeSet.empty⟩)
              (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩)) :=
          DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G) rfl
            (by simp only [NodeSet.union_empty_right, chainCondition_eq_prefix, node])
            (DoCalculusDerivation.weightedChain (G := G) (separation := pathRuleSeparation G)
              action (NodeSet.singleton node) (chainPrefix remaining n) NodeSet.empty
              (FourWayDisjoint.of_empty_w action (NodeSet.singleton node) (chainPrefix remaining n)
                (NodeSet.disjoint_of_subset_right outside (NodeSet.singleton_subset_of_mem selected))
                (NodeSet.disjoint_of_subset_right outside prefixSubset)
                (disjoint_singleton_chainPrefix remaining node)))
        let congruence := DoCalculusDerivation.weightedMultiplyCongr (G := G)
          (separation := pathRuleSeparation G) previous (factorDerivation node selected)
        have nextPrefix : chainPrefix remaining (n + 1) =
            NodeSet.union (NodeSet.singleton node) (chainPrefix remaining n) := by
          simpa only [node, selected, if_true] using prefixStep
        exact DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
          (by rw [nextPrefix]) (by simp only [prefixTerm, node, selected, if_true])
          (DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G) split congruence)
      else
        have absent : remaining node = false := by
          cases value : remaining node with
          | false => rfl
          | true => exact False.elim (selected value)
        have samePrefix : chainPrefix remaining (n + 1) = chainPrefix remaining n := by
          simpa only [node, selected, if_neg] using prefixStep
        exact DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
          (by rw [samePrefix]) (by simp only [prefixTerm, node, absent, Bool.false_eq_true, if_false]) previous

/-- Construct the whole recursive prefix tree from only the branch-local
factor obligations.  Intrinsic unconditional support and the guarded kernel
identity handle null prefixes before any graph soundness theorem is applied. -/
noncomputable def prefix_supportedAt
    (correct : DSeparationCorrectness G)
    (remaining action : NodeSet S) (outside : NodeSet.Disjoint action remaining)
    (factor : Fin S.count → ProbabilityTerm S)
    (factorDerivation : forall node, remaining node = true → PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩) (factor node))
    (model : ExactModel S) (reference : S.Assignment)
    (sourceFactorSupport : forall node (selected : remaining node = true),
      ProbabilityResult.PositiveSupportedValue
        ((ProbabilityTerm.kernel ⟨chainPrefix remaining node.val, action, NodeSet.empty⟩).denote model reference) →
      LocalDerivationSupport model reference ((factorDerivation node selected).compile correct))
    (targetFactorSupport : forall node, remaining node = true →
      ProbabilityResult.PositiveSupportedValue
        ((prefixTerm remaining factor node.val (Nat.le_of_lt node.isLt)).denote model reference) →
      (factor node).SupportedAt model reference) :
    (n : Nat) → (bound : n ≤ S.count) → LocalDerivationSupport model reference
      ((prefixDerivation remaining action outside factor factorDerivation n bound).compile correct)
  | 0, _ => by
      let sourceSupported := Kernel.unconditional_supportedAt model NodeSet.empty action reference
      let initialSupported := Kernel.unconditional_supportedAt model (chainPrefix remaining 0) action reference
      let targetSupported := Kernel.unconditional_supportedAt model NodeSet.empty NodeSet.empty reference
      let query : JointKernelQuery S := ⟨NodeSet.empty, action, NodeSet.disjoint_empty_right _⟩
      let ruleSupported := ProbabilityTerm.SupportedAt.congr
        (JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw query) sourceSupported
      dsimp [prefixDerivation, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        deleteActionRule3Derivation]
      exact ⟨initialSupported, ⟨targetSupported,
        ⟨sourceSupported, ⟨targetSupported, ⟨ruleSupported, ⟨targetSupported, ()⟩⟩⟩⟩⟩⟩
  | n + 1, bound => by
      let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
      let previousBound : n ≤ S.count := Nat.le_trans (Nat.le_succ n) bound
      let previousSupport := prefix_supportedAt correct remaining action outside factor factorDerivation
        model reference sourceFactorSupport targetFactorSupport n previousBound
      cases selected : remaining node with
      | false =>
          have notSelected : ¬ remaining node = true := by
            rw [selected]
            exact Bool.false_ne_true
          let sourceSupported := Kernel.unconditional_supportedAt model (chainPrefix remaining (n + 1)) action reference
          have targetSupported : (prefixTerm remaining factor (n + 1) bound).SupportedAt model reference := by
            simpa only [prefixTerm, node, selected, Bool.false_eq_true, if_false] using previousSupport.endpoints.2
          dsimp [prefixDerivation, node]
          simp only [node] at notSelected
          simp only [notSelected]
          dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
          exact ⟨sourceSupported, ⟨targetSupported, previousSupport⟩⟩
      | true =>
          let previousNodes := chainPrefix remaining n
          let sourceSupported := Kernel.unconditional_supportedAt model (chainPrefix remaining (n + 1)) action reference
          let jointSupported := Kernel.unconditional_supportedAt model
            (NodeSet.union (NodeSet.singleton node) previousNodes) action reference
          let splitSupported := ProbabilityTerm.SupportedAt.of_equivalent
            (ProbabilityTerm.weightedChain_soundAt model action (NodeSet.singleton node) previousNodes NodeSet.empty reference)
            jointSupported
          have intermediate : (ProbabilityTerm.weightedMultiply
              (.kernel ⟨previousNodes, action, NodeSet.empty⟩)
              (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩)).SupportedAt model reference := by
            simpa only [NodeSet.union_empty_right, chainCondition_eq_prefix, node] using splitSupported
          let factorTree := sourceFactorSupport node selected
          let targetSupported := ProbabilityResult.weightedMultiply_supported previousSupport.endpoints.2
            (targetFactorSupport node selected)
          have displayedSupported : (prefixTerm remaining factor (n + 1) bound).SupportedAt model reference := by
            simpa only [prefixTerm, node, selected, if_true] using targetSupported
          dsimp [prefixDerivation, node]
          simp only [node] at selected
          simp only [selected, dif_pos]
          dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
          exact ⟨sourceSupported, ⟨displayedSupported,
            ⟨jointSupported, ⟨targetSupported,
              ⟨⟨jointSupported, ⟨intermediate, ⟨jointSupported, ⟨splitSupported, ()⟩⟩⟩⟩,
                ⟨intermediate, ⟨targetSupported, ⟨previousSupport, factorTree⟩⟩⟩⟩⟩⟩⟩⟩

/-- A whole-host reduction assembled from its independently derived factors.
Its formula stays in host order; support is constructed separately below. -/
noncomputable def reduction
    (remaining action : NodeSet S) (outside : NodeSet.Disjoint action remaining)
    (factor : Fin S.count → ProbabilityTerm S)
    (free : forall node, remaining node = true → (factor node).ActionFree)
    (factorDerivation : forall node, remaining node = true → PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩) (factor node)) :
    PublishedCurrentKernelReduction G remaining action where
  formula := term remaining factor
  actionFree := term_actionFree remaining factor free
  derivation := DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
    (by rw [chainPrefix_count]) rfl
    (prefixDerivation remaining action outside factor factorDerivation S.count (Nat.le_refl _))

/-- The complete support tree, including the final source reindexing. -/
noncomputable def reduction_supportedAt
    (correct : DSeparationCorrectness G)
    (remaining action : NodeSet S) (outside : NodeSet.Disjoint action remaining)
    (factor : Fin S.count → ProbabilityTerm S)
    (free : forall node, remaining node = true → (factor node).ActionFree)
    (factorDerivation : forall node, remaining node = true → PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, action, chainCondition remaining node⟩) (factor node))
    (model : ExactModel S) (reference : S.Assignment)
    (sourceFactorSupport : forall node (selected : remaining node = true),
      ProbabilityResult.PositiveSupportedValue
        ((ProbabilityTerm.kernel ⟨chainPrefix remaining node.val, action, NodeSet.empty⟩).denote model reference) →
      LocalDerivationSupport model reference ((factorDerivation node selected).compile correct))
    (targetFactorSupport : forall node, remaining node = true →
      ProbabilityResult.PositiveSupportedValue
        ((prefixTerm remaining factor node.val (Nat.le_of_lt node.isLt)).denote model reference) →
      (factor node).SupportedAt model reference) :
    LocalDerivationSupport model reference
      ((reduction remaining action outside factor free factorDerivation).derivation.compile correct) := by
  let prefixSupport := prefix_supportedAt correct remaining action outside factor factorDerivation
    model reference sourceFactorSupport targetFactorSupport S.count (Nat.le_refl _)
  let sourceSupported := Kernel.unconditional_supportedAt model remaining action reference
  dsimp [reduction, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨sourceSupported, ⟨prefixSupport.endpoints.2, prefixSupport⟩⟩

end GuardedHostChain
end Causality
end Thesis
