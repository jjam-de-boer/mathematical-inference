import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

open Probability

/-!
# Topological chain compilation for arbitrary finite host sets

The success compiler needs a chain-rule derivation whose *syntax* agrees with
the ID engine, not merely a semantically equal product.  The engine's
`chainProduct` therefore lists later vertices first, as does the primitive
chain constructor.  This module develops the corresponding finite induction
without assuming that the host is a consecutive interval or the full graph.

A numeric prefix is only an induction device: the selected host may have
arbitrary gaps.  An absent vertex leaves the prefix unchanged; a present
vertex is peeled off on the left.  The first present vertex is handled by
reflexivity rather than by silently inserting a multiplication by the unit.
That distinction matters because `productTerms` represents a singleton list
by its sole term, not by a product with an empty factor.

This is probability-algebra infrastructure for the structural success
compiler.  It does not assert the c-component extraction theorem, does not
discard the recursive engine's current distribution, and does not assume
published soundness or completeness.
-/

/-! ## Finite host prefixes and their exact member lists -/

/-- The selected host vertices strictly before topological position `n`.
Unlike an interval, this prefix retains every gap in `remaining`. -/
def chainPrefix (remaining : NodeSet S) (n : Nat) : NodeSet S :=
  fun node => remaining node && decide (node.val < n)

/-- The empty numeric prefix contains no host vertex. -/
theorem chainPrefix_zero (remaining : NodeSet S) :
    chainPrefix remaining 0 = NodeSet.empty := by
  funext node
  simp [chainPrefix, NodeSet.empty]

/-- At the signature bound the prefix is the whole selected host. -/
theorem chainPrefix_count (remaining : NodeSet S) :
    chainPrefix remaining S.count = remaining := by
  funext node
  simp [chainPrefix, node.isLt]

/-- The engine's conditioner is exactly the host prefix preceding its node. -/
theorem chainCondition_eq_prefix (remaining : NodeSet S)
    (node : Fin S.count) :
    chainCondition remaining node = chainPrefix remaining node.val := rfl

/-- Enumerate the first `n` signature positions, then retain the selected
host vertices.  The bound is explicit, so this list contains actual observed
indices and never requires a default or a choice of representative. -/
private def chainPrefixMembers (remaining : NodeSet S) (n : Nat)
    (bound : n ≤ S.count) : List (Fin S.count) :=
  (List.ofFn fun i : Fin n =>
    (⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩ : Fin S.count)).filter remaining

/-- On an enumerated numeric prefix every listed index is below the bound,
so filtering by `chainPrefix` is the same as filtering by the host alone. -/
private theorem chainPrefix_filter_at_bound (remaining : NodeSet S)
    (n : Nat) (bound : n ≤ S.count) :
    (List.ofFn fun i : Fin n =>
      (⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩ : Fin S.count)).filter
        (chainPrefix remaining n) = chainPrefixMembers remaining n bound := by
  apply List.filter_congr
  intro node member
  rcases List.mem_ofFn.mp member with ⟨i, rfl⟩
  simp [chainPrefix, i.isLt]

/-- Filtering a longer enumeration by a shorter host prefix drops precisely
the positions beyond that prefix.  The proof removes the last enumerated
position, so the resulting order is preserved rather than reconstructed
from set membership. -/
private theorem chainPrefix_filter_enumeration (remaining : NodeSet S)
    (m : Nat) (bound : m ≤ S.count) (n : Nat) (shorter : n ≤ m) :
    (List.ofFn fun i : Fin m =>
      (⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩ : Fin S.count)).filter
        (chainPrefix remaining n) =
      chainPrefixMembers remaining n (Nat.le_trans shorter bound) := by
  induction m generalizing n with
  | zero =>
      have zero : n = 0 := Nat.eq_zero_of_le_zero shorter
      subst n
      simp [chainPrefixMembers]
  | succ m inductionHypothesis =>
      by_cases atBound : n = m + 1
      · subst n
        exact chainPrefix_filter_at_bound remaining (m + 1) bound
      · have shorter' : n ≤ m := by omega
        rw [List.ofFn_succ_last, List.filter_append]
        have lastExcluded :
            chainPrefix remaining (n := n)
              (⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) bound⟩ :
                Fin S.count) = false := by
          simp [chainPrefix, show ¬ m < n by omega]
        simp only [Fin.val_last, Fin.val_castSucc, List.filter_cons,
          lastExcluded, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
          List.append_nil]
        exact inductionHypothesis (Nat.le_trans (Nat.le_succ m) bound)
          n shorter'

/-- The ordinary graph member list of a host prefix is the filtered numeric
enumeration above.  Equality here records the topological order as well as
membership; that is what aligns the chain derivation with the engine syntax. -/
private theorem members_chainPrefix (remaining : NodeSet S) (n : Nat)
    (bound : n ≤ S.count) :
    NodeSet.members (chainPrefix remaining n) =
      chainPrefixMembers remaining n bound := by
  exact chainPrefix_filter_enumeration remaining S.count (Nat.le_refl _)
    n bound

/-- Crossing one signature position appends that vertex exactly when it is
selected in the host.  No consecutive-host hypothesis is used. -/
theorem members_chainPrefix_succ (remaining : NodeSet S) (n : Nat)
    (bound : n < S.count) :
    NodeSet.members (chainPrefix remaining (n + 1)) =
      if remaining ⟨n, bound⟩ then
        NodeSet.members (chainPrefix remaining n) ++ [⟨n, bound⟩]
      else NodeSet.members (chainPrefix remaining n) := by
  rw [members_chainPrefix remaining (n + 1) (Nat.succ_le_of_lt bound),
    members_chainPrefix remaining n (Nat.le_of_lt bound)]
  unfold chainPrefixMembers
  rw [List.ofFn_succ_last, List.filter_append]
  cases selected : remaining ⟨n, bound⟩ <;>
    simp [selected]

/-- The next selected vertex is disjoint from its earlier host prefix. -/
theorem disjoint_singleton_chainPrefix (remaining : NodeSet S)
    (node : Fin S.count) :
    NodeSet.Disjoint (NodeSet.singleton node)
      (chainPrefix remaining node.val) :=
  disjoint_singleton_chainCondition remaining node

/-- The set-level counterpart of `members_chainPrefix_succ`.  The union is
written with the new vertex on the left to match the primitive chain rule. -/
theorem chainPrefix_succ (remaining : NodeSet S) (n : Nat)
    (bound : n < S.count) :
    chainPrefix remaining (n + 1) =
      if remaining ⟨n, bound⟩ then
        NodeSet.union (NodeSet.singleton ⟨n, bound⟩) (chainPrefix remaining n)
      else chainPrefix remaining n := by
  funext node
  by_cases same : node = (⟨n, bound⟩ : Fin S.count)
  · subst node
    cases selected : remaining ⟨n, bound⟩ <;>
      simp [chainPrefix, NodeSet.union, NodeSet.singleton, selected]
  · have different : node.val ≠ n := fun equal => same (Fin.ext equal)
    have cutoff : (node.val < n + 1) ↔ (node.val < n) := by
      constructor
      · intro belowSuccessor
        have belowOrEqual := Nat.le_of_lt_succ belowSuccessor
        cases Nat.lt_or_eq_of_le belowOrEqual with
        | inl below => exact below
        | inr equal => exact False.elim (different equal)
      · exact fun below => Nat.lt_succ_of_lt below
    cases remaining ⟨n, bound⟩ <;>
      simp [chainPrefix, NodeSet.union, NodeSet.singleton, same, cutoff]

/-- An absent position changes neither the selected prefix nor its product. -/
theorem chainProduct_prefix_succ_of_absent (remaining : NodeSet S)
    (n : Nat) (bound : n < S.count)
    (absent : remaining ⟨n, bound⟩ = false) :
    chainProduct remaining (chainPrefix remaining (n + 1)) =
      chainProduct remaining (chainPrefix remaining n) := by
  rw [chainPrefix_succ remaining n bound, absent]
  rfl

/-- A selected position supplies the next later-first factor.  The explicit
list match preserves `productTerms`' singleton convention: the first factor
is not multiplied by an artificial unit term. -/
theorem chainProduct_prefix_succ_of_selected (remaining : NodeSet S)
    (n : Nat) (bound : n < S.count)
    (selected : remaining ⟨n, bound⟩ = true) :
    chainProduct remaining (chainPrefix remaining (n + 1)) =
      match NodeSet.members (chainPrefix remaining n) with
      | [] => .kernel (chainKernel remaining ⟨n, bound⟩)
      | _ :: _ =>
          .multiply (.kernel (chainKernel remaining ⟨n, bound⟩))
            (chainProduct remaining (chainPrefix remaining n)) := by
  unfold chainProduct
  rw [members_chainPrefix_succ remaining n bound, selected]
  simp only [↓reduceIte, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.map_cons]
  cases members : NodeSet.members (chainPrefix remaining n) with
  | nil => rfl
  | cons head tail =>
      apply productTerms_cons
      intro empty
      have lengthEqual := congrArg List.length empty
      simp only [List.length_map, List.length_reverse,
        List.length_cons, List.length_nil] at lengthEqual
      exact Nat.succ_ne_zero _ lengthEqual

/-! ## Supported probability-algebra compilation -/

/-- Split an observational joint into a later block conditioned on its
earlier block and the earlier block's marginal.  The only regularity premise
is observational positivity in the selected model class; all intermediate
conditioners are observational cylinders, whose positivity is already proved
in `Completeness`. -/
private noncomputable def observationalChainStepPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (later earlier : NodeSet S) (disjoint : NodeSet.Disjoint later earlier) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.union later earlier, NodeSet.empty, NodeSet.empty⟩) := by
  let split : PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.union later earlier, NodeSet.empty, NodeSet.empty⟩) := {
    formula := .multiply
      (.kernel ⟨later, NodeSet.empty, NodeSet.union earlier NodeSet.empty⟩)
      (.kernel ⟨earlier, NodeSet.empty, NodeSet.empty⟩)
    actionFree := ⟨fun _ => rfl, fun _ => rfl⟩
    derivation := DoCalculusDerivation.chain
      (separation := pathRuleSeparation G)
      NodeSet.empty later earlier NodeSet.empty
      ⟨NodeSet.disjoint_empty_left _, NodeSet.disjoint_empty_left _,
        NodeSet.disjoint_empty_left _, disjoint,
        NodeSet.disjoint_empty_right _, NodeSet.disjoint_empty_right _⟩
    supported := fun model member assignment sourceSupported => by
      let leftSupported := observationalConditional_supportedAt model
        (obsPositive member) later (NodeSet.union earlier NodeSet.empty)
        assignment
      let rightSupported := observationalConditional_supportedAt model
        (obsPositive member) earlier NodeSet.empty assignment
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
      exact ⟨sourceSupported,
        ⟨ProbabilityTerm.multiply_supportedAt leftSupported rightSupported, ()⟩⟩
  }
  exact split.reindex rfl
    (show ProbabilityTerm.multiply
        (.kernel ⟨later, NodeSet.empty, earlier⟩)
        (.kernel ⟨earlier, NodeSet.empty, NodeSet.empty⟩) = split.formula by
      change _ = ProbabilityTerm.multiply
        (.kernel ⟨later, NodeSet.empty, NodeSet.union earlier NodeSet.empty⟩) _
      rw [NodeSet.union_empty_right])

/-- Internal induction package.  Formula equality is retained explicitly so
composition never substitutes a merely equivalent product for the precise
term returned by the engine. -/
private structure ChainPrefixCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining : NodeSet S) (n : Nat) where
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩)
  formula_eq : certificate.formula =
    chainProduct remaining (chainPrefix remaining n)

/-- Compile all selected vertices before a numeric bound.  This is one
induction for every finite host, including the empty host and hosts with
arbitrary topological gaps.  The support tree is composed with the generic
certificate operations rather than reconstructed by denotational soundness. -/
private noncomputable def chainPrefixCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining : NodeSet S) (n : Nat) (bound : n ≤ S.count) :
    ChainPrefixCompilation C correct remaining n := by
  induction n with
  | zero =>
      let base := PublishedIdentificationCertificate.refl
        (C := C) (correct := correct) (unitProbabilityTerm S)
        (unitProbabilityTerm_actionFree S)
      let certificate := base.reindex
        (show ProbabilityTerm.kernel
            ⟨chainPrefix remaining 0, NodeSet.empty, NodeSet.empty⟩ =
            unitProbabilityTerm S by rw [chainPrefix_zero]; rfl)
        (show chainProduct remaining (chainPrefix remaining 0) = base.formula by
          unfold chainProduct
          rw [members_chainPrefix remaining 0 (Nat.zero_le _)]
          simp only [chainPrefixMembers, List.ofFn_zero, List.filter_nil,
            List.reverse_nil, List.map_nil]
          rfl)
      exact ⟨certificate, rfl⟩
  | succ n inductionHypothesis =>
      have beforeBound : n < S.count := by omega
      let previous := inductionHypothesis (Nat.le_of_lt beforeBound)
      cases selected : remaining ⟨n, beforeBound⟩ with
      | false =>
          let certificate := previous.certificate.reindex
            (show ProbabilityTerm.kernel
                ⟨chainPrefix remaining (n + 1), NodeSet.empty, NodeSet.empty⟩ =
                .kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩ by
              rw [chainPrefix_succ remaining n beforeBound, selected]; rfl)
            (show chainProduct remaining (chainPrefix remaining (n + 1)) =
                previous.certificate.formula by
              rw [chainProduct_prefix_succ_of_absent remaining n beforeBound
                selected, previous.formula_eq])
          exact ⟨certificate, rfl⟩
      | true =>
          cases members : NodeSet.members (chainPrefix remaining n) with
          | nil =>
              have emptyPrefix : chainPrefix remaining n = NodeSet.empty :=
                NodeSet.eq_empty_of_isEmpty (by
                  unfold NodeSet.isEmpty
                  rw [members]
                  rfl)
              let first := PublishedIdentificationCertificate.refl
                (C := C) (correct := correct)
                (.kernel (chainKernel remaining ⟨n, beforeBound⟩))
                (fun _ => rfl)
              let certificate := first.reindex
                (show ProbabilityTerm.kernel
                    ⟨chainPrefix remaining (n + 1), NodeSet.empty,
                    NodeSet.empty⟩ =
                    .kernel (chainKernel remaining ⟨n, beforeBound⟩) by
                  rw [chainPrefix_succ remaining n beforeBound, selected]
                  simp only [↓reduceIte, emptyPrefix, NodeSet.union_empty_right]
                  unfold chainKernel
                  change _ = ProbabilityTerm.kernel
                    ⟨_, NodeSet.empty, chainPrefix remaining n⟩
                  rw [emptyPrefix])
                (show chainProduct remaining (chainPrefix remaining (n + 1)) =
                    first.formula by
                  rw [chainProduct_prefix_succ_of_selected remaining n
                    beforeBound selected, members]; rfl)
              exact ⟨certificate, rfl⟩
          | cons head tail =>
              let split := observationalChainStepPublishedCertificate correct
                obsPositive (NodeSet.singleton ⟨n, beforeBound⟩)
                (chainPrefix remaining n)
                (disjoint_singleton_chainPrefix remaining ⟨n, beforeBound⟩)
              let compiledTail := PublishedIdentificationCertificate.multiply
                (PublishedIdentificationCertificate.refl
                  (C := C) (correct := correct)
                  (.kernel (chainKernel remaining ⟨n, beforeBound⟩))
                  (fun _ => rfl))
                previous.certificate
              let compiled := PublishedIdentificationCertificate.trans split
                compiledTail
              let certificate := compiled.reindex
                (show ProbabilityTerm.kernel
                    ⟨chainPrefix remaining (n + 1), NodeSet.empty, NodeSet.empty⟩ =
                    .kernel ⟨NodeSet.union (NodeSet.singleton ⟨n, beforeBound⟩)
                      (chainPrefix remaining n), NodeSet.empty, NodeSet.empty⟩ by
                  rw [chainPrefix_succ remaining n beforeBound, selected]; rfl)
                (show chainProduct remaining (chainPrefix remaining (n + 1)) =
                    compiled.formula by
                  rw [chainProduct_prefix_succ_of_selected remaining n
                    beforeBound selected, members]
                  change ProbabilityTerm.multiply _ _ =
                    ProbabilityTerm.multiply _ previous.certificate.formula
                  rw [previous.formula_eq]
                  rfl)
              exact ⟨certificate, rfl⟩

/-- An observational chain certificate whose displayed formula is exactly
`chainProduct remaining remaining`.  The source is the observational joint
on the selected host, not an arbitrary recursive ID input distribution. -/
structure PublishedObservationalChainCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining : NodeSet S) where
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨remaining, NodeSet.empty, NodeSet.empty⟩)
  formula_eq : certificate.formula = chainProduct remaining remaining

/-- Compile the ordinary chain rule on any finite host.  Taking the prefix
bound to `S.count` closes the induction without choosing a last host member,
so the same construction covers the zero-node signature and the empty host. -/
noncomputable def PublishedObservationalChainCompilation.ofPositive
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining : NodeSet S) :
    PublishedObservationalChainCompilation C correct remaining := by
  let prefixes := chainPrefixCompilation correct obsPositive remaining S.count
    (Nat.le_refl _)
  let certificate := prefixes.certificate.reindex
    (show ProbabilityTerm.kernel ⟨remaining, NodeSet.empty, NodeSet.empty⟩ =
        .kernel ⟨chainPrefix remaining S.count, NodeSet.empty, NodeSet.empty⟩ by
      rw [chainPrefix_count])
    (show chainProduct remaining remaining = prefixes.certificate.formula by
      rw [prefixes.formula_eq, chainPrefix_count])
  exact ⟨certificate, rfl⟩

/-- The positive graph-model class supplies the observational regularity
premise directly.  No do-calculus soundness theorem is used to establish
support of the chain compiler's intermediate formulas. -/
noncomputable def ObservedGraph.observationalChainCompilation
    (G : ObservedGraph S) (remaining : NodeSet S) :
    PublishedObservationalChainCompilation (GraphModelClass.positive G)
      G.dSeparationCorrectness remaining :=
  PublishedObservationalChainCompilation.ofPositive
    (C := GraphModelClass.positive G) G.dSeparationCorrectness
    (fun member => member.2) remaining

end Causality
end Thesis
