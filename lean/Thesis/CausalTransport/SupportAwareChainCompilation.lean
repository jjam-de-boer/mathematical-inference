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

The final section also assembles an ordinary published certificate for this
same formula.  Its syntax uses `weightedChain` and `weightedMultiplyCongr`;
the latter's recursive support tree demands a conditional subderivation only
on a positive prefix.  This is a genuine certificate in the existing language,
not a parallel interface accepting a semantic equality as an assumed leaf.
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

/-! ## Inspectable published certificates, including null prefix cells -/

/-- One explicit guarded chain step in any selected graph-model class.
The complete product's support follows from its intrinsic probability
identity; support of the isolated conditional at zero weight is not supplied.
This leaf uses no graph-dependent do-rule or global positivity premise. -/
private noncomputable def observationalGuardedChainStepCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (later earlier : NodeSet S) (disjoint : NodeSet.Disjoint later earlier) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.union later earlier, NodeSet.empty, NodeSet.empty⟩) := by
  let split : PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.union later earlier, NodeSet.empty, NodeSet.empty⟩) := {
    formula := .weightedMultiply
      (.kernel ⟨earlier, NodeSet.empty, NodeSet.empty⟩)
      (.kernel ⟨later, NodeSet.empty, NodeSet.union earlier NodeSet.empty⟩)
    actionFree := ⟨fun _ => rfl, fun _ => rfl⟩
    derivation := DoCalculusDerivation.weightedChain
      (separation := pathRuleSeparation G)
      NodeSet.empty later earlier NodeSet.empty
      ⟨NodeSet.disjoint_empty_left _, NodeSet.disjoint_empty_left _,
        NodeSet.disjoint_empty_left _, disjoint,
        NodeSet.disjoint_empty_right _, NodeSet.disjoint_empty_right _⟩
    supported := fun model _member assignment sourceSupported => by
      let targetSupported := ProbabilityTerm.SupportedAt.of_equivalent
        (ProbabilityTerm.weightedChain_soundAt model NodeSet.empty
          later earlier NodeSet.empty assignment) sourceSupported
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
      exact ⟨sourceSupported, ⟨targetSupported, ()⟩⟩
  }
  exact split.reindex rfl
    (show ProbabilityTerm.weightedMultiply
        (.kernel ⟨earlier, NodeSet.empty, NodeSet.empty⟩)
        (.kernel ⟨later, NodeSet.empty, earlier⟩) = split.formula by
      change _ = ProbabilityTerm.weightedMultiply _
        (.kernel ⟨later, NodeSet.empty, NodeSet.union earlier NodeSet.empty⟩)
      rw [NodeSet.union_empty_right])

/-- Keep exact compiled syntax beside its prefix certificate.  Endpoint
equalities use `reindex`, preserving an inspectable inner support tree rather
than hiding the tree behind a stuck dependent equality transport. -/
private structure GuardedChainPrefixCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining : NodeSet S)
    (n : Nat) (bound : n ≤ S.count) where
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩)
  formula_eq : certificate.formula = guardedChainPrefixTerm remaining n bound

/-- Assemble the guarded derivation by the same bounded host recursion as
the term compiler.  Replacing a prefix uses its already proved intrinsic
joint identity to establish target support; no causal soundness assumption
is used to manufacture support of an intermediate expression. -/
private noncomputable def guardedChainPrefixCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (remaining : NodeSet S) :
    (n : Nat) -> (bound : n ≤ S.count) ->
      GuardedChainPrefixCompilation C correct remaining n bound
  | 0, _ => by
      let base := PublishedIdentificationCertificate.refl
        (C := C) (correct := correct) (unitProbabilityTerm S)
        (unitProbabilityTerm_actionFree S)
      let certificate := base.reindex
        (show ProbabilityTerm.kernel
            ⟨chainPrefix remaining 0, NodeSet.empty, NodeSet.empty⟩ =
              unitProbabilityTerm S by rw [chainPrefix_zero]; rfl)
        rfl
      exact ⟨certificate, rfl⟩
  | n + 1, bound => by
      let node : Fin S.count := ⟨n, Nat.lt_of_succ_le bound⟩
      let previousBound : n ≤ S.count := Nat.le_trans (Nat.le_succ n) bound
      let previous := guardedChainPrefixCompilation (C := C) correct remaining n previousBound
      have prefixStep := chainPrefix_succ remaining n (Nat.lt_of_succ_le bound)
      cases selected : remaining node with
      | false =>
          have samePrefix : chainPrefix remaining (n + 1) = chainPrefix remaining n := by
            simpa only [node, selected, Bool.false_eq_true, if_false] using prefixStep
          let certificate := previous.certificate.reindex
            (show ProbabilityTerm.kernel
                ⟨chainPrefix remaining (n + 1), NodeSet.empty, NodeSet.empty⟩ =
                  .kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩ by
              rw [samePrefix]) rfl
          refine ⟨certificate, ?_⟩
          simpa only [guardedChainPrefixTerm, node, selected,
            Bool.false_eq_true, if_false, previousBound] using previous.formula_eq
      | true =>
          have nextPrefix : chainPrefix remaining (n + 1) =
              NodeSet.union (NodeSet.singleton node) (chainPrefix remaining n) := by
            simpa only [node, selected, if_true] using prefixStep
          let split := (observationalGuardedChainStepCertificate
            (C := C) correct (NodeSet.singleton node) (chainPrefix remaining n)
            (disjoint_singleton_chainPrefix remaining node)).reindex rfl
            (show ProbabilityTerm.weightedMultiply
                (.kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩)
                (.kernel (chainKernel remaining node)) = _ by
              change _ = ProbabilityTerm.weightedMultiply
                (.kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩)
                (.kernel ⟨NodeSet.singleton node, NodeSet.empty,
                  chainPrefix remaining n⟩)
              simp only [chainKernel, chainCondition_eq_prefix, node])
          let factor := PublishedIdentificationCertificate.refl
            (C := C) (correct := correct) (.kernel (chainKernel remaining node))
            (fun _ => rfl)
          let tail := PublishedIdentificationCertificate.weightedMultiplyWithSupport
            previous.certificate factor (fun model _member assignment sourceSupported => by
              have weights : ProbabilityTerm.EquivalentAt model
                  (.kernel ⟨chainPrefix remaining n, NodeSet.empty, NodeSet.empty⟩)
                  previous.certificate.formula assignment := by
                rw [previous.formula_eq]
                exact guardedChainPrefixTerm_soundAt model remaining assignment n previousBound
              exact ProbabilityTerm.SupportedAt.of_equivalent
                (ProbabilityResult.weightedMultiply_congr weights
                  (ProbabilityResult.refl _)) sourceSupported)
          let assembled := PublishedIdentificationCertificate.trans split tail
          let certificate := assembled.reindex
            (show ProbabilityTerm.kernel
                ⟨chainPrefix remaining (n + 1), NodeSet.empty, NodeSet.empty⟩ =
                  .kernel ⟨NodeSet.union (NodeSet.singleton node)
                    (chainPrefix remaining n), NodeSet.empty, NodeSet.empty⟩ by
              rw [nextPrefix])
            (show guardedChainPrefixTerm remaining (n + 1) bound = assembled.formula by
              change _ = ProbabilityTerm.weightedMultiply previous.certificate.formula
                (.kernel (chainKernel remaining node))
              rw [previous.formula_eq]
              simp only [guardedChainPrefixTerm, node, selected, if_true, previousBound])
          exact ⟨certificate, rfl⟩

/-- The ordinary published certificate for the whole guarded host joint.
Its model class is arbitrary: no global positivity or local-overlap premise
is required for an unconditional observational cylinder, including a zero
cell.  Graphical c-component extraction and recursive causal ID remain
separate obligations, not conclusions of this probability-algebra package. -/
structure PublishedObservationalGuardedChainCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining : NodeSet S) where
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨remaining, NodeSet.empty, NodeSet.empty⟩)
  formula_eq : certificate.formula = guardedChainTerm remaining

/-- Close the bounded induction at the actual signature count.  Empty and
gapped hosts use the same construction; no final vertex is chosen. -/
noncomputable def PublishedObservationalGuardedChainCompilation.ofModelClass
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining : NodeSet S) :
    PublishedObservationalGuardedChainCompilation C correct remaining := by
  let prefixes := guardedChainPrefixCompilation (C := C) correct remaining
    S.count (Nat.le_refl _)
  let certificate := prefixes.certificate.reindex
    (show ProbabilityTerm.kernel ⟨remaining, NodeSet.empty, NodeSet.empty⟩ =
        .kernel ⟨chainPrefix remaining S.count, NodeSet.empty, NodeSet.empty⟩ by
      rw [chainPrefix_count])
    (show guardedChainTerm remaining = prefixes.certificate.formula by
      exact prefixes.formula_eq.symm)
  exact ⟨certificate, rfl⟩

end Causality
end Thesis
