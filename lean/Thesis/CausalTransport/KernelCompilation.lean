import Thesis.CausalTransport.ChainCompilation
import Thesis.Causality.IdentificationKernel

namespace Thesis
namespace Causality

open Probability

/-!
# Supported compilation of the current recursive kernel

The replacement ID engine extracts a chain factor by taking two marginals
of its *current input expression*.  A recursive input need not be the host's
observational marginal: it may already describe a c-component under external
interventions.  This module keeps those external actions in the source kernel
and keeps the actual action-free expression in the target.

Two distinct invariants are used explicitly.  An input certificate supplies
an inspectable reduction of the source host kernel to the current expression;
a positive support value at every assignment makes the new prefix quotients
defined.  Positivity is propagated by finite sums, products, and division,
not inferred from do-calculus soundness.  The source kernels are supported
directly by SCM consistency and observational positivity.

The constructions below compile arbitrary host marginals, every individual
current-input chain factor, and the complete topological product on the host.
They are prerequisites for component extraction, not a claim that every
successful ID branch has already been compiled or that `PublishedCompleteness`
is inhabited.  No soundness module is imported.
-/

/-! ## Positivity of the exact replacement-engine expressions -/

/-- The two prefix marginals of an everywhere-positive current expression
are positive.  Consequently the exact quotient emitted by the replacement
engine is supported and positive, including its first-node total-mass
denominator.  No normalization or cancellation is assumed syntactically. -/
noncomputable def chainFactorFrom_positiveSupportedValue
    (model : ExactModel S) (remaining : NodeSet S)
    (current : ProbabilityTerm S) (node : Fin S.count)
    (inputPositive : forall assignment,
      ProbabilityResult.PositiveSupportedValue (current.denote model assignment))
    (reference : S.Assignment) :
    ProbabilityResult.PositiveSupportedValue
      ((chainFactorFrom remaining current node).denote model reference) :=
  (ProbabilityTerm.marginalizePositiveSupportedValue model
    (NodeSet.diff remaining
      (NodeSet.union (NodeSet.singleton node) (chainCondition remaining node)))
    current reference inputPositive).divide
    (ProbabilityTerm.marginalizePositiveSupportedValue model
      (NodeSet.diff remaining (chainCondition remaining node))
      current reference inputPositive)

/-- An engine product of positive factors has a positive supported value.
The empty product is the explicit empty-outcome kernel, and a singleton
product is its sole factor; neither case inserts an artificial multiplication
node into the syntax. -/
noncomputable def productTerms_map_positiveSupportedValue
    (model : ExactModel S) (positive : ObservationallyPositive model)
    (values : List X) (term : X -> ProbabilityTerm S) (reference : S.Assignment)
    (factorsPositive : forall value, value ∈ values ->
      ProbabilityResult.PositiveSupportedValue ((term value).denote model reference)) :
    ProbabilityResult.PositiveSupportedValue
      ((productTerms (values.map term)).denote model reference) := by
  induction values with
  | nil =>
      exact positive.kernelPositiveSupportedValue
        ⟨NodeSet.empty, NodeSet.empty, NodeSet.empty⟩ reference
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => exact factorsPositive head (List.mem_cons.mpr (Or.inl rfl))
      | cons next rest =>
          exact (factorsPositive head (List.mem_cons.mpr (Or.inl rfl))).multiply
            (inductionHypothesis (fun term member =>
              factorsPositive term (List.mem_cons.mpr (Or.inr member))))

/-- Restricting a recursive input to any component by current-input chain
factors preserves the everywhere-positive support invariant.  This is a
semantic statement about the generated expression, not the graph-dependent
claim that the expression identifies the component's interventional kernel. -/
noncomputable def chainProductFrom_positiveSupportedValue
    (model : ExactModel S) (positive : ObservationallyPositive model)
    (remaining : NodeSet S) (current : ProbabilityTerm S)
    (component : NodeSet S)
    (inputPositive : forall assignment,
      ProbabilityResult.PositiveSupportedValue (current.denote model assignment))
    (reference : S.Assignment) :
    ProbabilityResult.PositiveSupportedValue
      ((chainProductFrom remaining current component).denote model reference) := by
  exact productTerms_map_positiveSupportedValue model positive
    (NodeSet.members component).reverse
    (fun node => chainFactorFrom remaining current node) reference
    (fun node _member =>
      chainFactorFrom_positiveSupportedValue model remaining current node
        inputPositive reference)

/-! ## Marginals of an already compiled recursive input -/

/-- Compile a marginal of the current host kernel to the corresponding
marginal of its actual input expression.

`externalAction` is deliberately separate from the engine's local action:
it records intervention parameters already present in the recursive input.
The only geometry needed by this probability-algebra step is that those
parameters lie outside the host and that `kept` is a host subset.  Arbitrary
gaps, empty sets, and empty signatures are admitted.

The intermediate marginal still contains interventions, so it is *not*
pretended to be an action-free identification certificate.  Instead, the
primitive marginalization is composed with the lifted input certificate,
and its support tree is retained explicitly. -/
noncomputable def currentKernelMarginalPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction kept : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining)
    (keptSubset : NodeSet.Subset kept remaining)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨kept, externalAction, NodeSet.empty⟩) := by
  let removed := NodeSet.diff remaining kept
  let coveredInput : PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩) :=
    input.reindex
      (show ProbabilityTerm.kernel
          ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩ =
          .kernel ⟨remaining, externalAction, NodeSet.empty⟩ by
        rw [NodeSet.union_diff_eq keptSubset])
      rfl
  let lifted := coveredInput.marginalize removed
  let split : PathDoCalculusDerivation G
      (.kernel ⟨kept, externalAction, NodeSet.empty⟩)
      (.marginalize removed
        (.kernel ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩)) :=
    DoCalculusDerivation.marginalization
      (G := G) (separation := pathRuleSeparation G)
      externalAction kept removed NodeSet.empty
      (FourWayDisjoint.of_empty_w externalAction kept removed
        (NodeSet.disjoint_of_subset_right outside keptSubset)
        (NodeSet.disjoint_of_subset_right outside
          (NodeSet.diff_subset_left remaining kept))
        (NodeSet.disjoint_diff remaining kept))
  exact {
    formula := .marginalize removed input.formula
    actionFree := input.actionFree
    derivation := DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G) split lifted.derivation
    supported := fun model member reference sourceSupported => by
      let intermediate :=
        (ProbabilityTerm.marginalizePositiveSupportedValue model removed
          (.kernel ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩)
          reference (fun variant =>
            (obsPositive member).kernelPositiveSupportedValue
              ⟨NodeSet.union kept removed, externalAction, NodeSet.empty⟩
              variant)).toSupported
      let liftedSupported := lifted.supported model member reference intermediate
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules, split]
      exact ⟨sourceSupported, ⟨liftedSupported.endpoints.2,
        ⟨⟨sourceSupported, ⟨intermediate, ()⟩⟩, liftedSupported⟩⟩⟩
  }

/-- The current-input marginal compiler preserves the precise displayed
syntax required by the replacement engine. -/
theorem currentKernelMarginalPublishedCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction kept : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining)
    (keptSubset : NodeSet.Subset kept remaining)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩)) :
    (currentKernelMarginalPublishedCertificate correct obsPositive remaining
      externalAction kept outside keptSubset input).formula =
      .marginalize (NodeSet.diff remaining kept) input.formula := rfl

/-! ## Current-input prefix quotients with external interventions -/

/-- Compile the conditional factor of any selected host vertex to the exact
prefix quotient of the current input.

First apply primitive conditioning under `externalAction`.  Then compile
both resulting host-prefix kernels by marginalizing the *same* input
certificate.  The positive-input invariant supplies the target quotient's
denominator support directly; merely having supported operands would not
suffice.  All source-side conditioners are supported independently by finite
SCM consistency and observational positivity.

This construction works for an arbitrary certified recursive input and any
host subset.  It neither resets the input to an observational distribution
nor treats an external action coordinate as a random host vertex. -/
noncomputable def currentKernelFactorPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining)
    (node : Fin S.count) (selected : remaining node = true)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model ->
      forall reference,
        ProbabilityResult.PositiveSupportedValue
          (input.formula.denote model reference)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.singleton node, externalAction,
        chainCondition remaining node⟩) := by
  let earlier := chainCondition remaining node
  have earlierSubset : NodeSet.Subset earlier remaining := by
    intro vertex member
    exact (Bool.and_eq_true_iff.mp member).1
  have prefixSubset :
      NodeSet.Subset (NodeSet.union (NodeSet.singleton node) earlier) remaining :=
    NodeSet.union_subset (NodeSet.singleton_subset_of_mem selected) earlierSubset
  let numerator := currentKernelMarginalPublishedCertificate correct obsPositive
    remaining externalAction (NodeSet.union (NodeSet.singleton node) earlier)
    outside prefixSubset input
  let denominator := currentKernelMarginalPublishedCertificate correct obsPositive
    remaining externalAction earlier outside earlierSubset input
  let quotient := PublishedIdentificationCertificate.divideWithSupport
    numerator denominator (fun model member reference _sourceSupported =>
      (chainFactorFrom_positiveSupportedValue model remaining input.formula node
        (inputPositive model member) reference).toSupported)
  let split : PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node, externalAction,
        NodeSet.union earlier NodeSet.empty⟩)
      (.divide
        (.kernel ⟨NodeSet.union (NodeSet.singleton node) earlier,
          externalAction, NodeSet.empty⟩)
        (.kernel ⟨earlier, externalAction, NodeSet.empty⟩)) :=
    DoCalculusDerivation.conditioning
      (G := G) (separation := pathRuleSeparation G)
      externalAction (NodeSet.singleton node)
      earlier NodeSet.empty
      (FourWayDisjoint.of_empty_w externalAction (NodeSet.singleton node) earlier
        (NodeSet.disjoint_of_subset_right outside
          (NodeSet.singleton_subset_of_mem selected))
        (NodeSet.disjoint_of_subset_right outside earlierSubset)
        (disjoint_singleton_chainCondition remaining node))
  let compiled : PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.singleton node, externalAction,
        NodeSet.union earlier NodeSet.empty⟩) := {
    formula := quotient.formula
    actionFree := quotient.actionFree
    derivation := DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G) split quotient.derivation
    supported := fun model member reference sourceSupported => by
      let numeratorPositive := (obsPositive member).kernelPositiveSupportedValue
        ⟨NodeSet.union (NodeSet.singleton node) earlier,
          externalAction, NodeSet.empty⟩ reference
      let denominatorPositive := (obsPositive member).kernelPositiveSupportedValue
        ⟨earlier, externalAction, NodeSet.empty⟩ reference
      let intermediate := (numeratorPositive.divide denominatorPositive).toSupported
      let quotientSupported := quotient.supported model member reference intermediate
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules, split]
      exact ⟨sourceSupported, ⟨quotientSupported.endpoints.2,
        ⟨⟨sourceSupported, ⟨intermediate, ()⟩⟩, quotientSupported⟩⟩⟩
  }
  exact compiled.reindex
    (show ProbabilityTerm.kernel
        ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩ =
        .kernel ⟨NodeSet.singleton node, externalAction,
          NodeSet.union earlier NodeSet.empty⟩ by
      rw [NodeSet.union_empty_right])
    (show chainFactorFrom remaining input.formula node = compiled.formula by rfl)

/-- The factor compiler is formula-aligned, including the explicit first
factor denominator.  Equality is syntactic, not merely denotational. -/
theorem currentKernelFactorPublishedCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining)
    (node : Fin S.count) (selected : remaining node = true)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model ->
      forall reference,
        ProbabilityResult.PositiveSupportedValue
          (input.formula.denote model reference)) :
    (currentKernelFactorPublishedCertificate correct obsPositive remaining
      externalAction outside node selected input inputPositive).formula =
      chainFactorFrom remaining input.formula node := rfl

/-! ## Whole-host chain compilation with the exact current-input syntax -/

/-- An empty component contributes precisely the engine's unit term. -/
theorem chainProductFrom_empty (remaining : NodeSet S)
    (current : ProbabilityTerm S) :
    chainProductFrom remaining current NodeSet.empty = unitProbabilityTerm S := by
  have emptyMembers : NodeSet.members (NodeSet.empty : NodeSet S) = [] := by
    change (NodeSet.enumerated S).filter (fun _ => false) = []
    induction NodeSet.enumerated S with
    | nil => rfl
    | cons _ _ inductionHypothesis => exact inductionHypothesis
  unfold chainProductFrom
  rw [emptyMembers]
  rfl

/-- Crossing a selected host position puts its current-input quotient on
the left of the earlier product.  As with the observational chain compiler,
the first factor is not multiplied by a syntactic unit. -/
theorem chainProductFrom_prefix_succ_of_selected
    (remaining : NodeSet S) (current : ProbabilityTerm S)
    (n : Nat) (bound : n < S.count)
    (selected : remaining ⟨n, bound⟩ = true) :
    chainProductFrom remaining current (chainPrefix remaining (n + 1)) =
      match NodeSet.members (chainPrefix remaining n) with
      | [] => chainFactorFrom remaining current ⟨n, bound⟩
      | _ :: _ =>
          .multiply (chainFactorFrom remaining current ⟨n, bound⟩)
            (chainProductFrom remaining current (chainPrefix remaining n)) := by
  unfold chainProductFrom
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

/-- The empty host kernel reduces to the engine's action-free unit by rule
3 with an empty outcome.  The side condition is vacuous, not a new global
Markov hypothesis; both endpoint supports are retained below `eqCongr`. -/
private noncomputable def emptyHostCurrentKernelPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (externalAction : NodeSet S) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.empty, externalAction, NodeSet.empty⟩) := by
  let query : JointKernelQuery S :=
    ⟨NodeSet.empty, externalAction, NodeSet.disjoint_empty_right _⟩
  let separated := PathSpecification.PathDSeparated.of_isEmpty_left G
    (GraphMutilation.bar externalAction) NodeSet.empty externalAction NodeSet.empty
    NodeSet.isEmpty_empty
  exact {
    formula := unitProbabilityTerm S
    actionFree := unitProbabilityTerm_actionFree S
    derivation := deleteActionRule3Derivation query separated
    supported := fun model _member reference sourceSupported => by
      let unitSupported := emptyActionKernel_supportedAt model NodeSet.empty reference
      let ruleSourceSupported := ProbabilityTerm.SupportedAt.congr
        (JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw query) sourceSupported
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        deleteActionRule3Derivation]
      exact ⟨sourceSupported,
        ⟨unitSupported, ⟨ruleSourceSupported, ⟨unitSupported, ()⟩⟩⟩⟩
  }

/-- A prefix package carries syntactic formula equality through the numeric
induction.  Its source keeps the same external action at every prefix; the
host's missing positions never become extra random or action coordinates. -/
private structure CurrentKernelPrefixCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining externalAction : NodeSet S)
    (current : ProbabilityTerm S) (n : Nat) where
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨chainPrefix remaining n, externalAction, NodeSet.empty⟩)
  formula_eq : certificate.formula =
    chainProductFrom remaining current (chainPrefix remaining n)

/-- One topological induction compiles every finite host, including hosts
with gaps.  The inductive chain split is primitive probability algebra; each
new conditional factor is supplied by the already checked current-input
quotient compiler.  No multiplicative commutativity or normalization shortcut
is needed to align the target with the engine. -/
private noncomputable def currentKernelPrefixCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model ->
      forall reference,
        ProbabilityResult.PositiveSupportedValue
          (input.formula.denote model reference))
    (n : Nat) (bound : n ≤ S.count) :
    CurrentKernelPrefixCompilation C correct remaining externalAction
      input.formula n := by
  induction n with
  | zero =>
      let base := emptyHostCurrentKernelPublishedCertificate
        (C := C) correct externalAction
      let certificate := base.reindex
        (show ProbabilityTerm.kernel
            ⟨chainPrefix remaining 0, externalAction, NodeSet.empty⟩ =
            .kernel ⟨NodeSet.empty, externalAction, NodeSet.empty⟩ by
          rw [chainPrefix_zero])
        (show chainProductFrom remaining input.formula (chainPrefix remaining 0) =
            base.formula by rw [chainPrefix_zero, chainProductFrom_empty]; rfl)
      exact ⟨certificate, rfl⟩
  | succ n inductionHypothesis =>
      have beforeBound : n < S.count := by omega
      let previous := inductionHypothesis (Nat.le_of_lt beforeBound)
      cases selected : remaining ⟨n, beforeBound⟩ with
      | false =>
          let certificate := previous.certificate.reindex
            (show ProbabilityTerm.kernel
                ⟨chainPrefix remaining (n + 1), externalAction, NodeSet.empty⟩ =
                .kernel ⟨chainPrefix remaining n, externalAction, NodeSet.empty⟩ by
              rw [chainPrefix_succ remaining n beforeBound, selected]; rfl)
            (show chainProductFrom remaining input.formula
                (chainPrefix remaining (n + 1)) = previous.certificate.formula by
              rw [chainPrefix_succ remaining n beforeBound, selected]
              exact previous.formula_eq.symm)
          exact ⟨certificate, rfl⟩
      | true =>
          let factor := currentKernelFactorPublishedCertificate correct obsPositive
            remaining externalAction outside ⟨n, beforeBound⟩ selected input inputPositive
          cases members : NodeSet.members (chainPrefix remaining n) with
          | nil =>
              have emptyPrefix : chainPrefix remaining n = NodeSet.empty :=
                NodeSet.eq_empty_of_isEmpty (by
                  unfold NodeSet.isEmpty
                  rw [members]
                  rfl)
              let certificate := factor.reindex
                (show ProbabilityTerm.kernel
                    ⟨chainPrefix remaining (n + 1), externalAction, NodeSet.empty⟩ =
                    .kernel ⟨NodeSet.singleton ⟨n, beforeBound⟩, externalAction,
                      chainCondition remaining ⟨n, beforeBound⟩⟩ by
                  rw [chainPrefix_succ remaining n beforeBound, selected]
                  change ProbabilityTerm.kernel
                    ⟨NodeSet.union (NodeSet.singleton ⟨n, beforeBound⟩)
                      (chainPrefix remaining n), externalAction, NodeSet.empty⟩ =
                    .kernel ⟨NodeSet.singleton ⟨n, beforeBound⟩, externalAction,
                      chainPrefix remaining n⟩
                  rw [emptyPrefix, NodeSet.union_empty_right])
                (show chainProductFrom remaining input.formula
                    (chainPrefix remaining (n + 1)) = factor.formula by
                  rw [chainProductFrom_prefix_succ_of_selected remaining input.formula
                    n beforeBound selected, members]; rfl)
              exact ⟨certificate, rfl⟩
          | cons head tail =>
              have prefixSubset : NodeSet.Subset (chainPrefix remaining n) remaining := by
                intro node member
                exact (Bool.and_eq_true_iff.mp member).1
              let factorWithEmptyCondition := factor.reindex
                (show ProbabilityTerm.kernel
                    ⟨NodeSet.singleton ⟨n, beforeBound⟩, externalAction,
                      NodeSet.union (chainPrefix remaining n) NodeSet.empty⟩ =
                    .kernel ⟨NodeSet.singleton ⟨n, beforeBound⟩, externalAction,
                      chainCondition remaining ⟨n, beforeBound⟩⟩ by
                  rw [NodeSet.union_empty_right]; rfl)
                rfl
              let product := PublishedIdentificationCertificate.multiply
                factorWithEmptyCondition previous.certificate
              let split : PathDoCalculusDerivation G
                  (.kernel ⟨NodeSet.union (NodeSet.singleton ⟨n, beforeBound⟩)
                    (chainPrefix remaining n), externalAction, NodeSet.empty⟩)
                  (.multiply
                    (.kernel ⟨NodeSet.singleton ⟨n, beforeBound⟩, externalAction,
                      NodeSet.union (chainPrefix remaining n) NodeSet.empty⟩)
                    (.kernel ⟨chainPrefix remaining n, externalAction, NodeSet.empty⟩)) :=
                DoCalculusDerivation.chain
                  (G := G) (separation := pathRuleSeparation G)
                  externalAction (NodeSet.singleton ⟨n, beforeBound⟩)
                  (chainPrefix remaining n) NodeSet.empty
                  (FourWayDisjoint.of_empty_w externalAction
                    (NodeSet.singleton ⟨n, beforeBound⟩) (chainPrefix remaining n)
                    (NodeSet.disjoint_of_subset_right outside
                      (NodeSet.singleton_subset_of_mem selected))
                    (NodeSet.disjoint_of_subset_right outside prefixSubset)
                    (disjoint_singleton_chainPrefix remaining ⟨n, beforeBound⟩))
              let compiled : PublishedIdentificationCertificate C correct
                  (.kernel ⟨NodeSet.union (NodeSet.singleton ⟨n, beforeBound⟩)
                    (chainPrefix remaining n), externalAction, NodeSet.empty⟩) := {
                formula := product.formula
                actionFree := product.actionFree
                derivation := DoCalculusDerivation.trans
                  (G := G) (separation := pathRuleSeparation G) split product.derivation
                supported := fun model member reference sourceSupported => by
                  let leftPositive := (obsPositive member).kernelPositiveSupportedValue
                    ⟨NodeSet.singleton ⟨n, beforeBound⟩, externalAction,
                      NodeSet.union (chainPrefix remaining n) NodeSet.empty⟩ reference
                  let rightPositive := (obsPositive member).kernelPositiveSupportedValue
                    ⟨chainPrefix remaining n, externalAction, NodeSet.empty⟩ reference
                  let intermediate := (leftPositive.multiply rightPositive).toSupported
                  let productSupported := product.supported model member reference intermediate
                  dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules, split]
                  exact ⟨sourceSupported, ⟨productSupported.endpoints.2,
                    ⟨⟨sourceSupported, ⟨intermediate, ()⟩⟩, productSupported⟩⟩⟩
              }
              let certificate := compiled.reindex
                (show ProbabilityTerm.kernel
                    ⟨chainPrefix remaining (n + 1), externalAction, NodeSet.empty⟩ =
                    .kernel ⟨NodeSet.union (NodeSet.singleton ⟨n, beforeBound⟩)
                      (chainPrefix remaining n), externalAction, NodeSet.empty⟩ by
                  rw [chainPrefix_succ remaining n beforeBound, selected]; rfl)
                (show chainProductFrom remaining input.formula
                    (chainPrefix remaining (n + 1)) = compiled.formula by
                  rw [chainProductFrom_prefix_succ_of_selected remaining input.formula
                    n beforeBound selected, members]
                  change ProbabilityTerm.multiply _ _ =
                    ProbabilityTerm.multiply _ previous.certificate.formula
                  rw [previous.formula_eq]
                  rfl)
              exact ⟨certificate, rfl⟩

/-- A formula-aligned chain certificate for the actual recursive input,
with positive target values available for subsequent component restriction.
Unlike `PublishedObservationalChainCompilation`, the source may have external
interventions and the target factors are quotients of `current` itself. -/
structure PublishedCurrentKernelChainCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining externalAction : NodeSet S)
    (current : ProbabilityTerm S) where
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨remaining, externalAction, NodeSet.empty⟩)
  formula_eq : certificate.formula = chainProductFrom remaining current remaining
  positive : forall (model : ExactModel S), C.Mem model -> forall reference,
    ProbabilityResult.PositiveSupportedValue (certificate.formula.denote model reference)

/-- Assemble the general current-input chain compiler at the signature bound.
The same induction covers empty hosts, gapped hosts, and the zero-node
signature, without choosing a final selected vertex. -/
noncomputable def PublishedCurrentKernelChainCompilation.ofPositive
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model ->
      forall reference,
        ProbabilityResult.PositiveSupportedValue (input.formula.denote model reference)) :
    PublishedCurrentKernelChainCompilation C correct remaining externalAction input.formula := by
  let prefixes := currentKernelPrefixCompilation correct obsPositive remaining
    externalAction outside input inputPositive S.count (Nat.le_refl _)
  let certificate := prefixes.certificate.reindex
    (show ProbabilityTerm.kernel ⟨remaining, externalAction, NodeSet.empty⟩ =
        .kernel ⟨chainPrefix remaining S.count, externalAction, NodeSet.empty⟩ by
      rw [chainPrefix_count])
    (show chainProductFrom remaining input.formula remaining = prefixes.certificate.formula by
      rw [prefixes.formula_eq, chainPrefix_count])
  exact {
    certificate := certificate
    formula_eq := rfl
    positive := fun model member reference =>
      chainProductFrom_positiveSupportedValue model (obsPositive member)
        remaining input.formula remaining (inputPositive model member) reference
  }

end Causality
end Thesis
