import Thesis.CausalTransport.KernelCompilation
import Thesis.CausalTransport.KernelSeparation

namespace Thesis
namespace Causality

open Probability

/-!
# Supported extraction of a current-kernel c-component

The whole-host chain compiler alone does not identify a component.  Its
factors condition on every earlier host vertex, whereas a component kernel
fixes all vertices outside the component and conditions only on its own
earlier vertices.  This module bridges those two kernel shapes by actual
do-calculus steps, with graph side conditions proved in `KernelSeparation`.

For each component vertex, rule 3 first removes later outside-component
actions; rule 2 then exchanges the earlier outside-component actions for
observations.  The resulting host factor is compiled using the *current*
input expression.  All intermediate kernels retain their explicit support
trees, supplied by positivity rather than by a soundness assumption.

Parent closure is an invariant of the recursive host, not a condition on
its enumeration.  Bidirected closure admits a union of entire components
as well as a single listed component.  Neither connectedness nor a
consecutive topological interval is assumed in the general construction.
-/

/-! ## Partitioning the outside actions around a factor vertex -/

/-- Outside-component host vertices not preceding the selected vertex.
When that vertex belongs to the component, equality is excluded and every
selected vertex in this block is strictly later in topological order. -/
def chainLaterOutside (remaining component : NodeSet S)
    (node : Fin S.count) : NodeSet S :=
  NodeSet.diff (NodeSet.diff remaining component) (chainCondition remaining node)

/-- The outside action block is exactly its earlier and later pieces.
This equality concerns Boolean selections, including hosts with gaps. -/
theorem chainOutside_eq_earlier_union_later (remaining component : NodeSet S)
    (node : Fin S.count) :
    NodeSet.diff remaining component =
      NodeSet.union (NodeSet.diff (chainCondition remaining node) component)
        (chainLaterOutside remaining component node) := by
  funext vertex
  simp only [chainLaterOutside, NodeSet.diff, NodeSet.union, chainCondition]
  cases remaining vertex <;> cases component vertex <;>
    cases decide (vertex.val < node.val) <;> rfl

/-- Earlier outside-component observations together with the component's
own predecessors are precisely all host predecessors.  The subset premise
is essential: an arbitrary Boolean component could contain outside vertices. -/
theorem chainCondition_outside_union_inside (remaining component : NodeSet S)
    (componentSubset : NodeSet.Subset component remaining) (node : Fin S.count) :
    NodeSet.union (NodeSet.diff (chainCondition remaining node) component)
      (chainCondition component node) = chainCondition remaining node := by
  funext vertex
  cases inside : component vertex with
  | false => simp [NodeSet.union, NodeSet.diff, chainCondition, inside]
  | true =>
      simp [NodeSet.union, NodeSet.diff, chainCondition, inside,
        componentSubset vertex inside]

/-- The second outside block is genuinely later, not merely absent from
the earlier prefix.  Component membership of the factor vertex rules out
the equality case constructively. -/
theorem chainLaterOutside_after (remaining component : NodeSet S)
    (node : Fin S.count) (nodeInside : component node = true)
    {vertex : Fin S.count} (selected : chainLaterOutside remaining component node vertex = true) :
    node.val < vertex.val := by
  have parts := Bool.and_eq_true_iff.mp selected
  have outside := Bool.and_eq_true_iff.mp parts.1
  have noEarlier := parts.2
  by_cases before : vertex.val < node.val
  · have earlier : chainCondition remaining node vertex = true :=
      Bool.and_eq_true_iff.mpr ⟨outside.1, decide_eq_true before⟩
    change Bool.not (chainCondition remaining node vertex) = true at noEarlier
    rw [earlier] at noEarlier
    cases noEarlier
  · by_cases same : vertex.val = node.val
    · have equal : vertex = node := Fin.ext same
      subst vertex
      have notInside := outside.2
      change Bool.not (component node) = true at notInside
      rw [nodeInside] at notInside
      cases notInside
    · omega

/-! ## A component factor reduces to the actual current-input quotient -/

/-- The two graph-derived factor transformations, retained independently
of any compiled current expression.  Component extraction uses them forward;
the recursive product branch uses the same applications in reverse. -/
private structure ComponentFactorRuleApplications (G : ObservedGraph S)
    (remaining externalAction component : NodeSet S) (node : Fin S.count) where
  exchange : PathDoRuleApplication G
    (rule2Left externalAction (NodeSet.singleton node)
      (NodeSet.diff (chainCondition remaining node) component) (chainCondition component node))
    (rule2Right externalAction (NodeSet.singleton node)
      (NodeSet.diff (chainCondition remaining node) component) (chainCondition component node))
  deletion : PathDoRuleApplication G
    (rule3Left
      (NodeSet.union externalAction (NodeSet.diff (chainCondition remaining node) component))
      (NodeSet.singleton node) (chainLaterOutside remaining component node) (chainCondition component node))
    (rule3Right
      (NodeSet.union externalAction (NodeSet.diff (chainCondition remaining node) component))
      (NodeSet.singleton node) (chainLaterOutside remaining component node) (chainCondition component node))

/-- Both applications follow from parent and bidirected closure.  All
disjointness and path-separation obligations are proved here once; neither
direction of compilation receives an additional graph Boolean or semantic
independence hypothesis from its caller. -/
private noncomputable def componentFactorRuleApplicationsOfClosed
    {G : ObservedGraph S}
    (remaining externalAction component : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true ->
      remaining target = true -> G.bidirected source target = true -> component target = true)
    (node : Fin S.count) (nodeInside : component node = true) :
    ComponentFactorRuleApplications G remaining externalAction component node := by
  let earlier := chainCondition component node
  let exchanged := NodeSet.diff (chainCondition remaining node) component
  let later := chainLaterOutside remaining component node
  have earlierSubset : NodeSet.Subset earlier component :=
    fun _ selected => (Bool.and_eq_true_iff.mp selected).1
  have exchangedSubset : NodeSet.Subset exchanged remaining :=
    fun _ selected => (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp selected).1).1
  have laterSubset : NodeSet.Subset later (NodeSet.diff remaining component) :=
    NodeSet.diff_subset_left _ _
  have laterHost := laterSubset.trans (NodeSet.diff_subset_left remaining component)
  have outsideComponent : NodeSet.Disjoint exchanged component :=
    NodeSet.disjoint_diff_right _ _
  have exchangeDisjoint : FourWayDisjoint externalAction (NodeSet.singleton node)
      exchanged earlier := {
    xy := NodeSet.disjoint_of_subset_right closed.action_disjoint
      (NodeSet.singleton_subset_of_mem (componentSubset node nodeInside))
    xz := NodeSet.disjoint_of_subset_right closed.action_disjoint exchangedSubset
    xw := NodeSet.disjoint_of_subset_right closed.action_disjoint
      (earlierSubset.trans componentSubset)
    yz := NodeSet.disjoint_of_subset_right
      (disjoint_singleton_chainCondition remaining node) (NodeSet.diff_subset_left _ _)
    yw := disjoint_singleton_chainCondition component node
    zw := NodeSet.disjoint_of_subset_right outsideComponent earlierSubset
  }
  have earlierLater : NodeSet.Disjoint exchanged later := by
    intro vertex selected
    have before := (Bool.and_eq_true_iff.mp selected).1
    simp only [later, chainLaterOutside, NodeSet.diff, before, Bool.not_true, Bool.and_false]
  have laterEarlier : NodeSet.Disjoint later earlier :=
    NodeSet.disjoint_of_subset_right
      (NodeSet.Disjoint.of_subset_left (NodeSet.disjoint_diff_right remaining component)
        laterSubset) earlierSubset
  have deleteDisjoint : FourWayDisjoint (NodeSet.union externalAction exchanged)
      (NodeSet.singleton node) later earlier := {
    xy := NodeSet.disjoint_union_left_of exchangeDisjoint.xy exchangeDisjoint.yz.symm
    xz := NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint laterHost) earlierLater
    xw := NodeSet.disjoint_union_left_of exchangeDisjoint.xw exchangeDisjoint.zw
    yz := NodeSet.Disjoint.of_subset_left
      (NodeSet.disjoint_of_subset_right (NodeSet.disjoint_diff remaining component)
        laterSubset) (NodeSet.singleton_subset_of_mem nodeInside)
    yw := exchangeDisjoint.yw
    zw := laterEarlier
  }
  exact {
    exchange := DoRuleApplication.rule2 (G := G) (separation := pathRuleSeparation G)
      externalAction (NodeSet.singleton node) exchanged earlier exchangeDisjoint
      (G.pathDSeparated_rule2_outside_predecessors remaining externalAction component
        closed componentSubset bidirectedClosed node nodeInside)
    deletion := DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
      (NodeSet.union externalAction exchanged) (NodeSet.singleton node) later earlier
      deleteDisjoint
      (G.pathDSeparated_rule3_late_actions (NodeSet.union externalAction exchanged)
        later earlier node (fun _ selected => chainLaterOutside_after remaining component
          node nodeInside selected)
        (fun _ selected => Nat.le_of_lt
          (of_decide_eq_true (Bool.and_eq_true_iff.mp selected).2)))
  }

/-- Compile one factor of the externally intervened component kernel.

The source fixes `externalAction ∪ (remaining \ component)` and conditions
only on component predecessors.  The target is exactly the quotient emitted
by `chainFactorFrom remaining input.formula node`.  The shared graph package
above supplies both actual do-rule applications.

The construction is valid for unions of complete c-components too.  A
listed c-component supplies its subset and bidirected-closure premises from
the executable partition, as exposed by the wrapper below. -/
noncomputable def currentKernelComponentFactorPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction component : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true ->
      remaining target = true -> G.bidirected source target = true -> component target = true)
    (node : Fin S.count) (nodeInside : component node = true)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model -> forall reference,
      ProbabilityResult.PositiveSupportedValue (input.formula.denote model reference)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.singleton node,
        NodeSet.union externalAction (NodeSet.diff remaining component),
        chainCondition component node⟩) := by
  let earlier := chainCondition component node
  let exchanged := NodeSet.diff (chainCondition remaining node) component
  let later := chainLaterOutside remaining component node
  let rules := componentFactorRuleApplicationsOfClosed remaining externalAction component
    closed componentSubset bidirectedClosed node nodeInside
  let factor := currentKernelFactorPublishedCertificate correct obsPositive
    remaining externalAction closed.action_disjoint node (componentSubset node nodeInside)
    input inputPositive
  let exchangedFactor := factor.reindex
    (show ProbabilityTerm.kernel (rule2Right externalAction (NodeSet.singleton node)
        exchanged earlier) =
        .kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩ by
      change ProbabilityTerm.kernel ⟨NodeSet.singleton node, externalAction,
        NodeSet.union exchanged earlier⟩ = _
      rw [chainCondition_outside_union_inside remaining component componentSubset node])
    rfl
  let exchange := PublishedIdentificationCertificate.prependDoRuleOfPositive obsPositive
    rules.exchange exchangedFactor
  let deleted := PublishedIdentificationCertificate.prependDoRuleOfPositive obsPositive
    rules.deletion exchange
  exact deleted.reindex
    (show ProbabilityTerm.kernel ⟨NodeSet.singleton node,
        NodeSet.union externalAction (NodeSet.diff remaining component), earlier⟩ =
        .kernel (rule3Left (NodeSet.union externalAction exchanged)
          (NodeSet.singleton node) later earlier) by
      rw [chainOutside_eq_earlier_union_later remaining component node]
      simp only [rule3Left, NodeSet.union_assoc]
      rfl)
    (show chainFactorFrom remaining input.formula node = deleted.formula by rfl)

/-- Reduce a host conditional factor using an already identified component
factor.  This is the reverse graph bridge needed by the product branch.

No certificate for the entire host distribution is required: requiring one
would be circular when that distribution is precisely the product branch's
output.  The caller's component factor can target any action-free expression;
its exact target is preserved through the two reversed do-rule applications. -/
noncomputable def currentKernelHostFactorOfComponentPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction component : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true ->
      remaining target = true -> G.bidirected source target = true -> component target = true)
    (node : Fin S.count) (nodeInside : component node = true)
    (factor : PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.singleton node,
        NodeSet.union externalAction (NodeSet.diff remaining component),
        chainCondition component node⟩)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩) := by
  let earlier := chainCondition component node
  let exchanged := NodeSet.diff (chainCondition remaining node) component
  let later := chainLaterOutside remaining component node
  let rules := componentFactorRuleApplicationsOfClosed remaining externalAction component
    closed componentSubset bidirectedClosed node nodeInside
  let reindexed := factor.reindex
    (show ProbabilityTerm.kernel (rule3Left (NodeSet.union externalAction exchanged)
        (NodeSet.singleton node) later earlier) =
        .kernel ⟨NodeSet.singleton node,
          NodeSet.union externalAction (NodeSet.diff remaining component), earlier⟩ by
      rw [chainOutside_eq_earlier_union_later remaining component node]
      simp only [rule3Left, NodeSet.union_assoc]
      rfl) rfl
  let added := PublishedIdentificationCertificate.prependSymmetricDoRuleOfPositive obsPositive
    rules.deletion reindexed
  let exchange := PublishedIdentificationCertificate.prependSymmetricDoRuleOfPositive obsPositive
    rules.exchange added
  exact exchange.reindex
    (show ProbabilityTerm.kernel ⟨NodeSet.singleton node, externalAction,
        chainCondition remaining node⟩ =
        .kernel (rule2Right externalAction (NodeSet.singleton node) exchanged earlier) by
      change ProbabilityTerm.kernel ⟨NodeSet.singleton node, externalAction,
        chainCondition remaining node⟩ = .kernel ⟨NodeSet.singleton node, externalAction,
        NodeSet.union exchanged earlier⟩
      rw [chainCondition_outside_union_inside remaining component componentSubset node]) rfl

/-- Exact formula alignment for the component-factor compiler.  In
particular, the current expression is not reset to an observational marginal
when the source acquires outside-component interventions. -/
theorem currentKernelComponentFactorPublishedCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction component : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true ->
      remaining target = true -> G.bidirected source target = true -> component target = true)
    (node : Fin S.count) (nodeInside : component node = true)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model -> forall reference,
      ProbabilityResult.PositiveSupportedValue (input.formula.denote model reference)) :
    (currentKernelComponentFactorPublishedCertificate correct obsPositive remaining
      externalAction component closed componentSubset bidirectedClosed node nodeInside
      input inputPositive).formula = chainFactorFrom remaining input.formula node := rfl

/-! ## Assemble the whole extracted component -/

/-- The exact component expression emitted by current-kernel ID, together
with its inspectable derivation and the positive-support invariant needed
by the next recursive invocation.

The source intervenes on the discarded host vertices in addition to the
existing external action.  The formula continues to read `current` through
the original `remaining` host's prefix quotients.  These two different hosts
must not be silently interchanged. -/
structure PublishedCurrentKernelComponentCompilation
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G)
    (remaining externalAction component : NodeSet S) (current : ProbabilityTerm S) where
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨component,
      NodeSet.union externalAction (NodeSet.diff remaining component), NodeSet.empty⟩)
  formula_eq : certificate.formula = chainProductFrom remaining current component
  positive : forall (model : ExactModel S), C.Mem model -> forall reference,
    ProbabilityResult.PositiveSupportedValue (certificate.formula.denote model reference)

/-- Extract any bidirected-closed host subset using the same finite chain
fold as whole-host compilation.

The factor certificates above provide the missing graph-dependent content;
the shared fold supplies probability-algebra chain steps and their support.
Empty subsets are included without picking a component vertex or introducing
an artificial final factor.  Positivity of the exact target expression is
propagated through sums, quotients, and products of the positive current
input, independently of do-calculus soundness. -/
noncomputable def PublishedCurrentKernelComponentCompilation.ofClosed
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction component : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true ->
      remaining target = true -> G.bidirected source target = true -> component target = true)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model -> forall reference,
      ProbabilityResult.PositiveSupportedValue (input.formula.denote model reference)) :
    PublishedCurrentKernelComponentCompilation C correct
      remaining externalAction component input.formula := by
  let componentAction := NodeSet.union externalAction (NodeSet.diff remaining component)
  have outside : NodeSet.Disjoint componentAction component :=
    NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint componentSubset)
      (NodeSet.disjoint_diff_right remaining component)
  let certificate := currentKernelProductPublishedCertificate correct obsPositive
    remaining component componentAction outside input.formula
    (fun node selected => currentKernelComponentFactorPublishedCertificate correct
      obsPositive remaining externalAction component closed componentSubset bidirectedClosed
      node selected input inputPositive) (fun _ _ => rfl)
  exact {
    certificate := certificate
    formula_eq := rfl
    positive := fun model member reference =>
      chainProductFrom_positiveSupportedValue model (obsPositive member)
        remaining input.formula component (inputPositive model member) reference
  }

/-- The replacement engine's actual listed-component extraction has no
caller-supplied graph-separation obligations.  Both subset and bidirected
closure follow from membership in the executable host partition.

Host closure and a positive certified current input are the recursive
invariants.  The resulting source host again satisfies parent closure by
`KernelHostClosed.restrict`, and the returned positive field provides the
next current-input invariant. -/
noncomputable def PublishedCurrentKernelComponentCompilation.ofComponent
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model -> forall reference,
      ProbabilityResult.PositiveSupportedValue (input.formula.denote model reference)) :
    PublishedCurrentKernelComponentCompilation C correct
      remaining externalAction component input.formula :=
  PublishedCurrentKernelComponentCompilation.ofClosed correct obsPositive
    remaining externalAction component closed (cComponents_subset G remaining listed)
    (G.cComponents_bidirected_closed remaining listed) input inputPositive

/-! ## The terminal extraction branch also marginalizes its component -/

/-- Compile the exact marginal emitted by a terminal component-extraction
branch of current-kernel ID.

This is a general kernel construction: the outcome can be any subset of the
listed component, and external actions are retained.  The engine's branch
invariants must still relate this source action to the caller's original
query; those recursive invariants are not inferred from a terminal formula
alone.  The complementary marginal reads the extracted current expression,
never a fresh observational distribution. -/
noncomputable def currentKernelComponentMarginalPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining)
    (outcome : NodeSet S) (outcomeSubset : NodeSet.Subset outcome component)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model -> forall reference,
      ProbabilityResult.PositiveSupportedValue (input.formula.denote model reference)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome,
        NodeSet.union externalAction (NodeSet.diff remaining component), NodeSet.empty⟩) :=
  let extracted := PublishedCurrentKernelComponentCompilation.ofComponent correct
    obsPositive remaining externalAction closed listed input inputPositive
  let restrictedHost := closed.restrict component (cComponents_subset G remaining listed)
  currentKernelMarginalPublishedCertificate correct obsPositive component
    (NodeSet.union externalAction (NodeSet.diff remaining component)) outcome
    restrictedHost.action_disjoint outcomeSubset extracted.certificate

/-- The terminal component formula agrees syntactically with the
replacement engine, including the empty complementary marginal. -/
theorem currentKernelComponentMarginalPublishedCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (remaining externalAction : NodeSet S)
    (closed : G.KernelHostClosed remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining)
    (outcome : NodeSet S) (outcomeSubset : NodeSet.Subset outcome component)
    (input : PublishedIdentificationCertificate C correct
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩))
    (inputPositive : forall (model : ExactModel S), C.Mem model -> forall reference,
      ProbabilityResult.PositiveSupportedValue (input.formula.denote model reference)) :
    (currentKernelComponentMarginalPublishedCertificate correct obsPositive remaining
      externalAction closed listed outcome outcomeSubset input inputPositive).formula =
      .marginalize (NodeSet.diff component outcome)
        (chainProductFrom remaining input.formula component) := rfl

end Causality
end Thesis
