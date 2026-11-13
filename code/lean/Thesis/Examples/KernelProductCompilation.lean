import Thesis.CausalTransport.KernelProductCompilation
import Thesis.Causality.ProbabilityTermEquality
import Thesis.Examples.KernelRecursionCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentKernelSplitCompilation

open Probability
open FrontDoorIdentification
open CurrentKernelCompilation
open CurrentKernelComponentCompilation
open CurrentKernelRecursionCompilation

/-!
# Regression checks for the complete c-component product step

The first example groups the interleaving full-host components `{X,Y}` and
`{M}`.  The second identifies `(M,Y)` under `do(X)`: its free host has the two
singleton components `{M}` and `{Y}`, and each nested query is compiled by
the previously proved pruning/extraction constructors.  The final certificate
is checked against the actual replacement engine's complete returned syntax.

Denotational checks cover every positive compatible model at every assignment.
The engine comparison decides only finite expression syntax using the explicit
constructive equality procedures in `ProbabilityTermEquality`; it is neither
native evaluation nor an equality of sampled numerical denotations.
-/

/-! ## The full-host components genuinely interleave -/

/-- The independently extracted components read the original current input.
This family requires no component-compatible vertex order. -/
noncomputable def interleavingFamily :
    PublishedComponentKernelFamily (GraphModelClass.positive graph)
      graph.dSeparationCorrectness NodeSet.full NodeSet.empty where
  formula := fun component => chainProductFrom NodeSet.full (observationalJointTerm signature) component
  certificate := fun _component listed =>
    (PublishedCurrentKernelComponentCompilation.ofComponent
      (C := GraphModelClass.positive graph)
      graph.dSeparationCorrectness (fun member => member.2)
      NodeSet.full NodeSet.empty (ObservedGraph.KernelHostClosed.full graph) listed
      observationalInput initialInput.positive).certificate
  formula_eq := fun _component _listed => rfl
  positive := fun component _listed model member reference =>
    chainProductFrom_positiveSupportedValue model member.2 NodeSet.full
      (observationalJointTerm signature) component (initialInput.positive model member) reference

/-- Assemble the interleaving family using the general host-product theorem. -/
noncomputable def interleavingCompilation :=
  interleavingFamily.productCompilation (fun member => member.2)
    (ObservedGraph.KernelHostClosed.full graph)

/-- The actual graph partition is an exact factor permutation, independently
of any numerical model or particular derived formula. -/
theorem interleaving_partition_permutation :
    (NodeSet.members (NodeSet.full : NodeSet signature)).reverse.Perm
      ((graph.cComponents NodeSet.full).map
        (fun component => (NodeSet.members component).reverse)).flatten :=
  graph.cComponents_members_permutation NodeSet.full

noncomputable def interleavingCompilation_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model (observationalJointTerm signature)
      interleavingCompilation.certificate.formula reference :=
  let certificate := interleavingCompilation.certificate.compile
  certificate.derivation.denotational_soundAt
    (graph.publishedSoundness.primitive model member.1)
    (certificate.supported model member reference
      (member.2.kernelPositiveSupportedValue ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference).toSupported)

/-! ## The empty host needs no chosen component -/

/-- An empty signature has an empty partition.  All family obligations are
vacuous, including the data-valued certificate field; their empty-list
contradictions do not choose a vertex or a reduction. -/
noncomputable def emptyFamily :
    PublishedComponentKernelFamily (GraphModelClass.positive zeroGraph)
      zeroGraph.dSeparationCorrectness NodeSet.full NodeSet.empty where
  formula := fun _component => .zero
  certificate := fun _component absent => False.elim (List.not_mem_nil absent)
  formula_eq := fun _component absent => False.elim (List.not_mem_nil absent)
  positive := fun _component absent => False.elim (List.not_mem_nil absent)

/-- The general host-product construction returns the explicit positive
unit for the empty outer family.  This tests the graph/chain assembly too,
not merely the graph-independent empty-product regrouping operation. -/
noncomputable def emptyProductCompilation :=
  emptyFamily.productCompilation (fun member => member.2) (ObservedGraph.KernelHostClosed.full zeroGraph)

theorem emptyProductCompilation_formula : emptyProductCompilation.certificate.formula =
    unitProbabilityTerm zeroSignature := emptyProductCompilation.formula_eq

/-! ## Two genuine nested queries for the nonempty-action split -/

/-- The parent product query keeps both free variables after fixing `X`. -/
def jointQuery : JointKernelQuery signature where
  outcome := NodeSet.union (NodeSet.singleton mediator) (NodeSet.singleton y)
  action := NodeSet.singleton x
  action_outcome_disjoint := by
    intro node selected
    have same := (NodeSet.singleton_eq_true_iff x node).mp selected
    subst node
    rfl

/-- The mediator's ordinary ancestors are `X` and `M`.  Its recursive input
marginalizes away `Y` before extracting the terminal mediator component. -/
def mediatorAncestors : NodeSet signature :=
  graph.ancestralSet NodeSet.full (GraphMutilation.none signature) (NodeSet.singleton mediator)

noncomputable def mediatorPrunedInput :=
  initialInput.ancestral (fun member => member.2) (NodeSet.singleton mediator)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Membership is checked by explicit finite node-set equality, not a
classical function-equality instance. -/
theorem mediator_listed_after_pruning :
    NodeSet.singleton mediator ∈ graph.cComponents mediatorAncestors := by
  decide +kernel

/-- The terminal nested mediator certificate preserves the empty outer
marginal emitted by the engine, rather than simplifying its target syntax. -/
noncomputable def mediatorTerminalCertificate :=
  currentKernelComponentMarginalPublishedCertificate graph.dSeparationCorrectness
    (C := GraphModelClass.positive graph)
    (fun member => member.2) mediatorAncestors NodeSet.empty mediatorPrunedInput.closed
    mediator_listed_after_pruning (NodeSet.singleton mediator) (fun _ selected => selected)
    mediatorPrunedInput.certificate mediatorPrunedInput.positive

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Return the mediator reduction to its original-host complement action
using general ancestral pruning.  The only finite equality below aligns the
two displayed local/external action splits. -/
noncomputable def nestedMediatorCertificate :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨NodeSet.singleton mediator,
        NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full (NodeSet.singleton mediator)), NodeSet.empty⟩) :=
  currentKernelPrunePublishedCertificate initialInput (fun member => member.2)
    (NodeSet.diff NodeSet.full (NodeSet.singleton mediator)) (NodeSet.singleton mediator)
    (fun _ _ => rfl) (fun _ _ => rfl) (NodeSet.disjoint_diff_right _ _)
    (mediatorTerminalCertificate.reindex (by decide +kernel) rfl)

/-- The nested mediator formula is positive by finite marginalization and
current-input quotient positivity, independently of soundness. -/
noncomputable def nestedMediatorPositive
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityResult.PositiveSupportedValue (nestedMediatorCertificate.formula.denote model reference) :=
  ProbabilityTerm.marginalizePositiveSupportedValue model
    (NodeSet.diff (NodeSet.singleton mediator) (NodeSet.singleton mediator))
    (chainProductFrom mediatorAncestors mediatorPrunedInput.certificate.formula (NodeSet.singleton mediator))
    reference (chainProductFrom_positiveSupportedValue model member.2 mediatorAncestors
      mediatorPrunedInput.certificate.formula (NodeSet.singleton mediator)
      (mediatorPrunedInput.positive model member))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The existing containing-component and pruning regression identifies
`Y` under `do(X,M)`.  Reindex only the equal displayed complement action. -/
noncomputable def nestedYCertificate :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨NodeSet.singleton y,
        NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full (NodeSet.singleton y)), NodeSet.empty⟩) :=
  containingQueryCertificate.reindex (by decide +kernel) rfl

noncomputable def nestedYPositive
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityResult.PositiveSupportedValue (nestedYCertificate.formula.denote model reference) :=
  ProbabilityTerm.marginalizePositiveSupportedValue model
    (NodeSet.diff keptOutcomeHost (NodeSet.singleton y)) prunedInput.certificate.formula
    reference (prunedInput.positive model member)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The product branch's actual executable partition consists of these two
singleton components, in the engine's retained list order. -/
theorem free_partition_eq : graph.cComponents (NodeSet.diff NodeSet.full jointQuery.action) =
    [NodeSet.singleton mediator, NodeSet.singleton y] := by
  decide +kernel

/-- A total target function permits the engine's ordinary component-list map.
Only its two listed component values are consumed by the certificate fold. -/
noncomputable def recursiveComponentFormula (component : NodeSet signature) : ProbabilityTerm signature :=
  if NodeSet.equal component (NodeSet.singleton mediator) = true then
    nestedMediatorCertificate.formula else nestedYCertificate.formula

/-- Select the already constructed nested certificate by the Boolean finite
component test.  The partition equation proves the remaining case is `Y`;
no certificate is chosen from a propositional existence statement. -/
noncomputable def recursiveComponentCertificate (component : NodeSet signature)
    (listed : component ∈ graph.cComponents (NodeSet.diff NodeSet.full jointQuery.action)) :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨component, NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component), NodeSet.empty⟩) := by
  if isMediator : NodeSet.equal component (NodeSet.singleton mediator) = true then
    have same := (NodeSet.equal_eq_true_iff _ _).mp isMediator
    exact nestedMediatorCertificate.reindex (by rw [same]) rfl
  else
    have same : component = NodeSet.singleton y := by
      rw [free_partition_eq] at listed
      rcases List.mem_cons.mp listed with first | later
      · exact False.elim (isMediator ((NodeSet.equal_eq_true_iff _ _).mpr first))
      · rcases List.mem_cons.mp later with second | absent
        · exact second
        · exact False.elim (List.not_mem_nil absent)
    exact nestedYCertificate.reindex (by rw [same]) rfl

theorem recursiveComponentCertificate_formula (component : NodeSet signature)
    (listed : component ∈ graph.cComponents (NodeSet.diff NodeSet.full jointQuery.action)) :
    (recursiveComponentCertificate component listed).formula = recursiveComponentFormula component := by
  unfold recursiveComponentCertificate recursiveComponentFormula
  split <;> rfl

noncomputable def recursiveComponentPositive (component : NodeSet signature)
    (_listed : component ∈ graph.cComponents (NodeSet.diff NodeSet.full jointQuery.action))
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityResult.PositiveSupportedValue ((recursiveComponentFormula component).denote model reference) := by
  unfold recursiveComponentFormula
  split
  · exact nestedMediatorPositive model member reference
  · exact nestedYPositive model member reference

/-! ## Assemble and check the actual engine output -/

/-- The complete general split constructor is exercised with nonempty parent
action, two independently compiled nested queries, and their positive targets. -/
noncomputable def splitCompilation :=
  currentKernelSplitCompilation initialInput (fun member => member.2) jointQuery.action jointQuery.outcome
    (fun _ _ => rfl) (fun _ _ => rfl) jointQuery.action_outcome_disjoint
    recursiveComponentFormula recursiveComponentCertificate recursiveComponentCertificate_formula
    recursiveComponentPositive

/-- Read the actual returned expression, keeping a visible failure fallback. -/
def engineFormula : ProbabilityTerm signature :=
  match identifyJointKernel graph jointQuery with
  | .identified formula => formula
  | _ => .zero

set_option maxRecDepth 100000 in
/-- This is an actual successful engine run, not a hand-supplied formula. -/
theorem engine_identified : identifyJointKernel graph jointQuery = .identified engineFormula := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Exact generated syntax agrees with the product-branch certificate.
The comparison includes the recursively marginalized inputs and every
prefix denominator; ordinary Lean kernel reduction checks the finite test. -/
theorem splitCompilation_formula_matches_engine : splitCompilation.certificate.formula = engineFormula := by
  decide +kernel

/-- Check the complete assembled derivation at all assignments in every
positive compatible model, not just one front-door numerical example. -/
noncomputable def splitCompilation_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model jointQuery.sourceTerm engineFormula reference := by
  let certificate := splitCompilation.certificate.reindex
    (show jointQuery.sourceTerm = ProbabilityTerm.kernel
        ⟨jointQuery.outcome, NodeSet.union NodeSet.empty jointQuery.action, NodeSet.empty⟩ by
      rw [NodeSet.union_empty_left]; rfl) splitCompilation_formula_matches_engine.symm
  let compiled := certificate.compile
  exact compiled.derivation.denotational_soundAt (graph.publishedSoundness.primitive model member.1)
    (compiled.supported model member reference
      (member.2.kernelPositiveSupportedValue ⟨jointQuery.outcome, jointQuery.action, NodeSet.empty⟩ reference).toSupported)

end CurrentKernelSplitCompilation
end Examples
end Causality
end Thesis
