import Thesis.CausalTransport.Soundness
import Thesis.CausalTransport.Completeness
import Thesis.Causality.IdentificationKernel

namespace Thesis
namespace Causality
namespace Examples
namespace FrontDoorIdentification

open Probability

/-!
# Positive front-door regression for executable identification

This module records a load-bearing discrepancy in the legacy ID engine,
not an extra assumption and not a completed identification theorem.  In the
three-node graph `X → M → Y`, with `X ↔ Y`, `identifyJoint` returns a formula
for `P(Y | do(X))`.  In the explicit positive compatible model below the
true value at `X = Y = true` is `1/2`, whereas that formula has value `9/16`.
Both claims are checked by Lean's kernel, including all divisions.

The shared root contains an unbiased bit `U` and an independent noise bit
`E` with probability `1/4` of being true.  The private mediator root supplies
another independent noise bit `N`, also with probability `1/4`.  The equations
are `X = U`, `M = X xor N`, and `Y = U xor E`.  The last equation deliberately
does not use the allowed parent `M`: compatibility imposes permitted inputs
and the latent projection, not faithfulness or dependence on every parent.
Every observed assignment nevertheless has strictly positive probability.

The final theorem makes the consequence for completeness explicit: a
`PublishedJointTraceCompiler` aligned with *every* current successful engine
formula cannot exist.  Published soundness would turn such a certificate
into the false equality `1/2 = 9/16`.  This does not refute mathematical
identification completeness; it requires repairing the executable recursion
before demanding certificates for its displayed outputs.  The replacement
`identifyJointKernel` is checked below against this same positive model and
does recover the correct value.  The negative assertions remain specific
to the legacy engine and its formula-aligned compiler; they must not be
transferred to the replacement recursion or mistaken for a refutation of
mathematical completeness.
-/

/-! ## The front-door graph and a strictly positive compatible model -/

/-- The topological order is `X`, `M`, `Y`; the allowed directed arrows are
exactly `X → M` and `M → Y`. -/
def signature : ObservedSignature where
  count := 3
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (child.val = parent.val + 1)
  directed_earlier := by
    intro parent child edge
    have next : child.val = parent.val + 1 := of_decide_eq_true edge
    omega

def x : Fin signature.count := ⟨0, by decide⟩
def mediator : Fin signature.count := ⟨1, by decide⟩
def y : Fin signature.count := ⟨2, by decide⟩

/-- Root zero is shared by `X` and `Y`; root one is private to `M`.
Each root takes eight values so the biased noise bits can be implemented
deterministically from a uniform finite prior. -/
def latent : LatentExtension signature where
  count := 2
  Value := fun _ => Fin 8
  valueEnumeration := fun _ => List.finRange 8
  value_complete := fun _ value => List.mem_finRange value
  valueDecidableEq := fun _ => inferInstance
  incident := fun root child =>
    if root.val = 0 then decide (child.val = 0) || decide (child.val = 2)
    else decide (child.val = 1)

/-- Eight equally weighted latent values.  The threshold bit and the
remainder-zero bit are independent, with probabilities `1/2` and `1/4`. -/
def uniform8 : FiniteProbRecord (Fin 8) where
  atoms := [(⟨0, by decide⟩, 1), (⟨1, by decide⟩, 1),
    (⟨2, by decide⟩, 1), (⟨3, by decide⟩, 1),
    (⟨4, by decide⟩, 1), (⟨5, by decide⟩, 1),
    (⟨6, by decide⟩, 1), (⟨7, by decide⟩, 1)]
  den := 8
  den_pos := by decide
  total_mass := rfl

/-- The two independent root records and the three equations described
above.  The product law is the generic constructive product-record theorem,
not a numerically assumed independence equation. -/
def model : ExactModel signature where
  latent := latent
  factor := fun _ => uniform8
  prior := FiniteProduct.record 2 (fun _ => Fin 8) (fun _ => uniform8)
  product_law := fun events =>
    FiniteProduct.record_rectangular_probVal 2 (fun _ => Fin 8)
      (fun _ => uniform8) events
  mechanism := fun child parents inputs =>
    if atX : child.val = 0 then
      decide ((inputs ⟨0, by decide⟩ (by simp [latent, atX])).val ≥ 4)
    else if atMediator : child.val = 1 then
      Bool.xor
        (parents x (by simp [signature, x, atMediator]))
        (decide ((inputs ⟨1, by decide⟩
          (by simp [latent, atMediator])).val % 4 = 0))
    else
      have atY : child.val = 2 := by
        have bound := child.isLt
        change child.val < 3 at bound
        omega
      let shared := inputs ⟨0, by decide⟩ (by simp [latent, atY])
      Bool.xor (decide (shared.val ≥ 4)) (decide (shared.val % 4 = 0))

/-- The projection contains exactly the confounding edge `X ↔ Y`;
the signature supplies the directed arrows independently. -/
def graph : ObservedGraph signature := model.observedGraph

/-- The model's latent projection is the advertised front-door graph,
including the absence of confounding edges incident to the mediator. -/
theorem graph_bidirected_endpoints :
    graph.bidirected x y = true ∧
      graph.bidirected x mediator = false ∧
      graph.bidirected mediator y = false := by decide +kernel

/-- The joint query whose current engine output fails the semantic check. -/
def query : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  action_outcome_disjoint := by
    intro node selected
    have equal := (NodeSet.singleton_eq_true_iff x node).mp selected
    subst node
    rfl

/-- Extract the actual displayed engine formula, with a harmless fallback
only to make this definition total.  `legacyEngine_identified` proves that the
fallback is not used; a failed or unfinished run cannot fake the regression. -/
def legacyEngineFormula : ProbabilityTerm signature :=
  match identifyJoint graph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

def reference : signature.Assignment := fun _ => true

/-! ## Exact checked values and regularity witnesses -/

/-- A finite rational-value test uses cross multiplication, so it accepts
the engine's unreduced numerator and denominator without normalizing them. -/
private def valueTest (result : ProbabilityResult.Result) (expected : QProb) : Bool :=
  match result with
  | none => false
  | some value => decide (QProb.Equiv value expected)

/-- Turn a successful Boolean test into typed partial-result equivalence by
inspecting the result.  No representative is selected from a proposition. -/
private def equivalentOfValueTest (result : ProbabilityResult.Result) (expected : QProb)
    (checked : valueTest result expected = true) :
    ProbabilityResult.Equivalent result (some expected) := by
  cases result with
  | none => cases checked
  | some value => exact .value (of_decide_eq_true checked)

set_option maxRecDepth 100000 in
/-- The current executable run genuinely takes the identified branch. -/
theorem legacyEngine_identified :
    identifyJoint graph query = .identified legacyEngineFormula := by rfl

set_option maxRecDepth 100000 in
/-- Intervening on `X` does not change `Y = U xor E`, so the requested
probability remains `1/2`.  The kernel checks the concrete finite semantics. -/
def sourceAtReferenceHalf :
    ProbabilityResult.Equivalent (query.sourceTerm.denote model reference)
      (some ⟨1, 2, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The displayed engine expression evaluates instead to `9/16`.
`decide +kernel` checks ordinary finite reduction; it does not use
`native_decide` or introduce a reduction axiom. -/
def legacyEngineAtReferenceNineSixteenths :
    ProbabilityResult.Equivalent (legacyEngineFormula.denote model reference)
      (some ⟨9, 16, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

/-- Neither root has more than two observed children, and the chosen graph
is exactly its projected graph.  This is the published model-class premise. -/
theorem model_compatible : Compatible model graph := by
  constructor
  · change latent.CanonicalSemiMarkovian
    unfold LatentExtension.CanonicalSemiMarkovian latent
    decide +kernel
  · intro i j
    rfl

/-- A displayed three-bit observed assignment, used to exhaust the eight
positivity cases without any excluded-middle argument over propositions. -/
def assignmentOf (a b c : Bool) : signature.Assignment :=
  fun node => if node.val = 0 then a else if node.val = 1 then b else c

/-- Every dependent observed assignment is determined by these three bits. -/
theorem assignment_eq (assignment : signature.Assignment) :
    assignment = assignmentOf (assignment x) (assignment mediator)
      (assignment y) := by
  funext node
  match node with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨n + 3, bound⟩ =>
      change n + 3 < 3 at bound
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- All eight complete observed assignments have positive mass, so this is
a counterexample inside `GraphModelClass.positive`, not just among models
with zero-probability observational conditionals. -/
theorem model_positive : ObservationallyPositive model := by
  intro assignment
  rw [assignment_eq assignment]
  cases assignment x <;> cases assignment mediator <;> cases assignment y <;>
    decide +kernel

/-! ## The actual obstruction to a formula-aligned success compiler -/

/-- The source kernel and displayed engine formula disagree at a supported
assignment.  Positivity and compatibility above exclude regularity or graph
mismatch as explanations for the difference. -/
theorem legacyEngineFormula_not_equivalent :
    ¬ Nonempty (ProbabilityTerm.EquivalentAt model query.sourceTerm
      legacyEngineFormula reference) := by
  intro ⟨equivalent⟩
  let forced := ProbabilityResult.trans (ProbabilityResult.symm sourceAtReferenceHalf)
    (ProbabilityResult.trans equivalent legacyEngineAtReferenceNineSixteenths)
  cases forced with
  | value impossible =>
      exact (by decide : ¬ QProb.Equiv ⟨1, 2, by decide⟩ ⟨9, 16, by decide⟩)
        impossible

/-- The existing exact-output compiler interface is uninhabitable for this
graph.  A compiler would have to certify the identified trace; completed
published soundness then contradicts the two exact value checks above.
This theorem pinpoints an engine-repair obligation, not a missing axiom. -/
theorem legacyTraceCompiler_is_uninhabited :
    ¬ Nonempty (PublishedJointTraceCompiler graph (GraphModelClass.positive graph)
      graph.dSeparationCorrectness) := by
  intro ⟨compiler⟩
  cases identifyJoint_terminalTrace graph query with
  | identified term trace =>
      let compiled := compiler.compile query term trace
      have identified : identifyJoint graph query = .identified term := by
        exact trace.eq_identified
      have termEqual : term = legacyEngineFormula := by
        have resultsEqual := identified.symm.trans legacyEngine_identified
        injection resultsEqual
      have formulaEqual : compiled.certificate.formula = legacyEngineFormula :=
        compiled.formula_eq.trans termEqual
      let supported : query.sourceTerm.SupportedAt model reference :=
        ⟨⟨1, 2, by decide⟩, sourceAtReferenceHalf⟩
      let sound := compiled.certificate.compile.denotational_soundAt
        graph.publishedSoundness model ⟨model_compatible, model_positive⟩
        reference supported
      exact legacyEngineFormula_not_equivalent ⟨formulaEqual ▸ sound⟩
  | failed fail trace =>
      have failed : identifyJoint graph query = .failed fail := trace.eq_failed
      rw [legacyEngine_identified] at failed
      cases failed

/-! ## Positive correctness regression for the current-kernel replacement -/

/-- Extract the replacement engine's actual returned expression.  The
following branch equation checks that the fallback is not used. -/
def kernelEngineFormula : ProbabilityTerm signature :=
  match identifyJointKernel graph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

set_option maxRecDepth 100000 in
/-- The replacement handles the full front-door query, not a manually
supplied adjustment expression or a special-case model branch. -/
theorem kernelEngine_identified :
    identifyJointKernel graph query = .identified kernelEngineFormula := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Prefix quotients of the actual current kernel yield the correct `1/2`,
in contrast to the legacy output `9/16`.  Ordinary kernel reduction checks
the entire generated expression, including its nested sums and divisions. -/
def kernelEngineAtReferenceHalf :
    ProbabilityResult.Equivalent (kernelEngineFormula.denote model reference)
      (some ⟨1, 2, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

/-- The replacement formula and the requested interventional source agree
at the regression assignment.  This is a checked instance, not the general
semantic soundness or completeness theorem for all ID runs. -/
def kernelEngine_equivalent_source :
    ProbabilityTerm.EquivalentAt model query.sourceTerm kernelEngineFormula
      reference :=
  ProbabilityResult.trans sourceAtReferenceHalf
    (ProbabilityResult.symm kernelEngineAtReferenceHalf)

/-! ## A regression that actually exercises action augmentation -/

/-- Intervene on the mediator rather than on `X`.  All three vertices are
ordinary ancestors of `Y`, but cutting incoming arrows at `M` removes `X`
from that ancestor set.  The additional-action branch must therefore run. -/
def mediatorQuery : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton mediator
  action_outcome_disjoint := by
    intro node selected
    have equal := (NodeSet.singleton_eq_true_iff mediator node).mp selected
    subst node
    rfl

set_option maxRecDepth 100000 in
/-- The incoming-cut test adds exactly `X`, rather than shrinking the
current distribution by observationally marginalizing it away. -/
theorem mediatorAdditionalAction_members :
    NodeSet.members (identificationAdditionalAction graph NodeSet.full
      mediatorQuery.outcome mediatorQuery.action) = [x] := by rfl

/-- The actual replacement output for the mediator intervention.  This
case uses augmentation followed by the ordinary recursive ID branches. -/
def kernelMediatorFormula : ProbabilityTerm signature :=
  match identifyJointKernel graph mediatorQuery with
  | .identified term => term
  | _ => unitProbabilityTerm signature

set_option maxRecDepth 100000 in
/-- The query is identified by the generic engine with its public bound. -/
theorem kernelMediator_identified :
    identifyJointKernel graph mediatorQuery = .identified kernelMediatorFormula := by rfl

set_option maxRecDepth 100000 in
/-- The mediator is an unused allowed parent of `Y` in this compatible
model, so intervening on it also leaves the outcome probability at `1/2`. -/
def mediatorSourceAtReferenceHalf :
    ProbabilityResult.Equivalent (mediatorQuery.sourceTerm.denote model reference)
      (some ⟨1, 2, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The complete generated expression after action augmentation agrees
with the source value; the test checks all subsequent restrictions and
current-input quotients as well, not just the Boolean `W` selection. -/
def kernelMediatorAtReferenceHalf :
    ProbabilityResult.Equivalent (kernelMediatorFormula.denote model reference)
      (some ⟨1, 2, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

/-- Checked source/output agreement for the nonempty-`W` regression. -/
def kernelMediator_equivalent_source :
    ProbabilityTerm.EquivalentAt model mediatorQuery.sourceTerm kernelMediatorFormula
      reference :=
  ProbabilityResult.trans mediatorSourceAtReferenceHalf
    (ProbabilityResult.symm kernelMediatorAtReferenceHalf)

end FrontDoorIdentification
end Examples
end Causality
end Thesis
