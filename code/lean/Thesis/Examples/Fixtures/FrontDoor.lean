import Thesis.Causality.Identification

namespace Thesis
namespace Causality
namespace Examples
namespace FrontDoorIdentification

open Probability

/-!
# Shared positive front-door fixture

The graph is `X → M → Y` with the single confounding edge `X ↔ Y`.
The two independent finite roots encode an unbiased shared bit and two
independent quarter-probability noise bits. The allowed mediator parent of
`Y` is deliberately unused; compatibility does not assume faithfulness.

This module owns the concrete signature, model, query and checked positive
source value. It imports no identification program, legacy recursion or
soundness proof. Modern compiler examples can therefore reuse the same
mathematical fixture without importing a negative algorithm regression.
The small rational-value checker is shared by the two front-door tests;
its proof inspects actual option values and makes no classical selection.
-/

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

/-- The front-door query shared by the current and negative regressions. -/
def query : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  action_outcome_disjoint := by
    intro node selected
    have equal := (NodeSet.singleton_eq_true_iff x node).mp selected
    subst node
    rfl

def reference : signature.Assignment := fun _ => true

/-! ## Exact checked values and regularity witnesses -/

/-- A finite rational-value test uses cross multiplication, so it accepts
the engine's unreduced numerator and denominator without normalizing them. -/
def valueTest (result : ProbabilityResult.Result) (expected : QProb) : Bool :=
  match result with
  | none => false
  | some value => decide (QProb.Equiv value expected)

/-- Turn a successful Boolean test into typed partial-result equivalence by
inspecting the result.  No representative is selected from a proposition. -/
def equivalentOfValueTest (result : ProbabilityResult.Result) (expected : QProb)
    (checked : valueTest result expected = true) :
    ProbabilityResult.Equivalent result (some expected) := by
  cases result with
  | none => cases checked
  | some value => exact .value (of_decide_eq_true checked)

set_option maxRecDepth 100000 in
/-- Intervening on `X` does not change `Y = U xor E`, so the requested
probability remains `1/2`.  The kernel checks the concrete finite semantics. -/
def sourceAtReferenceHalf :
    ProbabilityResult.Equivalent (query.sourceTerm.denote model reference)
      (some ⟨1, 2, by decide⟩) :=
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


end FrontDoorIdentification
end Examples
end Causality
end Thesis
