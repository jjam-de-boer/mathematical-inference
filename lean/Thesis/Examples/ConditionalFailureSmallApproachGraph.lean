import Thesis.CausalTransport.ConditionalFailureSmallApproach

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureSmallApproach

open PathSpecification

/-!
# A genuine Small approach whose first conditioner is not latest

The five original three-valued vertices are `X,Y,U,P,Z`.  Declared arrows
are `X,Y,U -> P -> Z`; actual bidirected pairs are `X <-> P`, `U <-> P`
and `P <-> Z`.  The hedge uses Large `X,U,P`, Small `U,P`, and root `P`,
with legal selected child arrows `X,U -> P`.  A forest need not keep the
extra declared arrow `P -> Z` once its root is already queried.

For `P(Y | do(X), P,Z)`, every stopped Small-source path encounters evidence.
The unconditioned Small source `U` reaches its first conditioner `P`, while
the original incoming cut also reaches the later conditioner `Z`.  Preserving
the actual stopped path gives an unconditioned proper prefix; replacing its
endpoint by the latest reachable conditioner would pass through conditioned
`P`.  A second original query additionally conditions `U`, so every Small
row is conditioned and the new semantic branch can close it outright.

Both queries really exhaust singleton exchanges.  Displayed active paths
prove the negative tests without reducing the entire expanded moral closure.
This module provides only the graph, query and hedge certificates; its
companion applies the general approach and countermodel constructions.
-/

def signature : ObservedSignature where
  count := 5
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val < 3 ∧ child.val = 3) ∨ (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def actionNode : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩
def source : Fin signature.count := ⟨2, by decide⟩
def firstConditioner : Fin signature.count := ⟨3, by decide⟩
def laterConditioner : Fin signature.count := ⟨4, by decide⟩

private def pairMask (left right : Fin signature.count) : Bool :=
  decide ((left.val = 0 ∧ right.val = 3) ∨ (left.val = 2 ∧ right.val = 3) ∨ (left.val = 3 ∧ right.val = 4))

def graph : ObservedGraph signature where
  bidirected := fun left right => pairMask left right || pairMask right left
  bidirected_symmetric := by intro _ _ selected; simpa only [Bool.or_comm] using selected
  bidirected_irreflexive := by
    intro node
    have absent : pairMask node node = false := by unfold pairMask; apply decide_eq_false; omega
    simp only [absent, Bool.false_or]

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if same : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp same)
  else isFalse (fun equal => same ((SeparationNode.beq_eq_true_iff left right).mpr equal))

/-- Two separately interpreted original queries on one unchanged alphabet.
The Boolean parameter adds `U` to the second query's evidence; it is not a
query-changing step inside either countermodel construction. -/
def query (conditionSource : Bool) : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.singleton actionNode
  condition := fun node => NodeSet.singleton firstConditioner node || NodeSet.singleton laterConditioner node ||
    (conditionSource && NodeSet.singleton source node)
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := by cases conditionSource <;> unfold NodeSet.Disjoint <;> decide +kernel
  outcome_condition_disjoint := by cases conditionSource <;> unfold NodeSet.Disjoint <;> decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def selection : HedgeSelection signature where
  large := fun node => decide (node.val = 0 ∨ node.val = 2 ∨ node.val = 3)
  small := fun node => decide (node.val = 2 ∨ node.val = 3)
  child := fun node => if node.val = 0 ∨ node.val = 2 then some firstConditioner else none

theorem hedge_tests (conditionSource : Bool) : hedgeTestsHold graph (query conditionSource).jointNumerator selection = true := by
  cases conditionSource <;> decide +kernel

def witness (conditionSource : Bool) : HedgeWitness graph (query conditionSource).jointNumerator :=
  hedgeWitness_of_sets graph (query conditionSource).jointNumerator selection (hedge_tests conditionSource)

private def cut (conditionSource : Bool) (pivot : Fin signature.count) : GraphMutilation signature :=
  .barUnderline (query conditionSource).action (NodeSet.singleton pivot)

private def given (conditionSource : Bool) (pivot : Fin signature.count) : NodeSet signature :=
  NodeSet.union (query conditionSource).action (NodeSet.diff (query conditionSource).condition (NodeSet.singleton pivot))

/-- The first conditioner has the real incoming edge `Y -> P`; other
original evidence cannot block this two-vertex path in its singleton cut. -/
private def firstPath (conditionSource : Bool) :
    ActivePath graph (cut conditionSource firstConditioner) (given conditionSource firstConditioner)
      (.observed firstConditioner) (.observed outcome) where
  nodes := [.observed firstConditioner, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := ⟨Or.inr (by cases conditionSource <;> decide +kernel), True.intro⟩
  source_open := by cases conditionSource <;> decide +kernel
  target_open := by cases conditionSource <;> decide +kernel
  internal_active := .pair _ _

/-- The later conditioner uses its actual private `P,Z` root.  Conditioned
`P` is an activated collider on `Z <- L(P,Z) -> P <- Y`. -/
private def laterPath (conditionSource : Bool) :
    ActivePath graph (cut conditionSource laterConditioner) (given conditionSource laterConditioner)
      (.observed laterConditioner) (.observed outcome) where
  nodes := [.observed laterConditioner, .latentPair firstConditioner laterConditioner, .observed firstConditioner, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, True.intro⟩ <;> cases conditionSource <;> decide +kernel
  source_open := by cases conditionSource <;> decide +kernel
  target_open := by cases conditionSource <;> decide +kernel
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing _ (by cases conditionSource <;> decide +kernel),
      by cases conditionSource <;> unfold NonColliderOpen <;> decide +kernel⟩)
    (.step (Or.inl ⟨⟨by cases conditionSource <;> decide +kernel, by cases conditionSource <;> decide +kernel⟩,
      graph.ancestorOf_target _ _ (target := firstConditioner) (by cases conditionSource <;> decide +kernel)⟩)
      (.pair _ _))

/-- If `U` is also conditioned, its original `U,P` root supplies the same
activated collider at `P`; the removed outgoing `U -> P` is not used. -/
private def sourcePath : ActivePath graph (cut true source) (given true source) (.observed source) (.observed outcome) where
  nodes := [.observed source, .latentPair source firstConditioner, .observed firstConditioner, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, True.intro⟩ <;> decide +kernel
  source_open := by decide +kernel
  target_open := by decide +kernel
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing _ (by decide +kernel), by unfold NonColliderOpen; decide +kernel⟩)
    (.step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩,
      graph.ancestorOf_target _ _ (target := firstConditioner) (by decide +kernel)⟩)
      (.pair _ _))

private theorem test_false_of_path (conditionSource : Bool) (pivot : Fin signature.count)
    (path : ActivePath graph (cut conditionSource pivot) (given conditionSource pivot) (.observed pivot) (.observed outcome)) :
    conditionalExchangeTest graph (query conditionSource) pivot = false := by
  cases answer : conditionalExchangeTest graph (query conditionSource) pivot with
  | false => rfl
  | true =>
      exact False.elim ((graph.dSeparated_implies_pathDSeparated _ (query conditionSource).outcome
        (NodeSet.singleton pivot) _ answer)
        ⟨outcome, pivot, by cases conditionSource <;> decide +kernel,
          (NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl, ⟨path.reverse⟩⟩)

/-- Both original queries truly exhaust all singleton exchanges.  Finite
mask membership chooses which displayed path refutes the supplied test;
only its negative answer is proved, not full moral-closure evaluation. -/
theorem no_exchange (conditionSource : Bool) : conditionalExchangeStep? graph (query conditionSource) = none := by
  have excluded : forall node, (query conditionSource).condition node = true ->
      conditionalExchangeTest graph (query conditionSource) node = false := by
    intro node selected
    have alternatives : node = firstConditioner ∨ node = laterConditioner ∨ (conditionSource = true ∧ node = source) :=
      (by cases conditionSource <;> decide +kernel : forall node, (query conditionSource).condition node = true ->
        node = firstConditioner ∨ node = laterConditioner ∨ (conditionSource = true ∧ node = source)) node selected
    rcases alternatives with first | later | ⟨full, sourceEq⟩
    · subst node; exact test_false_of_path conditionSource firstConditioner (firstPath conditionSource)
    · subst node; exact test_false_of_path conditionSource laterConditioner (laterPath conditionSource)
    · subst conditionSource; subst node; exact test_false_of_path true source sourcePath
  cases result : conditionalExchangeStep? graph (query conditionSource) with
  | none => rfl
  | some step => exact False.elim (Bool.false_ne_true ((excluded step.node step.selected).symm.trans step.separated))

end CurrentConditionalFailureSmallApproach
end Examples
end Causality
end Thesis
