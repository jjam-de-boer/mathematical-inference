import Thesis.CausalTransport.HedgeChannelEnvironmentAbsorption
import Thesis.CausalTransport.ConditionalFailureFlowBoundary

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelEnvironmentAbsorption

open PathSpecification HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# A genuine conditioned collider with extra mandatory rows and a merge

The eight three-valued vertices are `X,Y,S,T,M,C,Z,P`.  The unchanged query
is `P(Y | do(X), P,Z)`.  Its hedge has Small `S,T,C,Z,P`, roots `Z,P`, and
Large obtained by adding `X`.  Genuine bidirected pairs connect `X,S,T,C`
to `P`, and `C` to `Z`; no global shared switch is introduced.

The active path `P <- U_{C,P} -> C <- Y` uses conditioned descendant `Z`
to activate collider `C`.  The original Small-flow paths all meet evidence.
Thus this is the conditioned branch, not another unconditioned queried-Small
source.  The selected interaction rows are `C,Z,P`, already inside Small.

Extra mandatory rows `S,T` feed the outside-Small merge row `M`, which feeds
the existing Small interaction row `C`.  This auxiliary routing uses actual
arrows `S,T -> M -> C` and stops at `C`.  Its complete domain is `S,T,M,C`;
the mandatory-row union is `S,T,M,C,Z,P`.  The semantic companion applies the
general absorption theorem rather than adding a second copy of row `C`.

Only finite graph certificates are checked here.  The companion verifies the
complete installed parity and builds positive original-label countermodels
without evaluating an exhaustive path-normalization search or model prior.
-/

def signature : ObservedSignature where
  count := 8
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 7) ∨ (parent.val = 1 ∧ child.val = 5) ∨
      ((parent.val = 2 ∨ parent.val = 3) ∧ (child.val = 4 ∨ child.val = 6)) ∨
      (parent.val = 4 ∧ child.val = 5) ∨ (parent.val = 5 ∧ child.val = 6))
  directed_earlier := by intro parent child edge; have endpoints := of_decide_eq_true edge; omega

def actionNode : Fin signature.count := ⟨0, by decide⟩
def outcomeNode : Fin signature.count := ⟨1, by decide⟩
def firstSource : Fin signature.count := ⟨2, by decide⟩
def secondSource : Fin signature.count := ⟨3, by decide⟩
def mergeNode : Fin signature.count := ⟨4, by decide⟩
def collider : Fin signature.count := ⟨5, by decide⟩
def evidence : Fin signature.count := ⟨6, by decide⟩
def pivotNode : Fin signature.count := ⟨7, by decide⟩

private def pairMask (left right : Fin signature.count) : Bool := decide
  (((left.val = 0 ∨ left.val = 2 ∨ left.val = 3 ∨ left.val = 5) ∧ right.val = 7) ∨
    (left.val = 5 ∧ right.val = 6))

def graph : ObservedGraph signature where
  bidirected := fun left right => pairMask left right || pairMask right left
  bidirected_symmetric := by intro _ _ selected; simpa only [Bool.or_comm] using selected
  bidirected_irreflexive := by
    intro node
    have absent : pairMask node node = false := by unfold pairMask; apply decide_eq_false; omega
    simp only [absent, Bool.false_or]

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.union (NodeSet.singleton evidence) (NodeSet.singleton pivotNode)
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def small : NodeSet signature := fun node => decide (node.val = 2 ∨ node.val = 3 ∨ 5 ≤ node.val)
def large : NodeSet signature := NodeSet.union small (NodeSet.singleton actionNode)
def child : ForestChild signature := fun node => if node = actionNode then some pivotNode else
  if node = firstSource ∨ node = secondSource ∨ node = collider then some evidence else none
def selection : HedgeSelection signature := ⟨large, small, child⟩

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

/-- The preceding exhaustive source theorem really places this fixture on
its conditioned side; none of the extra Small sources gives a free path. -/
def boundary : ConditionedSmallFlowBoundary witness where
  encounters_condition := by decide +kernel

def cut : GraphMutilation signature := .barUnderline query.action (NodeSet.singleton pivotNode)
def given : NodeSet signature := NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton pivotNode))
def shared : SeparationNode signature := .latentPair collider pivotNode

/-- An actual original-pair collider path, activated by the original
conditioned descendant.  No claimed disjointness or new latent input is used. -/
def actualPath : ActivePath graph cut given (.observed pivotNode) (.observed outcomeNode) where
  nodes := [.observed pivotNode, shared, .observed collider, .observed outcomeNode]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, True.intro⟩ <;> decide +kernel
  source_open := by decide +kernel
  target_open := by decide +kernel
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), by unfold NonColliderOpen; decide +kernel⟩)
    (.step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩,
      graph.ancestorOf_prepend cut given (middle := .observed evidence) (by decide +kernel)
        (graph.ancestorOf_target cut given (target := evidence) (by decide +kernel))⟩)
      (.pair (.observed collider) (.observed outcomeNode)))

/-! ## Certified absorbing forest at an already selected Small collider -/

def interaction : NodeSet signature := fun node => decide (5 ≤ node.val)
def absorbingDomain : NodeSet signature := fun node => decide (2 ≤ node.val ∧ node.val ≤ 5)
def absorbingSuccessor : ForestChild signature := fun parent =>
  if parent = firstSource ∨ parent = secondSource then some mergeNode else
    if parent = mergeNode then some collider else none

theorem absorbing_wellFormed : childWellFormedBool absorbingDomain absorbingSuccessor = true := by decide +kernel
theorem absorbing_stops : forall node, interaction node = true -> absorbingSuccessor node = none := by decide +kernel
theorem absorbing_sinks_inside : NodeSet.Subset (keptSinks absorbingDomain absorbingSuccessor) interaction := by
  unfold NodeSet.Subset; decide +kernel
theorem absorbing_contains_small : NodeSet.Subset witness.small (NodeSet.union interaction absorbingDomain) := by
  unfold NodeSet.Subset; decide +kernel
theorem absorbing_action_free : forall node, NodeSet.union interaction absorbingDomain node = true -> query.action node = false := by
  decide +kernel

/-- Both distinct mandatory sources merge at one genuine background row,
then feed an interaction row already in Small.  The outside-Small background
is precisely `M`, not a duplicate copy of the receiving collider `C`. -/
theorem actual_merge_and_small_overlap :
    absorbingSuccessor firstSource = some mergeNode ∧ absorbingSuccessor secondSource = some mergeNode ∧
    absorbingSuccessor mergeNode = some collider ∧ interaction collider = true ∧ witness.small collider = true ∧
    NodeSet.diff (NodeSet.union interaction absorbingDomain) witness.small = NodeSet.singleton mergeNode := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  funext node
  decide +kernel +revert

end CurrentHedgeChannelEnvironmentAbsorption
end Examples
end Causality
end Thesis
