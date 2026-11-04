import Thesis.Causality.ModeIndexedIdentification
import Thesis.Causality.BinaryBowModel
import Thesis.Causality.ProbabilityTermEquality

namespace Thesis
namespace Causality
namespace Examples
namespace ModeIndexedIdentification

open Probability FiniteProduct
open BinaryBow
open ModeQueryPolicy
open ModeIndexedAnswer

/-!
Same unconfounded `X → Y` graph, two modes, one query `P(Y | do(X))`.

Mode A may intervene on `X` and obtains an identified rational. Mode B may
not (only `Y`, or only observation): the query is `modeUnsupported`. Changing
B's belief does not identify it. Compact workspace `do(X)` is not an implicit
licence to ask `do(X)` without an explicit policy.
-/

def fairBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

def biasedBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 3)]
  den := 4
  den_pos := by decide
  total_mass := rfl

/-- Private noise into `X` only; `Y` copies `X`. No bidirected edge. -/
def chainLatent : LatentExtension signature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun _ child => decide (child.val = 0)

def chainModel : ExactModel signature where
  latent := chainLatent
  factor := fun _ => fairBit
  prior := record 1 (fun _ => Bool) (fun _ => fairBit)
  product_law := record_rectangular_probVal 1 (fun _ => Bool) (fun _ => fairBit)
  mechanism := fun child parents inputs =>
    if hx : child = x then
      inputs ⟨0, by decide⟩ (by simp [chainLatent, hx, x])
    else
      parents x (by
        rcases node_cases child with same | same
        · exact (hx same).elim
        · simp [signature, x, y, same])

def modeA : ExtensionalMode signature where
  model := chainModel
  belief := chainModel.prior

def modeB : ExtensionalMode signature where
  model := chainModel
  belief := record 1 (fun _ => Bool) (fun _ => biasedBit)

def policyA : ModeQueryPolicy signature where
  mode := modeA
  intervenable := NodeSet.singleton x

def policyB : ModeQueryPolicy signature where
  mode := modeB
  intervenable := NodeSet.singleton y

def policyBSameBelief : ModeQueryPolicy signature where
  mode := modeA
  intervenable := NodeSet.singleton y

def xy (xv yv : Bool) : signature.Assignment :=
  fun i => if i.val = 0 then xv else yv

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  action_outcome_disjoint := by
    intro i hx
    have : i = x := (NodeSet.singleton_eq_true_iff x i).mp hx
    subst this
    simp [NodeSet.singleton, x, y]

def obsQuery : JointKernelQuery signature where
  outcome := NodeSet.singleton y
  action := NodeSet.empty
  action_outcome_disjoint := NodeSet.disjoint_empty_left _

def reference : signature.Assignment :=
  xy true true

theorem same_graph : policyA.graph = policyB.graph :=
  rfl

theorem embed_empty_with_open_X :
    ExtensionalMode.noActive (ExtensionalMode.embed policyA.mode).record ∧
      policyA.allowedB ((HardIntervention.empty signature).set x true) = true :=
  policyA.embed_empty_do_of_nonempty_allowed x (by decide) true

theorem policyA_admissible : policyA.jointAdmissible query = true := by
  decide

theorem policyB_denied : policyB.jointAdmissible query = false := by
  decide

theorem policyBSameBelief_denied :
    policyBSameBelief.jointAdmissible query = false := by
  decide

theorem policyB_obs_admissible : policyB.jointAdmissible obsQuery = true :=
  policyB.empty_action_jointAdmissible obsQuery (by decide)

theorem policyB_modeUnsupported :
    policyB.identifyJoint query reference none none = .modeUnsupported :=
  policyB.identifyJoint_modeUnsupported query reference none none
    policyB_denied

theorem policyBSameBelief_modeUnsupported :
    policyBSameBelief.identifyJoint query reference none none =
      .modeUnsupported :=
  policyBSameBelief.identifyJoint_modeUnsupported query reference none none
    policyBSameBelief_denied

set_option maxRecDepth 100000

def chainFormula : ProbabilityTerm signature :=
  match identifyJointKernel policyA.graph query with
  | .identified term => term
  | _ => .zero

theorem chain_identified :
    identifyJointKernel policyA.graph query = .identified chainFormula := by
  rfl

theorem policyA_identified :
    policyA.identifyJoint query reference none none =
      .identified chainFormula
        (policyA.interpretIdentified chainFormula reference) :=
  policyA.identifyJoint_identified_of_kernel query reference none
    policyA_admissible chain_identified

theorem assignment_eq (a : signature.Assignment) : a = xy (a x) (a y) := by
  funext i
  rcases node_cases i with h | h <;> subst i <;> simp [xy, x, y]

/-- Copy-chain observational table: `Y = X`, fair exogenous `X`. -/
def observedTable : FiniteProbRecord signature.Assignment where
  atoms := [(xy false false, 1), (xy true true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

set_option maxHeartbeats 1000000 in
theorem observedTable_agrees (event : Event signature.Assignment) :
    QProb.Equiv (policyA.observationalLaw.probVal event)
      (observedTable.probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _
    signature.assignmentEnumeration signature.assignmentEnumeration_nodup
    signature.assignmentEnumeration_complete ?_ event
  intro assignment
  rw [assignment_eq assignment]
  cases assignment x <;> cases assignment y <;> decide +kernel

/-- Engine output on this unconfounded query: empty-outer `P(V) / P(X)`. -/
def compactFormula : ProbabilityTerm signature :=
  let joint : ProbabilityTerm signature :=
    .kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩
  .marginalize NodeSet.empty
    (.divide
      (.marginalize NodeSet.empty joint)
      (.marginalize (NodeSet.singleton y) joint))

set_option maxHeartbeats 1000000 in
theorem chainFormula_eq_compact : chainFormula = compactFormula :=
  (ProbabilityTerm.equal_eq_true_iff _ _).mp (by decide +kernel)

def valueTest (result : ProbabilityResult.Result) (expected : QProb) : Bool :=
  match result with
  | none => false
  | some value => decide (QProb.Equiv value expected)

def equivalentOfValueTest (result : ProbabilityResult.Result) (expected : QProb)
    (checked : valueTest result expected = true) :
    ProbabilityResult.Equivalent result (some expected) := by
  cases result with
  | none => cases checked
  | some value => exact .value (of_decide_eq_true checked)

def one : QProb := ⟨1, 1, Nat.succ_pos 0⟩

set_option maxHeartbeats 1000000 in
theorem compact_value : valueTest
    (compactFormula.observationalDenote observedTable reference) one = true := by
  decide +kernel

/-- Mode A identifies `P(Y | do(X))` at the reference to the rational `1`. -/
noncomputable def policyA_identified_value :
    ProbabilityResult.Equivalent
      (policyA.interpretIdentified chainFormula reference) (some one) := by
  rw [chainFormula_eq_compact]
  exact ProbabilityResult.trans
    (ProbabilityTerm.observationalDenote_congr policyA.observationalLaw
      observedTable observedTable_agrees compactFormula reference)
    (equivalentOfValueTest _ _ compact_value)

def policyBOpened : ModeQueryPolicy signature :=
  policyB.widen (NodeSet.singleton x)

theorem widen_graph_unchanged : policyBOpened.graph = policyB.graph :=
  rfl

theorem policyBOpened_admissible :
    policyBOpened.jointAdmissible query = true := by
  decide

theorem policyBOpened_identified :
    (policyBOpened.identifyJoint query reference none none).isIdentified =
      true := by
  have kernel :
      identifyJointKernel policyBOpened.graph query = .identified chainFormula :=
    chain_identified
  rw [policyBOpened.identifyJoint_identified_of_kernel query reference none
        policyBOpened_admissible kernel]
  rfl

def lockedState : ModeTheory.CurrentState signature where
  model := chainModel
  belief := chainModel.prior
  intervention := (HardIntervention.empty signature).set x true

def lockedPolicy : WorkspaceQueryPolicy signature where
  state := lockedState
  intervenable := NodeSet.singleton y

theorem locked_compact_do_is_X :
    lockedState.intervention.targets x = true := by
  simp [lockedState, HardIntervention.set, HardIntervention.targets,
    HardIntervention.empty, FiniteLatentSCM.noIntervention, x]

theorem locked_does_not_allow_current_do :
    lockedPolicy.allowedB lockedState.intervention = false := by
  decide

theorem locked_query_modeUnsupported :
    lockedPolicy.identifyJoint query reference none none = .modeUnsupported :=
  lockedPolicy.toQueryPolicy.identifyJoint_modeUnsupported query reference
    none none (by decide)

theorem locked_embed_still_empty :
    (ExtensionalMode.embed lockedPolicy.toQueryPolicy.mode).record.intervention =
      HardIntervention.empty signature :=
  WorkspaceQueryPolicy.toQueryPolicy_ignores_lock lockedPolicy

end ModeIndexedIdentification
end Examples
end Causality
end Thesis
