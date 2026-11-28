import Thesis.Causality.HardIntervention
import Thesis.Probability.Distros.EntropySupport
import Thesis.Probability.Distros.RationalConcentration
import Thesis.Probability.FiniteFunctionTables

/-!
# Replacement behind a finite feed-forward boundary

A boundary input and a local intervention are chosen before the subsystem
runs. The outside may use a shared source and fresh private randomness for
these choices and for its downstream readout. The local seed can depend on
the shared source. Given that source, its draw is independent of outside
randomness. Hence the shared source has to contain all the information
responsible for dependence across the boundary.

An admitted context either uses the shared population or selects a state
with positive population probability. Its upstream routing and downstream
Boolean readout are finite functions. In a multiworld plan the subsystem
uses the same local seed for every planned setting. The boundary law is on
the joint transcript of outgoing values. The context class permits arbitrary
fixed plans and tests of this transcript at supported shared states.
-/

namespace Thesis.Causality.LocalSCMReplacement

open Probability Probability.Distros

/-- The registered alphabet `A` consists of permitted local interventions.
An element of `O` records the whole joint output at one intervention. -/
structure Interface (U I A O E : Type) where
  sharedLabels : FiniteWitness U
  inputs : FiniteWitness I
  interventions : FiniteWitness A
  outputs : FiniteWitness O
  outsideLabels : FiniteWitness E
  shared : Distro U
  outside : Distro E

abbrev Plan (I A : Type) (worlds : Nat) := Fin worlds → I × A

/-- A local model conditional on the exposed shared source. The response
function is the deterministic evaluation of the local mechanisms at the
given boundary input, surgery and unit. -/
structure Subsystem (U I A O : Type) where
  Seed : Type
  noise : U → Distro Seed
  response : U → Seed → I → A → O

/-- All planned settings are evaluated on the same seed. With one setting
this is the usual interventional output law at a fixed boundary input. -/
def Subsystem.boundaryLaw (localModel : Subsystem U I A O) (u : U)
    (plan : Plan I A worlds) : Distro (Fin worlds → O) :=
  (localModel.noise u).map (fun seed world =>
    localModel.response u seed (plan world).1 (plan world).2)

def Interface.sharedEvent (face : Interface U I A O E) (u : U) : Event U :=
  @FiniteProbRecord.singletonEvent U face.sharedLabels.decidableEq u

def Interface.Supported (face : Interface U I A O E) (u : U) : Prop :=
  face.shared.record.EventPositive (face.sharedEvent u)

instance (face : Interface U I A O E) (u : U) : Decidable (face.Supported u) :=
  inferInstanceAs (Decidable (face.shared.record.EventPositive (face.sharedEvent u)))

/-- The shared-source event evaluated on a model's original latent unit. -/
def Interface.sourceEvent (face : Interface U I A O E) (expose : UnitState → U) (u : U) :
    Event UnitState :=
  fun unit => face.sharedEvent u (expose unit)

theorem Interface.exposed_support_iff (face : Interface U I A O E)
    {S : ObservedSignature.{0}} (model : ExactModel S) (expose : model.latent.Assignment → U)
    (sharedLaw : face.shared.SameLaw ⟨model.prior.map expose⟩) (u : U) :
    face.Supported u ↔ model.prior.EventPositive (face.sourceEvent expose u) :=
  QProb.equiv_num_pos_iff (QProb.equiv_trans (sharedLaw (face.sharedEvent u))
    (model.prior.map_probVal expose (face.sharedEvent u)))

/-- An actual SCM supplies a local evaluator and a conditional latent law.
The setting map registers how each input and permitted local intervention
become hard settings of the subsystem. The readout keeps the chosen joint
boundary outputs. On shared states of zero probability the conditional
seed law is immaterial to all admitted contexts. The exposed marginal
must agree with the interface population law. -/
def Subsystem.ofExactModel (face : Interface U I A O E) {S : ObservedSignature.{0}}
    (model : ExactModel S) (expose : model.latent.Assignment → U)
    (sharedLaw : face.shared.SameLaw ⟨model.prior.map expose⟩)
    (setting : I → A → HardIntervention S) (readout : S.Assignment → O) :
    Subsystem U I A O where
  Seed := model.latent.Assignment
  noise u :=
    if positive : face.Supported u then
      ⟨model.prior.conditionOn (face.sourceEvent expose u)
        ((face.exposed_support_iff model expose sharedLaw u).mp positive)⟩
    else ⟨model.prior⟩
  response _ unit input intervention :=
    readout (model.evalUnder (setting input intervention).value unit)

theorem Subsystem.ofExactModel_noise_at (face : Interface U I A O E)
    {S : ObservedSignature.{0}} (model : ExactModel S) (expose : model.latent.Assignment → U)
    (sharedLaw : face.shared.SameLaw ⟨model.prior.map expose⟩)
    (setting : I → A → HardIntervention S) (readout : S.Assignment → O)
    (u : U) (positive : face.Supported u) :
    ((ofExactModel face model expose sharedLaw setting readout).noise u).record =
      model.prior.conditionOn (face.sourceEvent expose u)
        ((face.exposed_support_iff model expose sharedLaw u).mp positive) := by
  simp only [ofExactModel, dif_pos positive]

/-- A context can route inputs and interventions using the shared state
and the outside draw. Its readout can also use those values and the
entire joint transcript. The fixed finite alphabets and fixed laws make
this a finite class of contexts for each declared number of worlds. -/
structure Context (face : Interface U I A O E) (worlds : Nat) where
  selected : Option {u : U // face.Supported u}
  upstream : U → E → Plan I A worlds
  downstream : U → E → Event (Fin worlds → O)

def Context.riskAt {face : Interface U I A O E}
    (context : Context face worlds) (localModel : Subsystem U I A O) (u : U) : SignedRatio :=
  face.outside.rationalExpectation fun outside =>
    ((localModel.boundaryLaw u (context.upstream u outside)).record.probVal
      (context.downstream u outside)).toSignedRatio

def Context.risk {face : Interface U I A O E}
    (context : Context face worlds) (localModel : Subsystem U I A O) : SignedRatio :=
  match context.selected with
  | none => face.shared.rationalExpectation (context.riskAt localModel)
  | some u => context.riskAt localModel u.val

/-- A supported-state test is ordinary singleton conditioning under the
declared shared population law. The outside draw keeps its fixed law. -/
theorem Context.risk_selects_supported {face : Interface U I A O E}
    (context : Context face worlds) (localModel : Subsystem U I A O)
    (u : U) (positive : face.Supported u) :
    SignedRatio.Equiv ({ context with selected := some ⟨u, positive⟩ }.risk localModel)
      ((face.shared.conditionOn (face.sharedEvent u) positive).rationalExpectation
        (context.riskAt localModel)) := by
  let selected := face.shared.conditionOn (face.sharedEvent u) positive
  change SignedRatio.Equiv (context.riskAt localModel u)
    (selected.rationalExpectation (context.riskAt localModel))
  apply SignedRatio.equiv_symm
  refine SignedRatio.equiv_trans ?_ (selected.rationalExpectation_constant (context.riskAt localModel u))
  apply Distro.rationalExpectation_congr_positive
  intro atom listed _
  have kept : face.sharedEvent u atom.1 = true := (List.mem_filter.mp listed).2
  letI : DecidableEq U := face.sharedLabels.decidableEq
  have same : atom.1 = u := of_decide_eq_true kept
  rw [same]
  exact SignedRatio.equiv_refl _

/-- The complete boundary interface quantifies over supported shared states,
declared plans and events of the joint transcript. -/
def BoundaryEquivalent (face : Interface U I A O E) (worlds : Nat)
    (left right : Subsystem U I A O) : Prop :=
  ∀ u, face.Supported u → ∀ plan : Plan I A worlds,
    (left.boundaryLaw u plan).SameLaw (right.boundaryLaw u plan)

theorem boundary_preserves_context {face : Interface U I A O E}
    {left right : Subsystem U I A O} (same : BoundaryEquivalent face worlds left right)
    (context : Context face worlds) : SignedRatio.Equiv (context.risk left) (context.risk right) := by
  have atState (u : U) (positive : face.Supported u) :
      SignedRatio.Equiv (context.riskAt left u) (context.riskAt right u) := by
    unfold Context.riskAt
    apply Distro.rationalExpectation_congr
    intro outside
    exact QProb.toSignedRatio_congr (same u positive _ _)
  unfold Context.risk
  cases context.selected with
  | none =>
    apply Distro.rationalExpectation_congr_positive
    intro atom listed positive
    letI : DecidableEq U := face.sharedLabels.decidableEq
    exact atState atom.1 (face.shared.pmf_pos_of_atom atom listed positive)
  | some u => exact atState u.val u.property

/-- A separating context conditions on a supported shared state, fixes
all inputs and local interventions, and emits a Boolean transcript test. -/
def boundaryTest (face : Interface U I A O E) (u : U) (positive : face.Supported u)
    (plan : Plan I A worlds) (event : Event (Fin worlds → O)) : Context face worlds :=
  ⟨some ⟨u, positive⟩, fun _ _ => plan, fun _ _ => event⟩

theorem boundaryTest_risk (face : Interface U I A O E) (u : U) (positive : face.Supported u)
    (plan : Plan I A worlds) (event : Event (Fin worlds → O)) (localModel : Subsystem U I A O) :
    SignedRatio.Equiv ((boundaryTest face u positive plan event).risk localModel)
      ((localModel.boundaryLaw u plan).record.probVal event).toSignedRatio := by
  unfold boundaryTest Context.risk Context.riskAt
  exact face.outside.rationalExpectation_constant
    (((localModel.boundaryLaw u plan).record.probVal event).toSignedRatio)

theorem contextual_equivalence_iff (face : Interface U I A O E)
    (left right : Subsystem U I A O) :
    (∀ context : Context face worlds, SignedRatio.Equiv (context.risk left) (context.risk right)) ↔
      BoundaryEquivalent face worlds left right := by
  constructor
  · intro indistinguishable u positive plan event
    let test := boundaryTest face u positive plan event
    apply (QProb.toSignedRatio_equiv_iff _ _).mp
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (boundaryTest_risk face u positive plan event left))
      (SignedRatio.equiv_trans (indistinguishable test) (boundaryTest_risk face u positive plan event right))
  · exact boundary_preserves_context

/-- A discrepancy in any supported boundary event supplies a particular
outside context with different risks. -/
theorem boundaryTest_distinguishes {face : Interface U I A O E}
    {left right : Subsystem U I A O} (u : U) (positive : face.Supported u)
    (plan : Plan I A worlds) (event : Event (Fin worlds → O))
    (different : ¬ QProb.Equiv ((left.boundaryLaw u plan).record.probVal event)
      ((right.boundaryLaw u plan).record.probVal event)) :
    ¬ SignedRatio.Equiv ((boundaryTest face u positive plan event).risk left)
      ((boundaryTest face u positive plan event).risk right) := by
  intro unchanged
  apply different
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (boundaryTest_risk face u positive plan event left))
    (SignedRatio.equiv_trans unchanged (boundaryTest_risk face u positive plan event right))

private def worldWitness (worlds : Nat) (labels : FiniteWitness X) :
    FiniteWitness (Fin worlds → X) :=
  FiniteProduct.finiteWitness worlds (fun _ => X) (fun _ => labels.enumeration)
    (fun _ => labels.enumeration_complete) (fun _ => labels.decidableEq)

/-- Check one singleton for every joint transcript, legal plan and
supported shared state. The test skips rows of the shared law with zero
mass, where the value of a local conditional law is immaterial. -/
def boundaryCheck (face : Interface U I A O E) (worlds : Nat)
    (left right : Subsystem U I A O) : Bool :=
  letI : DecidableEq U := face.sharedLabels.decidableEq
  let transcripts := worldWitness worlds face.outputs
  letI : DecidableEq (Fin worlds → O) := transcripts.decidableEq
  face.sharedLabels.enumeration.all fun u =>
    if 0 < (face.shared.pmf u).num then
      (worldWitness worlds (face.inputs.product face.interventions)).enumeration.all fun plan =>
        transcripts.enumeration.all fun output =>
          decide (QProb.Equiv ((left.boundaryLaw u plan).pmf output)
            ((right.boundaryLaw u plan).pmf output))
    else true

theorem boundaryCheck_true_iff (face : Interface U I A O E) (worlds : Nat)
    (left right : Subsystem U I A O) :
    boundaryCheck face worlds left right = true ↔ BoundaryEquivalent face worlds left right := by
  letI : DecidableEq U := face.sharedLabels.decidableEq
  let transcripts := worldWitness worlds face.outputs
  letI : DecidableEq (Fin worlds → O) := transcripts.decidableEq
  let plans := worldWitness worlds (face.inputs.product face.interventions)
  constructor
  · intro checked u positive plan
    have row := List.all_eq_true.mp checked u (face.sharedLabels.enumeration_complete u)
    change 0 < (face.shared.pmf u).num at positive
    rw [if_pos positive] at row
    have tested := List.all_eq_true.mp row plan (plans.enumeration_complete plan)
    apply Distro.sameLaw_of_singletons _ _ (deduplicate transcripts.enumeration)
      (deduplicate_nodup _) (fun output =>
        (mem_deduplicate _ _).mpr (transcripts.enumeration_complete output))
    intro output
    exact of_decide_eq_true (List.all_eq_true.mp tested output (transcripts.enumeration_complete output))
  · intro same
    apply List.all_eq_true.mpr
    intro u _
    by_cases positive : 0 < (face.shared.pmf u).num
    · simp only [if_pos positive, List.all_eq_true, decide_eq_true_eq]
      intro plan _ output _
      exact same u positive plan (FiniteProbRecord.singletonEvent output)
    · simp only [if_neg positive]

end Thesis.Causality.LocalSCMReplacement
