import Thesis.CausalTransport.LocalSCMReplacement
import Thesis.Examples.CausalAbstractionInverse

/-!
# Contextual replacement of a binary treatment subsystem

The outside can feed the treatment value into the subsystem, force its
outcome high, and read the joint pair of outgoing values. It shares the
latent bit that would otherwise set the treatment. The two subsystems
differ only in whether the outcome's fair latent bit is complemented by
treatment. Preserving the joint output law in each individual setting
suffices for all single-world contexts. Two worlds sharing a unit can
distinguish them.
-/

namespace Thesis.Examples.LocalSCMReplacement

open Probability Probability.Distros Causality Causality.BinaryBow
open Causality.LocalSCMReplacement
open Thesis.Examples.CausalAbstractionInverse (pairedModel setTreatment)

private def bitLabels : FiniteWitness Bool :=
  FiniteWitness.ofList [false, true] (by intro value; cases value <;> simp) (by decide)

private def expose (flip : Bool) (unit : (pairedModel flip).latent.Assignment) : Bool :=
  unit root x

private def outsideBit : Distro Bool :=
  ⟨⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩⟩

/-- A context is supplied the shared treatment bit. Its private bit is
independent, and both may affect the upstream route and downstream readout. -/
def boundary : Interface Bool Bool Bool (Bool × Bool) Bool where
  sharedLabels := bitLabels
  inputs := bitLabels
  interventions := bitLabels
  outputs := bitLabels.product bitLabels
  outsideLabels := bitLabels
  shared := ⟨(pairedModel false).prior.map (expose false)⟩
  outside := outsideBit

private def setting (input forceOutcome : Bool) : HardIntervention signature :=
  if forceOutcome then (setTreatment input).set y true else setTreatment input

private def readout (state : signature.Assignment) : Bool × Bool := (state x, state y)

theorem shared_source_law (flip : Bool) :
    boundary.shared.SameLaw ⟨(pairedModel flip).prior.map (expose flip)⟩ := by
  intro event
  exact QProb.equiv_refl _

def localModel (flip : Bool) : Subsystem Bool Bool Bool (Bool × Bool) :=
  Subsystem.ofExactModel boundary (pairedModel flip) (expose flip) (shared_source_law flip) setting readout

theorem single_world_table : boundaryCheck boundary 1 (localModel false) (localModel true) = true := by
  decide +kernel

/-- This is a stochastic feed-forward context. The private bit and the
shared bit jointly select the input, and the private bit selects a test of
the downstream outcome. -/
def routed : Context boundary 1 where
  selected := none
  upstream u outside _ := (Bool.xor u outside, false)
  downstream _ outside transcript := Bool.xor (transcript 0).2 outside

theorem routed_replacement : SignedRatio.Equiv
    (routed.risk (localModel false)) (routed.risk (localModel true)) :=
  boundary_preserves_context
    ((boundaryCheck_true_iff boundary 1 _ _).mp single_world_table) routed

private theorem sharedFalse : boundary.Supported false := by decide +kernel

private def bothInputs : Plan Bool Bool 2 := fun world => (world.val == 1, false)
private def changed : Event (Fin 2 → (Bool × Bool)) :=
  fun transcript => Bool.xor (transcript 0).2 (transcript 1).2

/-- The same supported shared-source condition and the same two interventions
detect a difference once the output values are paired on the same unit. -/
def separator : Context boundary 2 := boundaryTest boundary false sharedFalse bothInputs changed

theorem separates_at_supported_state :
    SignedRatio.Equiv (separator.risk (localModel false)) SignedRatio.zero ∧
    SignedRatio.Equiv (separator.risk (localModel true)) SignedRatio.one := by
  constructor <;> decide +kernel

theorem two_world_table : boundaryCheck boundary 2 (localModel false) (localModel true) = false := by
  decide +kernel

end Thesis.Examples.LocalSCMReplacement
