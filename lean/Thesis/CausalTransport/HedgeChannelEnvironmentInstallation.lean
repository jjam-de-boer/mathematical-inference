import Thesis.CausalTransport.HedgeChannelEnvironment
import Thesis.CausalTransport.HedgeChannelObservational

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open HedgeChannelInstallation

/-!
# Installing hedge pairs with genuine independent shared-input signals

Small-forest and background signals may now read both declared observed
parents and the terminal environment bit at each incident original pair root.
The large-channel correction remains the checked correction on the actual
kept arrows.  All main incidence characters use the independent initial
coordinates; they never reuse an environment bit as their own noise.

The original installation's local correction evaluates the small and
background functions only at its current child and current parents.  We
therefore supply their already computed local values as constant functions
when building that one row.  This does not give a mechanism another child's
inputs: the only latent argument it receives is its own typed incident map.
The explicit local-evaluation lemma below verifies this use of the old API.

At each fixed environment the installed centres are exactly the previous
centres with arbitrary ordinary parent signals.  Its complete numerator
matching theorem applies pointwise, and `HedgeChannelEnvironment` integrates
that equality over the actual independent environment support.  Thus these
are actual compatible, fully positive models with equal entire observed
laws for every supplied hedge and every legal latent-input signal family.

No causal or conditional separation is inferred from those three properties.
The remaining task is to construct signal families on irreducible terminal
active paths and prove a nonzero normalized query change after this actual
environment integration.  This module removes the observed-parent-only
restriction; it does not assume that the widened family has universal gaps.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- One child's genuine incident environment bits.  The incidence proof
is required for every read; nonincident original roots are unavailable. -/
abbrev EnvironmentInputs (G : ObservedGraph S) (child : Fin S.count) :=
  (root : Fin (pairRootCount G.binary)) -> pairRootIncident G.binary root child = true -> Bool

/-- A local signal may read observed parents and incident reserved bits,
but no complete shared assignment or another child's observed value. -/
abbrev ParentSignal (G : ObservedGraph S) :=
  (child : Fin S.count) -> S.binary.ParentValues child -> EnvironmentInputs G child -> Bool

/-- Read only the independent terminal coordinates of incident vectors. -/
def environmentInputs (G : ObservedGraph S) (channels : Nat) (child : Fin S.count)
    (inputs : (PairRootChannels.extension G.binary (channels + 1)).Inputs child) : EnvironmentInputs G child :=
  fun root incident => inputs root incident (Fin.last channels)

/-- The initial coordinates retain all actual main incidence inputs. -/
def mainInputs (G : ObservedGraph S) (channels : Nat) (child : Fin S.count)
    (inputs : (PairRootChannels.extension G.binary (channels + 1)).Inputs child) :
    (PairRootChannels.extension G.binary channels).Inputs child :=
  fun root incident channel => inputs root incident channel.castSucc

/-- Freezing the environment gives an arbitrary ordinary typed parent
function.  This is a proof parameter, not a mechanism with global inputs. -/
def frozenParentSignal (signal : ParentSignal G)
    (environment : PairRootChannels.Environment.Assignment G.binary) : HedgeChannelInstallation.ParentSignal S :=
  fun child parents => signal child parents (fun root _incident => environment root)

private theorem largeParentSignal_local (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : HedgeChannelInstallation.ParentSignal S)
    (index : Fin (masks (outer w)).length) (child : Fin S.count) (parents : S.binary.ParentValues child) :
    largeParentSignal w rich (fun _ _ => smallSignal child parents) (fun _ _ => backgroundSignal child parents)
      index child parents = largeParentSignal w rich smallSignal backgroundSignal index child parents := by
  let originalParents : S.ParentValues child := fun parent edge => BinaryEncoding.value rich parent (parents parent edge)
  let restoredParents : S.binary.ParentValues child := fun parent edge => hedgeIsSecond rich parent (originalParents parent edge)
  have restored : restoredParents = parents := by
    funext parent edge
    exact BinaryEncoding.bit_value rich parent (parents parent edge)
  change Bool.xor (if w.small child then smallSignal child parents else false)
      (Bool.xor (hedgeForestParentBitsFrom rich (restrictChild (NodeSet.diff w.large w.small) w.child) child originalParents)
        (Bool.xor (if selected w index child then backgroundSignal child parents else false)
          (hedgeForestParentBitsFrom rich (restrictChild (selected w index) w.child) child originalParents))) =
    Bool.xor (if w.small child then smallSignal child restoredParents else false)
      (Bool.xor (hedgeForestParentBitsFrom rich (restrictChild (NodeSet.diff w.large w.small) w.child) child originalParents)
        (Bool.xor (if selected w index child then backgroundSignal child restoredParents else false)
          (hedgeForestParentBitsFrom rich (restrictChild (selected w index) w.child) child originalParents)))
  rw [restored]

private theorem leftParentSignal_local (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : HedgeChannelInstallation.ParentSignal S)
    (child : Fin S.count) (parents : S.binary.ParentValues child) (channel : Fin (channelCount w)) :
    leftParentSignal w rich (fun _ _ => smallSignal child parents) (fun _ _ => backgroundSignal child parents)
      child parents channel = leftParentSignal w rich smallSignal backgroundSignal child parents channel := by
  unfold leftParentSignal
  cases role w channel with
  | large index => exact largeParentSignal_local w rich smallSignal backgroundSignal index child parents
  | small => rfl
  | background _ => rfl

private theorem rightParentSignal_local (w : HedgeWitness G q)
    (smallSignal backgroundSignal : HedgeChannelInstallation.ParentSignal S)
    (child : Fin S.count) (parents : S.binary.ParentValues child) (channel : Fin (channelCount w)) :
    rightParentSignal w (fun _ _ => smallSignal child parents) (fun _ _ => backgroundSignal child parents)
      child parents channel = rightParentSignal w smallSignal backgroundSignal child parents channel := by
  unfold rightParentSignal
  cases role w channel <;> rfl

/-- Each left centre uses the unchanged kept-edge correction, the current
row's two local signals, and only its actual main incidence coordinates. -/
def leftSignals (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) : HedgeChannelEnvironment.Signals G (channelCount w) :=
  fun child parents inputs => HedgeChannelInstallation.leftSignals w rich
    (fun _ _ => smallSignal child parents (environmentInputs G (channelCount w) child inputs))
    (fun _ _ => backgroundSignal child parents (environmentInputs G (channelCount w) child inputs))
    child parents (mainInputs G (channelCount w) child inputs)

/-- The right model reads the same local environment, independently of all
its main channel coordinates and with no change in row capacities. -/
def rightSignals (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal G) :
    HedgeChannelEnvironment.Signals G (channelCount w) :=
  fun child parents inputs => HedgeChannelInstallation.rightSignals w
    (fun _ _ => smallSignal child parents (environmentInputs G (channelCount w) child inputs))
    (fun _ _ => backgroundSignal child parents (environmentInputs G (channelCount w) child inputs))
    child parents (mainInputs G (channelCount w) child inputs)

private theorem environmentInputs_join (channels : Nat) (child : Fin S.count)
    (environment : PairRootChannels.Environment.Assignment G.binary)
    (inputs : (PairRootChannels.extension G.binary channels).Inputs child) :
    environmentInputs G channels child (fun root incident => FiniteProduct.extend (environment root) (inputs root incident)) =
      (fun root _incident => environment root) := by
  funext root incident
  exact FiniteProduct.extend_last (Value := fun _ => Bool) (environment root) (inputs root incident)

private theorem mainInputs_join (channels : Nat) (child : Fin S.count)
    (environment : PairRootChannels.Environment.Assignment G.binary)
    (inputs : (PairRootChannels.extension G.binary channels).Inputs child) :
    mainInputs G channels child (fun root incident => FiniteProduct.extend (environment root) (inputs root incident)) = inputs := by
  funext root incident channel
  exact FiniteProduct.extend_castSucc (Value := fun _ => Bool) (environment root) (inputs root incident) channel

/-- At a fixed environment the entire left centre family is the old family
with the frozen parent functions.  This is literal function equality at all
rows, parents, incident main inputs and channels, not just a character mean. -/
theorem frozen_leftSignals (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (environment : PairRootChannels.Environment.Assignment G.binary) :
    HedgeChannelEnvironment.frozenSignals G (channelCount w) (leftSignals w rich smallSignal backgroundSignal) environment =
      HedgeChannelInstallation.leftSignals w rich (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment) := by
  funext child parents inputs
  unfold HedgeChannelEnvironment.frozenSignals leftSignals
  rw [environmentInputs_join, mainInputs_join]
  funext channel
  unfold HedgeChannelInstallation.leftSignals HedgeChannelTable.incidenceSignals
  apply congrArg (fun phase => Bool.xor phase _)
  exact leftParentSignal_local w rich (frozenParentSignal smallSignal environment)
    (frozenParentSignal backgroundSignal environment) child parents channel

/-- The right centres have the same literal frozen-environment identity. -/
theorem frozen_rightSignals (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal G)
    (environment : PairRootChannels.Environment.Assignment G.binary) :
    HedgeChannelEnvironment.frozenSignals G (channelCount w) (rightSignals w smallSignal backgroundSignal) environment =
      HedgeChannelInstallation.rightSignals w (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment) := by
  funext child parents inputs
  unfold HedgeChannelEnvironment.frozenSignals rightSignals
  rw [environmentInputs_join, mainInputs_join]
  funext channel
  unfold HedgeChannelInstallation.rightSignals HedgeChannelTable.incidenceSignals
  apply congrArg (fun phase => Bool.xor phase _)
  exact rightParentSignal_local w (frozenParentSignal smallSignal environment)
    (frozenParentSignal backgroundSignal environment) child parents channel

/-- Actual left and right SCMs on one common enlarged pair-root alphabet. -/
def leftModel (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) : ExactModel S.binary :=
  HedgeChannelEnvironment.model G (channelCount w) (leftTables w) (leftSignals w rich smallSignal backgroundSignal)

def rightModel (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal G) : ExactModel S.binary :=
  HedgeChannelEnvironment.model G (channelCount w) (rightTables w) (rightSignals w smallSignal backgroundSignal)

/-- Both actual models retain precisely the original projected graph and
the canonical at-most-two-child incidence bound. -/
theorem models_compatible (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) :
    Compatible (leftModel w rich smallSignal backgroundSignal) G.binary ∧
      Compatible (rightModel w smallSignal backgroundSignal) G.binary :=
  ⟨HedgeChannelEnvironment.model_compatible G _ _ _, HedgeChannelEnvironment.model_compatible G _ _ _⟩

/-- Positivity covers every complete Boolean observed sample on both sides,
not only a selected conditional evidence event or a distinguished root. -/
theorem models_positive (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) :
    ObservationallyPositive (leftModel w rich smallSignal backgroundSignal) ∧
      ObservationallyPositive (rightModel w smallSignal backgroundSignal) :=
  ⟨HedgeChannelEnvironment.model_positive G _ _ _, HedgeChannelEnvironment.model_positive G _ _ _⟩

/-- Every legal local shared-input signal family gives equality of the
entire actual observational laws.  The complete old expansion matches at
each environment, and the checked enlarged prior integrates that equality.
No assumed mixture law, readiness flag or full-sample read is used. -/
theorem models_observationallyEquivalent (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) :
    ObservationallyEquivalent (leftModel w rich smallSignal backgroundSignal)
      (rightModel w smallSignal backgroundSignal) := by
  apply HedgeChannelEnvironment.models_observationallyEquivalent_of_frozenNumerators G (channelCount w)
    (leftTables w) (rightTables w) (leftSignals w rich smallSignal backgroundSignal)
    (rightSignals w smallSignal backgroundSignal) (capacities_equal w)
  intro environment sample
  rw [frozen_leftSignals, frozen_rightSignals]
  exact integratedNumerators_equal w rich (frozenParentSignal smallSignal environment)
    (frozenParentSignal backgroundSignal environment) sample

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
