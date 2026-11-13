import Thesis.CausalTransport.HedgeChannelEnvironmentFactorization
import Thesis.CausalTransport.HedgeChannelProjection
import Thesis.Probability.FiniteBooleanBlocks

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open HedgeChannelInstallation

/-!
# The actual environment-and-observation support on one Boolean cube

The installed countermodels already integrate over every independent reserved
pair-root bit and every observed assignment.  The interaction inequalities use
a single false-valued Boolean cylinder.  This module connects those two
presentations by the explicit block reads and inverse, with the *actual*
duplicate-free observed enumeration on the model side.

Every original pair root gets one environment coordinate, and every original
observed node gets one observed coordinate.  This is only a proof-level
indexing of assignments.  Local mechanisms still read their typed directed
parents and incident roots; none is given access to this whole cube.

The sum identity permits arbitrary mixed integrands.  In particular it does
not assume that shared-input signals factor over the two displayed blocks.
The restricted observed support is proved to be a permutation of the actual
observed event list before its integer sum is used.  Fixed coordinates,
empty masks and zero-sized blocks are all retained literally.

On the original action cut, conflicting samples have zero actual background
product.  This proves the additional action restriction, and the hedge's
small-forest avoidance makes its installed capacity and amplitude products
positive constants.  Their literal scalars are then separated from both
complete cube integrals without cancelling any varying background row.

Connecting these support sums to homogeneous interaction weights, and deriving
the required parity data from every terminal active path, remain separate
obligations.  Reindexing alone is not a conditional completeness proof.
-/

variable {S : ObservedSignature.{0}}

/-- One proof coordinate per actual reserved pair-root bit, followed by one
per original observed node.  The model's latent incidence is not enlarged. -/
abbrev Cube (G : ObservedGraph S) := Fin (pairRootCount G.binary + S.count) -> Bool

/-- Recover the actual independent reserved-root assignment. -/
def cubeEnvironment (G : ObservedGraph S) (point : Cube G) :
    PairRootChannels.Environment.Assignment G.binary :=
  FiniteProduct.BooleanBlocks.leftBlock (pairRootCount G.binary) S.count point

/-- Recover every original observed coordinate from the same cube point. -/
def cubeSample (G : ObservedGraph S) (point : Cube G) : S.binary.Assignment :=
  FiniteProduct.BooleanBlocks.rightBlock (pairRootCount G.binary) S.count point

/-- Assemble the two actual assignments without selecting an inverse or
merging their independent roots into a new shared source. -/
def joinCube (G : ObservedGraph S) (environment : PairRootChannels.Environment.Assignment G.binary)
    (sample : S.binary.Assignment) : Cube G :=
  FiniteProduct.BooleanBlocks.join (pairRootCount G.binary) S.count environment sample

/-- The environment read restores every original pair-root bit. -/
theorem cubeEnvironment_joinCube (G : ObservedGraph S)
    (environment : PairRootChannels.Environment.Assignment G.binary) (sample : S.binary.Assignment) :
    cubeEnvironment G (joinCube G environment sample) = environment :=
  FiniteProduct.BooleanBlocks.leftBlock_join _ _ environment sample

/-- The observed read restores every original node, including nodes outside
the requested event.  Such nodes are still integrated over by the likelihood. -/
theorem cubeSample_joinCube (G : ObservedGraph S)
    (environment : PairRootChannels.Environment.Assignment G.binary) (sample : S.binary.Assignment) :
    cubeSample G (joinCube G environment sample) = sample :=
  FiniteProduct.BooleanBlocks.rightBlock_join _ _ environment sample

/-- The model-side reads reconstruct each supplied cube point literally. -/
theorem joinCube_reads (G : ObservedGraph S) (point : Cube G) :
    joinCube G (cubeEnvironment G point) (cubeSample G point) = point :=
  FiniteProduct.BooleanBlocks.join_split _ _ point

/-- Fix only the designated observed coordinates.  All actual independent
environment bits remain free, even if their incident children are fixed. -/
def cubeMask (G : ObservedGraph S) (nodes : NodeSet S) : Cube G :=
  FiniteProduct.BooleanBlocks.join (pairRootCount G.binary) S.count (fun _ => false) nodes

/-- Combining two observed event masks combines exactly their corresponding
cube masks.  Environment coordinates remain free on both sides, including
when the two observed events overlap. -/
theorem cubeMask_union (G : ObservedGraph S) (left right : NodeSet S) :
    cubeMask G (NodeSet.union left right) = (fun index => cubeMask G left index || cubeMask G right index) := by
  funext index
  unfold cubeMask FiniteProduct.BooleanBlocks.join NodeSet.union
  by_cases earlier : index.val < pairRootCount G.binary
  · simp only [dif_pos earlier, Bool.false_or]
  · simp only [dif_neg earlier]

/-- A listed cube point fixes exactly the designated observed coordinates
to false.  The actual suffix read and the joined mask justify this fact;
the independent environment prefix is not conditioned on a guessed value. -/
theorem cubeSample_false_of_mem (G : ObservedGraph S) (nodes : NodeSet S) (point : Cube G)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count) (cubeMask G nodes))
    (child : Fin S.count) (fixed : nodes child = true) : cubeSample G point child = false := by
  have observed := (FiniteProduct.BooleanBlocks.cylinder_member_iff
    (pairRootCount G.binary) S.count (cubeMask G nodes) point).mp listed |>.2
  unfold cubeMask at observed
  rw [FiniteProduct.BooleanBlocks.rightBlock_join] at observed
  exact (FiniteProduct.falseCylinderEnumeration_member_iff S.count nodes (cubeSample G point)).mp observed child fixed

/-- The restricted Boolean observed product lists exactly the same samples
as filtering the actual model's observed enumeration.  Deduplication in that
enumeration does not authorize assuming literal list equality or changing
any event multiplicity; the complete support permutation supplies the link. -/
theorem observedCylinder_perm_filter (nodes : NodeSet S) :
    (FiniteProduct.falseCylinderEnumeration S.count nodes).Perm
      (S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count nodes)) := by
  letI : DecidableEq (Fin S.count -> Bool) :=
    FiniteProduct.assignmentDecidableEq S.count (fun _ => Bool) (fun _ => inferInstance)
  apply ConstructivePermutation.perm_of_nodup_mem_iff
  · exact FiniteProduct.falseCylinderEnumeration_nodup S.count nodes
  · exact List.Pairwise.filter _ S.binary.assignmentEnumeration_nodup
  · intro sample
    rw [FiniteProduct.falseCylinderEnumeration_member_iff, List.mem_filter,
      FiniteProduct.falseCylinder_eq_true_iff]
    exact ⟨fun consistent => ⟨S.binary.assignmentEnumeration_complete sample, consistent⟩,
      fun selected => selected.2⟩

/-- Every complete cube-cylinder sum is the actual environment-by-observed
event sum.  Its integrand may read both blocks jointly; all model assignments
are included before summation, rather than one selected environment slice. -/
theorem cubeCylinder_sum_eq_environment_sum (G : ObservedGraph S) (nodes : NodeSet S)
    (term : PairRootChannels.Environment.Assignment G.binary -> S.binary.Assignment -> Int) :
    ((FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count) (cubeMask G nodes)).map
      (fun point => term (cubeEnvironment G point) (cubeSample G point))).sum =
      ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
        ((S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count nodes)).map
          (term environment)).sum)).sum := by
  unfold cubeMask cubeEnvironment cubeSample
  rw [FiniteProduct.BooleanBlocks.cylinder_sum_split]
  simp only [FiniteProduct.BooleanBlocks.leftBlock_join, FiniteProduct.BooleanBlocks.rightBlock_join]
  change ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
      ((FiniteProduct.falseCylinderEnumeration S.count nodes).map (term environment)).sum)).sum = _
  apply congrArg List.sum
  apply List.map_congr_left
  intro environment _listed
  exact FiniteSupportedSum.sum_eq_of_perm ((observedCylinder_perm_filter nodes).map (term environment))

/-! ## The original action coordinates are removed only at proved zero terms -/

/-- A mixed environment/event sum becomes the combined action-and-event
cube cylinder only when its actual integrand vanishes on every conflicting
action assignment.  This does not silently strengthen the requested event
or replace forced indicators by one at inconsistent samples. -/
theorem cubeCylinder_sum_eq_action_event_sum (G : ObservedGraph S) (action nodes : NodeSet S)
    (term : PairRootChannels.Environment.Assignment G.binary -> S.binary.Assignment -> Int)
    (zero : forall environment sample,
      FiniteProduct.falseCylinder S.count action sample = false -> term environment sample = 0) :
    ((FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union action nodes))).map
        (fun point => term (cubeEnvironment G point) (cubeSample G point))).sum =
      ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
        ((S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count nodes)).map
          (term environment)).sum)).sum := by
  rw [cubeCylinder_sum_eq_environment_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro environment _listed
  have restricted := FiniteSupportedSum.sum_eq_filter_of_zero
    (S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count nodes))
    (FiniteProduct.falseCylinder S.count action) (term environment)
    (fun sample _selected conflicting => zero environment sample conflicting)
  rw [List.filter_filter] at restricted
  have combined : (fun sample : S.binary.Assignment =>
      FiniteProduct.falseCylinder S.count action sample && FiniteProduct.falseCylinder S.count nodes sample) =
      FiniteProduct.falseCylinder S.count (NodeSet.union action nodes) := by
    funext sample
    exact (FiniteProduct.falseCylinder_union S.count action nodes sample).symm
  exact (restricted.trans (congrArg (fun event : S.binary.Assignment -> Bool =>
    ((S.binary.assignmentEnumeration.filter event).map (term environment)).sum) combined)).symm

variable {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## The actual small-row factors are constant under the original action -/

/-- Product of the installed capacities at exactly the small-forest rows.
All other original observed rows contribute one; they are not removed from
the background likelihood.  This is a natural scalar, not a probability. -/
def smallCapacityScalar (w : HedgeWitness G q) : Nat :=
  FiniteProduct.natProduct S.count (fun child => if w.small child then (rightTables w child).capacity else 1)

/-- Product of the installed small-channel amplitudes, including its actual
anchor exponent.  Replacing this with an ordinary power would lose that
coefficient; retaining the installed tables makes the scalar literal. -/
def smallAmplitudeScalar (w : HedgeWitness G q) : Nat :=
  FiniteProduct.natProduct S.count (fun child =>
    if w.small child then (rightTables w child).amplitude (smallChannel w) else 1)

theorem smallCapacityScalar_positive (w : HedgeWitness G q) : 0 < smallCapacityScalar w := by
  apply FiniteProduct.natProduct_positive
  intro child
  cases inside : w.small child with
  | false => exact Nat.zero_lt_one
  | true => exact (rightTables w child).capacity_positive

theorem smallAmplitudeScalar_positive (w : HedgeWitness G q) : 0 < smallAmplitudeScalar w := by
  apply FiniteProduct.natProduct_positive
  intro child
  cases inside : w.small child with
  | false => exact Nat.zero_lt_one
  | true =>
      exact HedgeChannelCoefficients.tables_amplitude_positive
        (channelCount w) S.count (rightNodes w) (rightAnchors w) (rightDeficits w) child (smallChannel w)

/-- Every small row is free under the *full original* action, by the hedge's
avoidance certificate.  Its capacity product is consequently the displayed
constant even at samples conflicting with other forced rows.  Those outside
conflicts remain zero in the separate background product. -/
theorem smallCapacityProductUnder_eq_scalar_of_action (w : HedgeWitness G q) (sample : S.binary.Assignment) :
    smallCapacityProductUnder w (falseActionTarget q.action) sample = (smallCapacityScalar w : Int) := by
  unfold smallCapacityProductUnder smallCapacityScalar
  rw [← FiniteProduct.iProduct_nat]
  apply FiniteProduct.iProduct_congr S.count
  intro child
  cases inside : w.small child with
  | false => rfl
  | true =>
      simp only [if_true, capacityRowUnder, falseActionTarget,
        w.small_avoids_intervention child inside, Bool.false_eq_true, if_false,
        BooleanChannelTable.expansionCoefficientUnder]

/-- The actual full-small amplitude is likewise constant because none of
its rows is forced.  This is justified by small-forest avoidance, not by
assuming a consistent observed sample or cancelling another coefficient. -/
theorem smallAmplitudeProductUnder_eq_scalar_of_action (w : HedgeWitness G q) (sample : S.binary.Assignment) :
    smallAmplitudeProductUnder w (falseActionTarget q.action) sample = (smallAmplitudeScalar w : Int) := by
  unfold smallAmplitudeProductUnder smallAmplitudeScalar
  rw [← FiniteProduct.iProduct_nat]
  apply FiniteProduct.iProduct_congr S.count
  intro child
  cases inside : w.small child with
  | false => rfl
  | true =>
      simp only [if_true, falseActionTarget, w.small_avoids_intervention child inside,
        Bool.false_eq_true, if_false, BooleanChannelTable.expansionCoefficientUnder]

private theorem outsideBackground_zero_of_action_conflict (w : HedgeWitness G q)
    (backgroundSignal : HedgeChannelInstallation.ParentSignal S) (sample : S.binary.Assignment)
    (conflicting : FiniteProduct.falseCylinder S.count q.action sample = false) :
    outsideBackgroundProductUnder w backgroundSignal (falseActionTarget q.action) sample = 0 := by
  rcases FiniteProduct.falseCylinder_conflict_of_false S.count q.action sample conflicting with
    ⟨child, forced, value⟩
  have outsideSmall : w.small child = false := by
    cases inside : w.small child with
    | false => rfl
    | true =>
        exact False.elim (Bool.false_ne_true ((w.small_avoids_intervention child inside).symm.trans forced))
  apply outsideBackgroundProductUnder_zero_of_conflict w backgroundSignal _ sample child false outsideSmall
  · simp only [falseActionTarget, forced, if_true]
  · intro equal
    exact Bool.false_ne_true (equal.symm.trans value)

/-- The installed background event mass on the original full action cut is
the complete cube-cylinder sum of its actual local factors.  The equality
includes every independent environment and every retained observed node;
forced conflicts are eliminated by their proved zero background product. -/
theorem backgroundEventSum_eq_cubeCylinder_sum_of_action
    (w : HedgeWitness G q) (backgroundSignal : ParentSignal G) (nodes : NodeSet S) :
    backgroundEventSum w backgroundSignal (falseActionTarget q.action)
        (FiniteProduct.falseCylinder S.count nodes) =
      ((FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
        (cubeMask G (NodeSet.union q.action nodes))).map (fun point =>
          smallCapacityProductUnder w (falseActionTarget q.action) (cubeSample G point) *
            outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal (cubeEnvironment G point))
              (falseActionTarget q.action) (cubeSample G point))).sum := by
  unfold backgroundEventSum
  symm
  apply cubeCylinder_sum_eq_action_event_sum G q.action nodes
    (fun environment sample => smallCapacityProductUnder w (falseActionTarget q.action) sample *
      outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal environment) (falseActionTarget q.action) sample)
  intro environment sample conflicting
  rw [outsideBackground_zero_of_action_conflict w _ sample conflicting, Int.mul_zero]

/-- Separate the literal positive small-capacity scalar from the complete
background cylinder integral.  No actual latent environment, outside row,
event coordinate or forced conflict is discarded in this factorization. -/
theorem backgroundEventSum_eq_scaled_cube_sum_of_action
    (w : HedgeWitness G q) (backgroundSignal : ParentSignal G) (nodes : NodeSet S) :
    backgroundEventSum w backgroundSignal (falseActionTarget q.action)
        (FiniteProduct.falseCylinder S.count nodes) =
      (smallCapacityScalar w : Int) *
        ((FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
          (cubeMask G (NodeSet.union q.action nodes))).map (fun point =>
            outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal (cubeEnvironment G point))
              (falseActionTarget q.action) (cubeSample G point))).sum := by
  rw [backgroundEventSum_eq_cubeCylinder_sum_of_action]
  simp only [smallCapacityProductUnder_eq_scalar_of_action]
  exact FiniteSupportedSum.sum_mul_left _ _ _

/-- The complete small-character interaction uses the very same cube and
the very same full action cut as the old background.  Its sign is retained
on every surviving sample; a single positive frozen environment is not
substituted for this complete signed event integral. -/
theorem interactionEventSum_eq_cubeCylinder_sum_of_action
    (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal G) (nodes : NodeSet S) :
    interactionEventSum w smallSignal backgroundSignal (falseActionTarget q.action)
        (FiniteProduct.falseCylinder S.count nodes) =
      ((FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
        (cubeMask G (NodeSet.union q.action nodes))).map (fun point =>
          smallAmplitudeProductUnder w (falseActionTarget q.action) (cubeSample G point) *
            FiniteProbRecord.characterSign
              (signalPhase w.small (frozenParentSignal smallSignal (cubeEnvironment G point)) (cubeSample G point)) *
            outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal (cubeEnvironment G point))
              (falseActionTarget q.action) (cubeSample G point))).sum := by
  unfold interactionEventSum
  symm
  apply cubeCylinder_sum_eq_action_event_sum G q.action nodes
    (fun environment sample => smallAmplitudeProductUnder w (falseActionTarget q.action) sample *
      FiniteProbRecord.characterSign (signalPhase w.small (frozenParentSignal smallSignal environment) sample) *
      outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal environment) (falseActionTarget q.action) sample)
  intro environment sample conflicting
  rw [outsideBackground_zero_of_action_conflict w _ sample conflicting, Int.mul_zero]

/-- The interaction's literal positive small-amplitude scalar multiplies
the complete signed background cylinder integral.  Its conditioning integral
is not assumed zero; this exact formula can be used for joint and evidence
events separately before their normalized cross-product is compared. -/
theorem interactionEventSum_eq_scaled_cube_sum_of_action
    (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal G) (nodes : NodeSet S) :
    interactionEventSum w smallSignal backgroundSignal (falseActionTarget q.action)
        (FiniteProduct.falseCylinder S.count nodes) =
      (smallAmplitudeScalar w : Int) *
        ((FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
          (cubeMask G (NodeSet.union q.action nodes))).map (fun point =>
            FiniteProbRecord.characterSign
              (signalPhase w.small (frozenParentSignal smallSignal (cubeEnvironment G point)) (cubeSample G point)) *
            outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal (cubeEnvironment G point))
              (falseActionTarget q.action) (cubeSample G point))).sum := by
  rw [interactionEventSum_eq_cubeCylinder_sum_of_action]
  simp only [smallAmplitudeProductUnder_eq_scalar_of_action, Int.mul_assoc]
  exact FiniteSupportedSum.sum_mul_left _ _ _

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
