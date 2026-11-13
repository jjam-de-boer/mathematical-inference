import Thesis.CausalTransport.HedgeChannelEnvironmentLinear

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open HedgeChannelInstallation
open FiniteBooleanInteraction

/-!
# Actual installed event masses as positive homogeneous moments

The cube support identity and local XOR construction are not substitute
likelihoods.  This module identifies their interaction product with the
installed model's actual outside-small background at every action-consistent
point.  Small and forced rows contribute a unit factor here; their installed
small capacity and amplitude scalars were retained separately by the cube
factorization.  All other rows retain their actual capacity and background
amplitude, with the proved strict capacity room of the installed power tables.

Consequently the complete old background event sum is the positive small
capacity scalar times the unit-character moment.  The actual complete
interaction event sum is the positive small amplitude scalar times the full
small-forest character moment.  These equalities hold independently for any
supplied original event mask, including joint and conditioning masks.

No positive integral, matched conditioning mass, homogeneous-phase readiness
flag or formal likelihood polynomial is assumed.  Homogeneity comes from the
legal local mask interpreter, and the coefficient identities come from the
actual installed tables and hard-intervention indicators.  Universal terminal
coverage still requires the active path to construct strict parity data.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- Actual capacity of an outside-small free row; other rows are the unit
in the separate background product.  This does not replace the small rows'
capacity scalar or an inconsistent forced indicator by one. -/
def backgroundCapacity (w : HedgeWitness G q) (child : Fin S.count) : Int :=
  if w.small child || q.action child then 1 else ((rightTables w child).capacity : Int)

/-- Actual background amplitude of every outside-small free row.  Small and
forced rows have zero background amplitude, with no extra interaction factor. -/
def backgroundAmplitude (w : HedgeWitness G q) (child : Fin S.count) : Int :=
  if w.small child || q.action child then 0 else ((rightTables w child).amplitude (backgroundChannel w child) : Int)

private theorem installed_background_amplitude (w : HedgeWitness G q) (child : Fin S.count) :
    (rightTables w child).amplitude (backgroundChannel w child) =
      HedgeChannelCoefficients.ordinaryAmplitude (channelCount w) S.count := by
  simp only [rightTables, HedgeChannelCoefficients.tables, BooleanChannelTable.ofCapacity,
    HedgeChannelCoefficients.rowExponent, rightAnchors, role_backgroundChannel]
  rfl

/-- The installed integer interaction amplitudes are nonnegative at all
rows, including the deliberately zero small and forced background factors. -/
theorem backgroundAmplitude_nonneg (w : HedgeWitness G q) (child : Fin S.count) :
    0 <= backgroundAmplitude w child := by
  unfold backgroundAmplitude
  split
  · exact Int.le_refl 0
  · exact Int.natCast_nonneg _

/-- Every selected free outside-small background row has a strictly
positive actual amplitude.  Positivity is not required of the unit rows,
whose deliberately zero amplitude is used by the same weight identity. -/
theorem backgroundAmplitude_positive_of_free (w : HedgeWitness G q) (child : Fin S.count)
    (outsideSmall : w.small child = false) (free : q.action child = false) :
    0 < backgroundAmplitude w child := by
  simp only [backgroundAmplitude, outsideSmall, free, Bool.false_or, Bool.false_eq_true, if_false]
  have positive : 0 < (rightTables w child).amplitude (backgroundChannel w child) :=
    HedgeChannelCoefficients.tables_amplitude_positive
      (channelCount w) S.count (rightNodes w) (rightAnchors w) (rightDeficits w) child (backgroundChannel w child)
  omega

/-- Strict positive capacity room for the very coefficients in the actual
background.  Free rows use the installed ordinary bias; unit rows have room
zero below one.  No arbitrary channel-amplitude comparison is substituted. -/
theorem backgroundAmplitude_lt_capacity (w : HedgeWitness G q) (child : Fin S.count) :
    backgroundAmplitude w child < backgroundCapacity w child := by
  unfold backgroundAmplitude backgroundCapacity
  by_cases omitted : (w.small child || q.action child) = true
  · rw [if_pos omitted, if_pos omitted]
    decide
  · rw [if_neg omitted, if_neg omitted, installed_background_amplitude,
      show (rightTables w child).capacity = HedgeChannelCoefficients.capacity (channelCount w) S.count from
        HedgeChannelCoefficients.tables_capacity _ _ _ _ _ child]
    have room := HedgeChannelCoefficients.ordinaryAmplitude_lt_capacity (channelCount w) S.count
    omega

/-- The actual action-consistent background product is precisely the
homogeneous interaction weight.  Every original observed row occurs once;
only its proved small/forced status makes its separate background factor
unit.  Shared environment inputs remain in the actual legal row phases. -/
theorem outsideBackground_eq_weight_of_consistent
    (w : HedgeWitness G q) (background : LinearSignal G) (point : Cube G)
    (consistent : forall child, q.action child = true -> cubeSample G point child = false) :
    outsideBackgroundProductUnder w (frozenParentSignal background.signal (cubeEnvironment G point))
        (falseActionTarget q.action) (cubeSample G point) =
      weight (pairRootCount G.binary + S.count) S.count (backgroundCapacity w) (backgroundAmplitude w)
        (LinearSignal.rowPhase background) point := by
  unfold outsideBackgroundProductUnder weight
  apply FiniteProduct.iProduct_congr S.count
  intro child
  cases inside : w.small child with
  | true =>
      simp only [if_true, backgroundCapacity, backgroundAmplitude, inside, Bool.true_or,
        Int.zero_mul, Int.add_zero]
  | false =>
      cases forced : q.action child with
      | false =>
          simp only [Bool.false_eq_true, if_false, backgroundRowUnder, capacityRowUnder,
            falseActionTarget, forced, BooleanChannelTable.expansionCoefficientUnder,
            backgroundCapacity, backgroundAmplitude, inside, Bool.false_or, LinearSignal.rowPhase]
      | true =>
          simp only [Bool.false_eq_true, if_false, backgroundRowUnder, capacityRowUnder,
            falseActionTarget, forced, if_true, consistent child forced,
            BooleanChannelTable.expansionCoefficientUnder, backgroundCapacity, backgroundAmplitude,
            inside, Bool.false_or, Int.zero_mul, Int.add_zero]

/-- A supplied complete original event mask fixes the actual action rows
on its combined cube support, so the pointwise weight identity needs no
independent consistency premise at any listed point. -/
theorem outsideBackground_eq_weight_of_mem
    (w : HedgeWitness G q) (background : LinearSignal G) (nodes : NodeSet S) (point : Cube G)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union q.action nodes))) :
    outsideBackgroundProductUnder w (frozenParentSignal background.signal (cubeEnvironment G point))
        (falseActionTarget q.action) (cubeSample G point) =
      weight (pairRootCount G.binary + S.count) S.count (backgroundCapacity w) (backgroundAmplitude w)
        (LinearSignal.rowPhase background) point := by
  apply outsideBackground_eq_weight_of_consistent w background point
  intro child forced
  apply cubeSample_false_of_mem G (NodeSet.union q.action nodes) point listed child
  simp only [NodeSet.union, forced, Bool.true_or]

/-- Every complete installed background event sum is its actual positive
small-capacity scalar times the unit-character moment.  This is a semantic
identity with the old model mass, not a positivity hypothesis on a new weight. -/
theorem backgroundEventSum_eq_moment_of_action
    (w : HedgeWitness G q) (background : LinearSignal G) (nodes : NodeSet S) :
    backgroundEventSum w background.signal (falseActionTarget q.action) (FiniteProduct.falseCylinder S.count nodes) =
      (smallCapacityScalar w : Int) *
        moment (pairRootCount G.binary + S.count) S.count (cubeMask G (NodeSet.union q.action nodes))
          (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
          (HomogeneousPhase.unit (pairRootCount G.binary + S.count)) := by
  rw [backgroundEventSum_eq_scaled_cube_sum_of_action]
  unfold moment
  apply congrArg ((smallCapacityScalar w : Int) * ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro point listed
  rw [outsideBackground_eq_weight_of_mem w background nodes point listed]
  simp only [HomogeneousPhase.unit, FiniteProbRecord.characterSign, Bool.false_eq_true, if_false, Int.mul_one]

/-- Every complete installed interaction event sum is its actual positive
small-amplitude scalar times the full small-forest character moment.  The
same equality applies to conditioning events, whose character moment is not
discarded or assumed zero before normalized cells are cross-multiplied. -/
theorem interactionEventSum_eq_moment_of_action
    (w : HedgeWitness G q) (small background : LinearSignal G) (nodes : NodeSet S) :
    interactionEventSum w small.signal background.signal (falseActionTarget q.action)
        (FiniteProduct.falseCylinder S.count nodes) =
      (smallAmplitudeScalar w : Int) *
        moment (pairRootCount G.binary + S.count) S.count (cubeMask G (NodeSet.union q.action nodes))
          (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
          (LinearSignal.forestPhase small w.small) := by
  rw [interactionEventSum_eq_scaled_cube_sum_of_action]
  unfold moment
  apply congrArg ((smallAmplitudeScalar w : Int) * ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro point listed
  rw [outsideBackground_eq_weight_of_mem w background nodes point listed]
  exact Int.mul_comm _ _

/-! ## Full joint-event moments retain the unchanged conditioning cylinder -/

private theorem action_joint_mask (action outcome condition : NodeSet S) :
    cubeMask G (NodeSet.union action (NodeSet.union outcome condition)) =
      (fun index => cubeMask G (NodeSet.union action condition) index || cubeMask G outcome index) := by
  have reordered : NodeSet.union action (NodeSet.union outcome condition) =
      NodeSet.union (NodeSet.union action condition) outcome := by
    funext child
    unfold NodeSet.union
    cases action child <;> cases outcome child <;> cases condition child <;> rfl
  rw [reordered, cubeMask_union]

/-- The complete actual joint background mass is a full-outcome cylinder
moment on the original action-and-conditioning support.  All outcome
coordinates remain in its event filter, not just a path endpoint. -/
theorem backgroundJointSum_eq_cylinderMoment
    (w : HedgeWitness G q) (background : LinearSignal G) (outcome condition : NodeSet S) :
    backgroundEventSum w background.signal (falseActionTarget q.action)
        (FiniteProduct.falseCylinder S.count (NodeSet.union outcome condition)) =
      (smallCapacityScalar w : Int) *
        cylinderMoment (pairRootCount G.binary + S.count) S.count
          (cubeMask G (NodeSet.union q.action condition)) (cubeMask G outcome)
          (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
          (HomogeneousPhase.unit (pairRootCount G.binary + S.count)) := by
  rw [backgroundEventSum_eq_moment_of_action, cylinderMoment_eq_moment_union, action_joint_mask]

/-- The actual joint interaction has the same full-outcome event and the
same original conditioning support as the background.  It retains the
complete small-forest phase before either normalized cross-product is formed. -/
theorem interactionJointSum_eq_cylinderMoment
    (w : HedgeWitness G q) (small background : LinearSignal G) (outcome condition : NodeSet S) :
    interactionEventSum w small.signal background.signal (falseActionTarget q.action)
        (FiniteProduct.falseCylinder S.count (NodeSet.union outcome condition)) =
      (smallAmplitudeScalar w : Int) *
        cylinderMoment (pairRootCount G.binary + S.count) S.count
          (cubeMask G (NodeSet.union q.action condition)) (cubeMask G outcome)
          (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
          (LinearSignal.forestPhase small w.small) := by
  rw [interactionEventSum_eq_moment_of_action, cylinderMoment_eq_moment_union, action_joint_mask]

/-- The exact normalized joint/evidence response of the installed pair,
before its common positive main-prior scalar.  Both evidence and joint
interaction changes are retained; this is not their difference at one point. -/
def signedConditionalResponse (w : HedgeWitness G q) (small background : LinearSignal G)
    (outcome condition : NodeSet S) : Int :=
  interactionEventSum w small.signal background.signal (falseActionTarget q.action)
      (FiniteProduct.falseCylinder S.count (NodeSet.union outcome condition)) *
    backgroundEventSum w background.signal (falseActionTarget q.action) (FiniteProduct.falseCylinder S.count condition) -
  backgroundEventSum w background.signal (falseActionTarget q.action)
      (FiniteProduct.falseCylinder S.count (NodeSet.union outcome condition)) *
    interactionEventSum w small.signal background.signal (falseActionTarget q.action) (FiniteProduct.falseCylinder S.count condition)

/-- The actual normalized response is exactly the full-outcome covariance
times the two strictly positive installed small-row scalars.  This equality
connects the arithmetic inequality to the genuine model integrals; no equal
conditioning mass or abstract polynomial interpretation is assumed. -/
theorem signedConditionalResponse_eq_covariance
    (w : HedgeWitness G q) (small background : LinearSignal G) (outcome condition : NodeSet S) :
    signedConditionalResponse w small background outcome condition =
      ((smallAmplitudeScalar w : Int) * (smallCapacityScalar w : Int)) *
        cylinderCovarianceNumerator (pairRootCount G.binary + S.count) S.count
          (cubeMask G (NodeSet.union q.action condition)) (cubeMask G outcome)
          (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
          (LinearSignal.forestPhase small w.small) := by
  unfold signedConditionalResponse
  rw [interactionJointSum_eq_cylinderMoment, backgroundJointSum_eq_cylinderMoment,
    backgroundEventSum_eq_moment_of_action, interactionEventSum_eq_moment_of_action]
  unfold cylinderCovarianceNumerator
  rw [Int.mul_sub]
  congr 1 <;> ac_rfl

/-- A strictly positive complete covariance gives a strictly positive
actual normalized response.  Both scalar positivity proofs refer to the
installed small coefficients, so no probability denominator is guessed. -/
theorem signedConditionalResponse_positive_of_covariance
    (w : HedgeWitness G q) (small background : LinearSignal G) (outcome condition : NodeSet S)
    (positive : 0 < cylinderCovarianceNumerator (pairRootCount G.binary + S.count) S.count
      (cubeMask G (NodeSet.union q.action condition)) (cubeMask G outcome)
      (backgroundCapacity w) (backgroundAmplitude w) (LinearSignal.rowPhase background)
      (LinearSignal.forestPhase small w.small)) :
    0 < signedConditionalResponse w small background outcome condition := by
  have amplitudePositive : (0 : Int) < smallAmplitudeScalar w := by
    have := smallAmplitudeScalar_positive w
    omega
  have capacityPositive : (0 : Int) < smallCapacityScalar w := by
    have := smallCapacityScalar_positive w
    omega
  rw [signedConditionalResponse_eq_covariance]
  exact Int.mul_pos (Int.mul_pos amplitudePositive capacityPositive) positive

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
