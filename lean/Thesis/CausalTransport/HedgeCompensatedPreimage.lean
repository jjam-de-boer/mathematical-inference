import Thesis.CausalTransport.HedgeCompensatedReadout
import Thesis.CausalTransport.HedgeInterventionalMarginal

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Full-value local preimages in the actual compensated carrier pair

Protected-mechanism closure proves denominator equality only off the installed
mask.  A denominator inspecting installed rows needs a different argument:
at fixed fresh inputs, pull its full-value cylinder back to partial incidence
equations and a common private-background predicate, then compare the old
weighted fibres and integrate all actual fresh factors.

This module supplies the exact local preimages for installed forest rows.
The source-bit equations differ between ordinary and nested incidence; the
background predicate does not.  Both equations are proved for the mechanisms
of the actual folded SCMs at arbitrary current parents, not for a substitute
signal distribution or only for factual observations.

The background constraint is deliberately retained.  A readout which flips
an old `second` value to bit zero emits `first`, even if the original private
background was a third label.  Testing only the recovered incidence bit
would incorrectly admit that third-label cylinder.

These local equivalences do not yet establish a marginal comparison.  The
global pullback must also check intervention consistency, all other free
rows, and whether a proposed omitted balancing coordinate is read by any
remaining equation.  `HedgeReadoutNoise` supplies the fixed-slice integration
boundary once those full events have been compared.  The companion
`HedgeCompensatedMarginal` now proves this global comparison for cylinders
omitting a common root unused by the composed flow; no such global marginal
equality is assumed by the local equivalences here.
-/

namespace HedgeCompensatedPreimage

variable {G : ObservedGraph S} {q : JointKernelQuery S}

private theorem listed (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (child : Fin S.count)
    (selected : w.smallOutcomeFlowNodes child = true) :
    w.carrierFlowReadoutStep rich noise child ∈ w.carrierFlowReadoutPlan rich noise :=
  List.mem_map.mpr ⟨child, (NodeSet.mem_members_iff w.smallOutcomeFlowNodes child).mpr selected, rfl⟩

end HedgeCompensatedPreimage

/-- An installed large-carrier forest row realizes a full target value
exactly when its old incidence/parent/defect bit equals the inverse readout
bit and its original private background passes the common full-label test.

The fresh bit belongs to the actual encoded augmented unit.  No noise bias,
support, route-permission, or agreement of factual and current parents is
assumed at this local boundary. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_mechanism_preimage_of_large
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (inside : w.large child = true)
    (parents : S.ParentValues child) (target : S.Value child) :
    decide (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).mechanism
        child parents (fun root _incident => (w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit root) = target) =
      (decide (Bool.xor
        (Bool.xor
          (hedgeXorPairBitsWithinFrom G w.large child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)))
          (hedgeForestParentBitsFrom rich w.child child parents))
        (if child = w.actionRoot then hedgeDefectBitOf G unit else false) =
          hedgeReadoutRequiredCarrierBit rich child (w.carrierFlowReadoutStep rich noise child).parentSignal
            parents (bits child) target) &&
        hedgeReadoutCarrierBackgroundFits rich child (w.carrierFlowReadoutStep rich noise child).parentSignal
          parents (bits child) target
          (hedgePrivateDecode S child (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit) child))) := by
  have mechanism := FiniteLatentSCM.withHedgeReadouts_mechanism_of_mem (w.largeCarrierDefectParityModel rich) rich
    (w.carrierFlowReadoutPlan rich noise) (w.carrierFlowReadoutPlan_pivots_distinct rich noise)
    (w.carrierFlowReadoutStep rich noise child) (HedgeCompensatedPreimage.listed w rich noise child selected)
    bits unit parents
  dsimp only [HedgeWitness.carrierFlowReadoutStep] at mechanism
  rw [mechanism, w.largeCarrierDefectParityModel_mechanism_incidence rich child parents unit]
  simp only [HedgeWitness.carrierFlowReadoutStep, inside, if_true]
  exact hedgeNoisyReadout_carrier_preimage rich child
    (fun current => Bool.xor (hedgeForestParentBitsFrom rich w.child child current)
      (hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child current)) parents _ (bits child) _ target

/-- The nested installed forest row has the same full-label predicate as
the large row, but its own nested incidence and row-specific kept map.
Only the source-bit equation changes.  This exact separation is what permits
a weighted partial-incidence comparison to retain arbitrary observed labels.

Outer-only rows use the original kept map; small rows use its restriction.
This theorem does not assume that rerouting an outer-only row preserves the
complete observational law: that is a separate global obligation. -/
theorem HedgeWitness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_mechanism_preimage_of_large
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (bits : Fin S.count -> Bool) (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (inside : w.large child = true)
    (parents : S.ParentValues child) (target : S.Value child) :
    decide (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).mechanism
        child parents (fun root _incident => (w.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit root) = target) =
      (decide (Bool.xor
        (Bool.xor
          (hedgeNestedXorPairBitsWithinFrom G w.large w.small child (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)))
          (hedgeForestParentBitsFrom rich
            (if w.small child then restrictChild w.small w.child else w.child) child parents))
        (if child = w.actionRoot then hedgeDefectBitOf G unit else false) =
          hedgeReadoutRequiredCarrierBit rich child (w.carrierFlowReadoutStep rich noise child).parentSignal
            parents (bits child) target) &&
        hedgeReadoutCarrierBackgroundFits rich child (w.carrierFlowReadoutStep rich noise child).parentSignal
          parents (bits child) target
          (hedgePrivateDecode S child (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit) child))) := by
  have mechanism := FiniteLatentSCM.withHedgeReadouts_mechanism_of_mem (w.smallCarrierDefectParityModel rich) rich
    (w.carrierFlowReadoutPlan rich noise) (w.carrierFlowReadoutPlan_pivots_distinct rich noise)
    (w.carrierFlowReadoutStep rich noise child) (HedgeCompensatedPreimage.listed w rich noise child selected)
    bits unit parents
  dsimp only [HedgeWitness.carrierFlowReadoutStep] at mechanism
  rw [mechanism, w.smallCarrierDefectParityModel_mechanism_incidence rich child parents unit]
  simp only [HedgeWitness.carrierFlowReadoutStep, inside, if_true]
  exact hedgeNoisyReadout_carrier_preimage rich child
    (fun current => Bool.xor (hedgeForestParentBitsFrom rich w.child child current)
      (hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child current)) parents _ (bits child) _ target

end Causality
end Thesis
