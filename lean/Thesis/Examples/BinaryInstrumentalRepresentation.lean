import Thesis.CausalTransport.BinaryInstrumentalEffect

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalRepresentation

open Probability BinaryInstrumental

/-!
# Native IV regressions: null instruments, unrestricted response maps and ATE

The original graph is the actual hidden DAG `U -> X,Y`, `Z -> X -> Y`.
Its projection is computed, rather than supplied as an external equivalence
interface.  All native realizations below therefore live on that original
graph and use the universal feasible-set transfer theorems.

A law with `X=false,Y=false` throughout leaves the other treatment risk
free: two feasible response records realize zero and one with the same
whole observed law.  This is checked both for a fair instrument and for an
instrument whose true value has probability zero.  The latter case must not
be replaced by an arbitrarily specified conditional at that null value.

A decreasing treatment map is also admitted.  Its outcome response has a
signed effect of minus one, represented by affine score zero.  This catches
both accidental monotonicity assumptions and truncated natural subtraction.
Small closed record calculations are reduced by the kernel; whole native
model claims come from the proved symbolic transport, not native reduction.
-/

def fullGraph : FiniteHiddenDAG signature where
  count := 4
  observedNode := fun node => ⟨node.val + 1, Nat.succ_lt_succ node.isLt⟩
  observedNode_injective := by
    intro first second same
    exact Fin.ext (Nat.succ.inj (congrArg Fin.val same))
  hidden := fun node => decide (node.val = 0)
  observed_not_hidden := by decide +kernel
  node_classified := by decide +kernel
  edge := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 2) ∨ (parent.val = 0 ∧ child.val = 3) ∨
      (parent.val = 1 ∧ child.val = 2) ∨ (parent.val = 2 ∧ child.val = 3))
  rank := Fin.val
  edge_rank_lt := by decide +kernel

private theorem directed_search_matches : forall first second : Fin signature.count,
    signature.directed first second =
      (fullGraph.hiddenInternalPath? (fullGraph.observedNode first) (fullGraph.observedNode second)).isSome := by
  decide +kernel

private theorem directed_matches : fullGraph.DirectedProjectionMatches := by
  intro first second
  change signature.directed first second = true ↔
    fullGraph.HiddenInternalPath (fullGraph.observedNode first) (fullGraph.observedNode second)
  rw [directed_search_matches first second]
  exact fullGraph.hiddenInternalPath?_iff _ _

def projection : FiniteLatentProjection signature := fullGraph.computedLatentProjection directed_matches

theorem projected_iv_graph : HasIVProjection projection := by decide +kernel

def fairInstrument : FiniteProbRecord Bool := ⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩
def nullInstrument : FiniteProbRecord Bool := ⟨[(false, 1), (true, 0)], 1, by decide, rfl⟩

def fixedTreatment (otherOutcome : Bool) : Profile :=
  fun bit => if bit.val = 3 then otherOutcome else false

def singletonResponse (profile : Profile) : FiniteProbRecord Profile :=
  ⟨[(profile, 1)], 1, by decide, rfl⟩

def constantLaw (instrument : FiniteProbRecord Bool) : FiniteProbRecord signature.Assignment :=
  observedRecord instrument (singletonResponse (fixedTreatment false))

theorem fair_constant_feasible (otherOutcome : Bool) :
    FeasibleResponses (constantLaw fairInstrument) (singletonResponse (fixedTreatment otherOutcome)) := by
  cases otherOutcome <;> decide +kernel

theorem null_constant_feasible (otherOutcome : Bool) :
    FeasibleResponses (constantLaw nullInstrument) (singletonResponse (fixedTreatment otherOutcome)) := by
  cases otherOutcome <;> decide +kernel

def constantRisks (otherOutcome : Bool) : Bool → QProb :=
  fun action => if action && otherOutcome then QProb.one else QProb.zero

/-- The two arm probabilities are attained simultaneously by one native
model, while every observed event has exactly the supplied constant law. -/
theorem fair_native_risks (otherOutcome : Bool) :
    RisksAttainableAt projection (constantLaw fairInstrument) (constantRisks otherOutcome) := by
  apply (risksAttainableAt_iff projection projected_iv_graph _ _).mpr
  refine ⟨singletonResponse (fixedTreatment otherOutcome), fair_constant_feasible otherOutcome, ?_⟩
  cases otherOutcome <;> decide +kernel

theorem null_native_risks (otherOutcome : Bool) :
    RisksAttainableAt projection (constantLaw nullInstrument) (constantRisks otherOutcome) := by
  apply (risksAttainableAt_iff projection projected_iv_graph _ _).mpr
  refine ⟨singletonResponse (fixedTreatment otherOutcome), null_constant_feasible otherOutcome, ?_⟩
  cases otherOutcome <;> decide +kernel

def constantScore (otherOutcome : Bool) : QProb :=
  if otherOutcome then QProb.one else effectHalf

/-- These score endpoints encode actual ATE values zero and one.  They
are actual native witnesses, not a claim that a general optimizer is finished. -/
theorem null_native_effect_scores (otherOutcome : Bool) :
    EffectScoreAttainableAt projection (constantLaw nullInstrument) (constantScore otherOutcome) := by
  apply (effectScoreAttainableAt_iff projection projected_iv_graph _ _).mpr
  refine ⟨singletonResponse (fixedTreatment otherOutcome), null_constant_feasible otherOutcome, ?_⟩
  cases otherOutcome <;> decide +kernel

def decreasingProfile : Profile := fun bit => decide (bit.val = 0 ∨ bit.val = 2)
def decreasingResponses : FiniteProbRecord Profile := singletonResponse decreasingProfile
def decreasingLaw : FiniteProbRecord signature.Assignment := observedRecord fairInstrument decreasingResponses

theorem decreasing_feasible : FeasibleResponses decreasingLaw decreasingResponses := by decide +kernel

/-- `Y(1)=false,Y(0)=true` has ATE minus one, not a naturally truncated zero.
The displayed exact signed numerator uses the original normalized record. -/
theorem decreasing_signed_effect : decreasingResponses.signedMass effectChange = -1 := by decide +kernel

theorem decreasing_native_effect : EffectScoreAttainableAt projection decreasingLaw QProb.zero := by
  apply (effectScoreAttainableAt_iff projection projected_iv_graph _ _).mpr
  exact ⟨decreasingResponses, decreasing_feasible, by decide +kernel⟩

end BinaryInstrumentalRepresentation
end Examples
end Causality
end Thesis
