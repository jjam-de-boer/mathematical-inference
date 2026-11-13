import Thesis.CausalTransport.BinaryInstrumental.Transportation
import Thesis.CausalTransport.BinaryInstrumental.Effect
import Thesis.Examples.BinaryInstrumental.Representation

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalTransportation

open Probability BinaryInstrumental
open FourLabelTransportation

/-!
# Native IV witnesses from a jointly optimized transportation table

The whole observed law is uniform on the eight Boolean `Z,X,Y` assignments.
Each instrument-arm treatment/outcome category has probability one quarter.
The common-total transportation table is constructed by the proved joint
optimizer, not supplied as a semantic model or a list of desired risk values.

Two explicit fill rules choose the previously unobserved outcome response
in opposite directions.  Each yields a genuine model on the actual hidden
DAG already computed in `BinaryInstrumental.Representation`.  The lower
signed-effect witness has risks `3/4` under control and `1/4` under treatment;
the upper witness has the opposite pair.  Their ATE values are `-1/2` and
`1/2`, encoded by scores `1/4` and `3/4` without truncated subtraction.

These tests certify whole-law agreement and simultaneous native attainments.
They do not replace the still-needed universal bound theorem for arbitrary
response denominators, or claim a complete arbitrary-observed-law optimizer.
Only the eight-cell observed record and sixteen-cell response data are reduced
by the kernel; the expanded native SCM is handled by symbolic preservation.
-/

def uniformLaw : FiniteProbRecord signature.Assignment where
  atoms := signature.assignmentEnumeration.map (fun sample => (sample, 1))
  den := 8
  den_pos := by decide
  total_mass := by decide +kernel

def units : Masses := fun _ => 1

theorem unit_margins : Margins 4 units units := by
  refine ⟨rfl, rfl, ?_⟩
  intro _
  change 1 + 1 ≤ 4
  decide +kernel

theorem uniform_arm_marginals : ArmMarginals uniformLaw 4 (by decide) units units := by
  constructor <;> decide +kernel

def first : Fin 4 × Fin 4 := (0, 1)
def second : Fin 4 × Fin 4 := (3, 2)
theorem first_different : first.1 ≠ first.2 := by decide +kernel
theorem second_different : second.1 ≠ second.2 := by decide +kernel

theorem complementary : ComplementaryEdges first second := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

def jointTable : Transportation units units :=
  maximizeComplementary 4 units units unit_margins first second first_different second_different complementary

/-- If the factual treatment is false, choose its missing treated response
false; if true, choose its missing control response true.  Opposite treatment
arms already determine both responses, so this fill is irrelevant there. -/
def lowerFill (pair : ResponsePair) : Bool := pair.1.1
def upperFill (pair : ResponsePair) : Bool := !pair.1.1

def lowerResponses : FiniteProbRecord Profile := transportationResponses 4 (by decide) units units unit_margins jointTable lowerFill
def upperResponses : FiniteProbRecord Profile := transportationResponses 4 (by decide) units units unit_margins jointTable upperFill

theorem lower_feasible : FeasibleResponses uniformLaw lowerResponses :=
  transportationResponses_feasible uniformLaw 4 (by decide) units units unit_margins uniform_arm_marginals jointTable lowerFill

theorem upper_feasible : FeasibleResponses uniformLaw upperResponses :=
  transportationResponses_feasible uniformLaw 4 (by decide) units units unit_margins uniform_arm_marginals jointTable upperFill

def quarter : QProb := ⟨1, 4, by decide⟩
def threeQuarters : QProb := ⟨3, 4, by decide⟩
def lowerRisks (action : Bool) : QProb := if action then quarter else threeQuarters
def upperRisks (action : Bool) : QProb := if action then threeQuarters else quarter

/-- A single original-DAG SCM has both lower-effect risks at once and
agrees on every observed event with the supplied uniform law. -/
theorem lower_native_risks : RisksAttainableAt BinaryInstrumentalRepresentation.projection uniformLaw lowerRisks := by
  apply (risksAttainableAt_iff BinaryInstrumentalRepresentation.projection
    BinaryInstrumentalRepresentation.projected_iv_graph uniformLaw lowerRisks).mpr
  refine ⟨lowerResponses, lower_feasible, ?_⟩
  intro action
  cases action <;> decide +kernel

theorem upper_native_risks : RisksAttainableAt BinaryInstrumentalRepresentation.projection uniformLaw upperRisks := by
  apply (risksAttainableAt_iff BinaryInstrumentalRepresentation.projection
    BinaryInstrumentalRepresentation.projected_iv_graph uniformLaw upperRisks).mpr
  refine ⟨upperResponses, upper_feasible, ?_⟩
  intro action
  cases action <;> decide +kernel

/-- The original response records have denominator four.  Thus these
signed integer numerators really mean ATE minus one half and plus one half. -/
theorem signed_numerators : lowerResponses.signedMass effectChange = -2 ∧ upperResponses.signedMass effectChange = 2 := by
  decide +kernel

theorem lower_native_effect : EffectScoreAttainableAt BinaryInstrumentalRepresentation.projection uniformLaw quarter := by
  apply (effectScoreAttainableAt_iff BinaryInstrumentalRepresentation.projection
    BinaryInstrumentalRepresentation.projected_iv_graph uniformLaw quarter).mpr
  exact ⟨lowerResponses, lower_feasible, by decide +kernel⟩

theorem upper_native_effect : EffectScoreAttainableAt BinaryInstrumentalRepresentation.projection uniformLaw threeQuarters := by
  apply (effectScoreAttainableAt_iff BinaryInstrumentalRepresentation.projection
    BinaryInstrumentalRepresentation.projected_iv_graph uniformLaw threeQuarters).mpr
  exact ⟨upperResponses, upper_feasible, by decide +kernel⟩

end BinaryInstrumentalTransportation
end Examples
end Causality
end Thesis
