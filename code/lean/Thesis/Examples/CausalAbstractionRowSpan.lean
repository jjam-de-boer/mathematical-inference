import Thesis.CausalTransport.CausalAbstractionRowSpan
import Thesis.Examples.CausalAbstractionInverse

/-! # Uniform identification and a particular boundary dataset -/

namespace Thesis.Examples.CausalAbstractionRowSpan

open Probability Probability.Distros RationalLinear
open Causality Causality.CausalAbstractionInverse
open Thesis.Examples.CausalAbstractionInverse
open Thesis.Examples.CausalAbstractionSynthesis (compactSignature compactDoTrue)

private def first (state : fine.Assignment) : Bool := state (0 : Fin 2)

def firstQuery : EventQuery fine := .intervention (.empty fine) first

private def pointOn (state : fine.Assignment) :
    Fin spec.problem.cells.length → SignedRatio := fun i =>
  if SharedResponse.eval fine (HardIntervention.empty fine).value (spec.problem.cells.get i) = state then
    SignedRatio.one
  else SignedRatio.zero

private def allFalse := pointOn (fun _ => false)
private def firstOnly := pointOn (fun node => node.val == 0)

/-- The two point laws give the same measured AND values but disagree about
the first parent. This excludes the query row from the rational span. -/
theorem first_not_in_uniform_span : ¬ RationalSpan spec.measurementRows (spec.queryRow firstQuery) := by
  intro spanned
  have answered := (spec.uniform_fine_query_iff firstQuery).mpr spanned
    allFalse firstOnly (by unfold Simplex; decide +kernel)
      (by unfold Simplex; decide +kernel) (by decide +kernel)
  exact (by decide +kernel :
    ¬ SignedRatio.Equiv (dot _ (spec.queryRow firstQuery) allFalse)
      (dot _ (spec.queryRow firstQuery) firstOnly)) answered

def positiveBoundary : Specification fine compactSignature :=
  { spec with
    measurements := [⟨.empty compactSignature, deterministic true⟩,
      ⟨compactDoTrue, deterministic true⟩] }

private def coarseTrue (state : compactSignature.Assignment) : Bool := state ⟨0, by decide⟩

/-- If the retained AND is always true, the first parent is always true.
The original measurement rows are unchanged. It is the measured value
that puts the fitted model on a face where the extra query is identified. -/
theorem first_identified_on_boundary (model : ExactModel fine) (fits : positiveBoundary.Fits model) :
    QProb.Equiv (firstQuery.value model) QProb.one := by
  let measurement : Measurement compactSignature := ⟨.empty compactSignature, deterministic true⟩
  have listed : (.empty fine, measurement) ∈ positiveBoundary.comparisons :=
    (positiveBoundary.comparison_iff _ _).mpr ⟨List.mem_cons_self .., by decide +kernel⟩
  have observed := fits (.empty fine, measurement) listed coarseTrue
  let law := model.interventionalDist (HardIntervention.empty fine).value
  have bothOne : QProb.Equiv (law.probVal bothTrue) QProb.one := observed
  have increases : QProb.LE (law.probVal bothTrue) (law.probVal first) := by
    apply Nat.mul_le_mul_right _
    apply FiniteProbRecord.eventMass_mono
    intro state selected
    exact (Bool.and_eq_true_iff.mp selected).1
  exact Nat.le_antisymm (law.probVal_le_one first)
    (QProb.le_congr bothOne (QProb.equiv_refl _) increases)

end Thesis.Examples.CausalAbstractionRowSpan
