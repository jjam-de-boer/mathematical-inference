import Thesis.CausalTransport.BoundedNativeClassification
import Thesis.Examples.BoundedNativeSearch

namespace Thesis.Causality.Examples.BoundedNativeClassification

open Probability BoundedNativeSearch
open Causality.BoundedNativeSearch

/-!
# Public bounded-class predicates on the native null-action regression

The two factual point-mass models give a genuine semantic separation witness
for the intervention target. The factual query is identified throughout the
whole bounded native class because every fitted model has the same observed
law. A zero denominator bound is incompatible, not vacuously point identified.
The public exact-check theorem relates these mathematical statements to the
actual solver output, without expanding a large structural catalogue.
-/

theorem entry_fits (respond : Bool) : Fits projection 2 1 1 observed (entry respond).model :=
  ⟨nodes_bounded respond, sources_bounded respond, denominator_bounded respond, observational_agreement respond⟩

theorem effect_separated : Separated projection 2 1 1 observed effect :=
  ⟨(entry false).model, (entry true).model, entry_fits false, entry_fits true, different_effects⟩

theorem effect_not_point_identified : ¬ PointIdentified projection 2 1 1 observed effect := by
  intro identified
  exact different_effects (identified.2 (entry false).model (entry true).model (entry_fits false) (entry_fits true))

theorem factual_point_identified : PointIdentified projection 2 1 1 observed factual := by
  refine ⟨⟨(entry false).model, entry_fits false⟩, ?_⟩
  intro left right leftFits rightFits
  exact QProb.equiv_trans (leftFits.2.2.2 outcome) (QProb.equiv_symm (rightFits.2.2.2 outcome))

theorem zero_bound_not_compatible : ¬ Compatible projection 2 1 0 observed := by
  rintro ⟨original, _, _, denominators, _⟩
  exact (Nat.not_le_of_lt (original.factor x).den_pos) (denominators x)

theorem zero_bound_not_point_identified : ¬ PointIdentified projection 2 1 0 observed effect :=
  fun identified => zero_bound_not_compatible identified.1

theorem solver_separation_check : (solve projection 2 1 1 observed effect).separatedCheck = true :=
  ((solve projection 2 1 1 observed effect).separatedCheck_exact).mpr effect_separated

theorem solver_identification_check : (solve projection 2 1 1 observed factual).pointIdentifiedCheck = true :=
  ((solve projection 2 1 1 observed factual).pointIdentifiedCheck_exact).mpr factual_point_identified

theorem solver_compatibility_check : (solve projection 2 1 1 observed effect).compatibleCheck = true :=
  ((solve projection 2 1 1 observed effect).compatibleCheck_exact).mpr ⟨(entry false).model, entry_fits false⟩

end Thesis.Causality.Examples.BoundedNativeClassification
