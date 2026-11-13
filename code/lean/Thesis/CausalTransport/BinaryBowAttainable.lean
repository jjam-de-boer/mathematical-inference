import Thesis.CausalTransport.BinaryBowBounds
import Thesis.Causality.BinaryBowMixture
import Thesis.Probability.AffineInterval

namespace Thesis
namespace Causality
namespace BinaryBow

open Probability

/-!
# Every rational point in the native bow interval is attainable

At positive other-action mass, compute the exact rational switch needed for
the requested value.  The endpoint inequalities bound that switch by one,
and the existing Bernoulli record realizes it.  The actual shared-root SCM
is then realized on the original hidden DAG, preserving the whole observed
law and the requested intervention probability by proved model theorems.

At zero other-action mass there is no switch denominator.  Both endpoints
already agree, the two interval inequalities force the requested fraction
to agree with them, and the ordinary lower model realizes it.  This explicit
branch is essential: dividing zero by zero is neither necessary nor valid.

The final iff characterizes the entire rational attainable set of the full
native model class, not merely a convex relaxation or a selected subfamily.
It supplements the independently proved fixed-law identification theorem.
-/

theorem mixture_compatible_projection (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) :
    Compatible (mixtureModel law switch) projection.observedGraph :=
  ⟨mixture_isCanonical law switch, fun first second =>
    (mixture_hasProjectedGraph law switch first second).trans
      ((projectedGraph_eq_bow projection present first second).symm)⟩

/-- The mixture is placed on the same original hidden graph as the bounds'
full model family, without merging that graph's independent latent sources. -/
def nativeMixture (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) :
    FiniteHiddenDAGSCM signature projection :=
  (mixtureModel law switch).toHiddenDAGSCM (mixture_compatible_projection projection present law switch)

theorem nativeMixture_hasObservedLaw (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) :
    HasObservedLaw (nativeMixture projection present law switch) law := by
  intro event
  exact QProb.equiv_trans
    ((mixtureModel law switch).toHiddenDAGSCM_observationalValue
      (mixture_compatible_projection projection present law switch) event)
    (mixture_observationalValue_preserved law switch event)

theorem nativeMixture_interventionalValue (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) (action : Bool) :
    QProb.Equiv
      ((nativeMixture projection present law switch).interventionalValue
        (intervention action) (fun sample => sample y))
      (QProb.add (lower law action) (QProb.mul (outside law action) (switch.probVal id))) :=
  QProb.equiv_trans
    ((mixtureModel law switch).toHiddenDAGSCM_interventionalValue
      (mixture_compatible_projection projection present law switch) (intervention action) _)
    (mixture_interventionalValue law switch action)

/-- The common denominator of the two observational endpoint pieces
provides the exact simple-denominator upper fraction used by interpolation. -/
private theorem upper_common_denominator (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    QProb.Equiv (upper law action)
      ⟨(lower law action).num + (outside law action).num, law.den, law.den_pos⟩ :=
  QProb.add_mk_same_den law.den law.den_pos (lower law action).num (outside law action).num

/-- A supplied rational point inside a positive-gap interval gives an actual
native model.  The switch is explicitly computed, not extracted by choice. -/
theorem attainable_of_positive_gap (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) (value : QProb)
    (positive : 0 < (outside law action).num)
    (lowerBound : QProb.LE (lower law action) value) (upperBound : QProb.LE value (upper law action)) :
    AttainableAt projection law action value := by
  let chance := QProb.intervalChance law.den law.den_pos (lower law action).num
    (outside law action).num positive value
  have simpleUpper := QProb.le_congr (QProb.equiv_refl value) (upper_common_denominator law action) upperBound
  have bounded : QProb.LE chance QProb.one :=
    QProb.intervalChance_le_one law.den law.den_pos (lower law action).num
      (outside law action).num positive value simpleUpper
  let switch := QProb.bernoulliRecord chance bounded
  let native := nativeMixture projection present law switch
  refine ⟨native, nativeMixture_hasObservedLaw projection present law switch, ?_⟩
  exact QProb.equiv_trans (nativeMixture_interventionalValue projection present law switch action)
    (QProb.equiv_trans
      (QProb.add_congr (QProb.equiv_refl _)
        (QProb.mul_congr (QProb.equiv_refl _) (QProb.bernoulliRecord_probVal chance bounded)))
      (QProb.intervalChance_reconstruct law.den law.den_pos (lower law action).num
        (outside law action).num positive value lowerBound))

/-- Exact rational attainable-set classification, including degenerate
intervals and zero-containing observed distributions.  The forward direction
uses universal native bounds; the reverse constructs a model on this DAG. -/
theorem attainable_iff_bounds (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) (value : QProb) :
    AttainableAt projection law action value ↔
      QProb.LE (lower law action) value ∧ QProb.LE value (upper law action) := by
  constructor
  · exact (sharp_bounds projection present law action).1 value
  · rintro ⟨lowerBound, upperBound⟩
    rcases Nat.eq_zero_or_pos (outside law action).num with zero | positive
    · have outsideZero : QProb.Equiv (outside law action) QProb.zero := by
        simp only [QProb.Equiv, QProb.zero, zero, Nat.zero_mul, Nat.mul_zero]
      have endpoints : QProb.Equiv (upper law action) (lower law action) :=
        QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) outsideZero) (QProb.add_zero _)
      have reverse := QProb.le_congr (QProb.equiv_refl value) endpoints upperBound
      have equal := QProb.equiv_of_le_of_le lowerBound reverse
      exact ⟨endpointModel projection present law false,
        endpointModel_hasObservedLaw projection present law false,
        QProb.equiv_trans (native_lower_endpoint projection present law action) equal⟩
    · exact attainable_of_positive_gap projection present law action value positive lowerBound upperBound

end BinaryBow
end Causality
end Thesis
