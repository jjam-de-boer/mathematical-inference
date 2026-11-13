import Thesis.Causality.BinaryBowEndpoints
import Thesis.CausalTransport.HiddenDAGConsistencyBounds
import Thesis.CausalTransport.HiddenDAGProbability
import Thesis.CausalTransport.HiddenDAGAlmostSureIntervention

namespace Thesis
namespace Causality
namespace BinaryBow

open Probability

/-!
# Native sharp bow bounds and complete fixed-observed-law identification

The original hidden DAG is arbitrary, with the two Boolean observed nodes
and their fixed arrow `X -> Y`.  Its actual projection must contain `X <-> Y`.
Hidden and private-noise domains have no cardinality restriction.  Universal
bounds apply to every native SCM; the internally proved canonical realization
places the explicit endpoint models on that very same original hidden DAG.
There is no selected-family assumption or external model-class interface.

Every finite rational observational law is realized by both endpoint models.
Consequently a fixed law cannot identify the effect merely because that law
is incompatible with all models.  Identification quantifies over the entire
native family with that whole law.  It holds exactly when the requested
action already has probability one; otherwise actual native endpoints differ.

The sharpness theorem proves universal containment and attainment of both
ends.  The stronger claim that every rational point between the endpoints is
attainable is intentionally a separate mixture-construction obligation.
-/

variable {P : FiniteLatentProjection signature}

/-- With only two observed nodes, one bidirected edge fixes the whole
projected bidirected graph.  Its symmetry and irreflexivity are actual
graph fields; no latent-projection equivalence theorem is assumed. -/
theorem projectedGraph_eq_bow (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true) :
    forall first second, projection.observedGraph.bidirected first second = graph.bidirected first second := by
  intro first second
  rcases node_cases first with same | same <;> subst first
  · rcases node_cases second with same | same <;> subst second
    · simpa only [graph, natBeq_refl, Bool.not_true] using projection.observedGraph.bidirected_irreflexive x
    · simpa [graph, x, y] using present
  · rcases node_cases second with same | same <;> subst second
    · simpa [graph, x, y] using projection.observedGraph.bidirected_symmetric present
    · simpa only [graph, natBeq_refl, Bool.not_true] using projection.observedGraph.bidirected_irreflexive y

/-- Endpoint incidence is compatible with the original DAG's actual
projection.  This is established from the explicit single edge, not supplied
as an additional readiness condition on the countermodel construction. -/
theorem model_compatible_projection (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (offFactual : Bool) :
    Compatible (model law offFactual) projection.observedGraph :=
  ⟨model_isCanonical law offFactual, fun first second =>
    (model_hasProjectedGraph law offFactual first second).trans
      ((projectedGraph_eq_bow projection present first second).symm)⟩

/-- An actual SCM on the original hidden DAG, with a constructed product
prior and arbitrary finite relay alphabets.  Probability preservation is the
proved native realization theorem, not a field supplied by this constructor. -/
def endpointModel (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (offFactual : Bool) :
    FiniteHiddenDAGSCM signature projection :=
  (model law offFactual).toHiddenDAGSCM (model_compatible_projection projection present law offFactual)

/-- Equality to a fixed *whole* observed law.  Marginal agreement alone
would not justify the fixed-distribution classification or its bounds. -/
def HasObservedLaw (native : FiniteHiddenDAGSCM signature P)
    (law : FiniteProbRecord signature.Assignment) : Prop :=
  forall event, QProb.Equiv (native.observationalValue event) (law.probVal event)

theorem endpointModel_hasObservedLaw (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (offFactual : Bool) :
    HasObservedLaw (endpointModel projection present law offFactual) law := by
  intro event
  exact QProb.equiv_trans
    ((model law offFactual).toHiddenDAGSCM_observationalValue
      (model_compatible_projection projection present law offFactual) event)
    (observationalValue_preserved law offFactual event)

theorem native_lower_endpoint (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    QProb.Equiv
      ((endpointModel projection present law false).interventionalValue
        (intervention action) (fun sample => sample y)) (lower law action) :=
  QProb.equiv_trans
    ((model law false).toHiddenDAGSCM_interventionalValue
      (model_compatible_projection projection present law false) (intervention action) _)
    (lower_endpoint law action)

theorem native_upper_endpoint (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    QProb.Equiv
      ((endpointModel projection present law true).interventionalValue
        (intervention action) (fun sample => sample y)) (upper law action) :=
  QProb.equiv_trans
    ((model law true).toHiddenDAGSCM_interventionalValue
      (model_compatible_projection projection present law true) (intervention action) _)
    (upper_endpoint law action)

/-! ## Universal bounds and attained endpoints in the full native class -/

private def queryKernel : Kernel signature :=
  ⟨NodeSet.singleton y, NodeSet.singleton x, NodeSet.empty⟩

private def reference (action : Bool) : signature.Assignment := fun _ => action

private theorem queryKernel_hasAction : queryKernel.hasAction = true := rfl

private theorem queryKernel_actionCylinder (action : Bool) :
    Kernel.agreesOn queryKernel.action (reference action) = actionEvent action := by
  funext sample
  exact Kernel.agreesOn_singleton x (reference action) sample

private theorem queryKernel_intervention (action : Bool) :
    queryKernel.intervention (reference action) = (intervention action).value := by
  funext node
  rcases node_cases node with same | same <;> subst node <;> rfl

private theorem queryKernel_distribution (native : FiniteHiddenDAGSCM signature P) (action : Bool) :
    native.kernelDistribution queryKernel (reference action) = native.interventionalDist (intervention action) := by
  simp only [FiniteHiddenDAGSCM.kernelDistribution, queryKernel_hasAction, if_true,
    queryKernel_intervention]

/-- Every native model with this whole law lies within the displayed
interval.  Its hidden structure can be noncanonical and its observed law can
contain zeros; native consistency, not model replacement, proves the bound. -/
theorem native_bounds (native : FiniteHiddenDAGSCM signature P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law) (action : Bool) :
    QProb.LE (lower law action) (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y)) (upper law action) := by
  have bounds := native.kernelDistribution_consistency_bounds queryKernel (reference action) (fun sample => sample y)
  have raw : QProb.LE (native.observationalValue (lowerEvent action))
        (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y))
        (QProb.add (native.observationalValue (lowerEvent action))
          (native.observationalValue (outsideEvent action))) := by
    simpa only [queryKernel_distribution, queryKernel_actionCylinder,
      FiniteHiddenDAGSCM.interventionalValue, FiniteHiddenDAGSCM.observationalValue,
      lowerEvent, outsideEvent] using bounds
  exact ⟨QProb.le_congr (observed (lowerEvent action)) (QProb.equiv_refl _) raw.1,
    QProb.le_congr (QProb.equiv_refl _)
      (QProb.add_congr (observed (lowerEvent action)) (observed (outsideEvent action))) raw.2⟩

/-- An attainable value needs an actual finite native model with the fixed
whole law.  It is not just a feasible relaxation or a formally named bound. -/
def AttainableAt (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) (value : QProb) : Prop :=
  ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law ∧
    QProb.Equiv (native.interventionalValue (intervention action) (fun sample => sample y)) value

/-- Sharp bounds in the full native class: every attainable value is inside
the interval and both endpoints are themselves attained on the original DAG. -/
theorem sharp_bounds (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    (forall value, AttainableAt projection law action value →
      QProb.LE (lower law action) value ∧ QProb.LE value (upper law action)) ∧
      AttainableAt projection law action (lower law action) ∧
      AttainableAt projection law action (upper law action) := by
  constructor
  · rintro value ⟨native, observed, attained⟩
    have bounds := native_bounds native law observed action
    exact ⟨QProb.le_congr (QProb.equiv_refl _) attained bounds.1,
      QProb.le_congr attained (QProb.equiv_refl _) bounds.2⟩
  · exact ⟨⟨endpointModel projection present law false,
        endpointModel_hasObservedLaw projection present law false, native_lower_endpoint projection present law action⟩,
      ⟨endpointModel projection present law true,
        endpointModel_hasObservedLaw projection present law true, native_upper_endpoint projection present law action⟩⟩

/-! ## Complete fixed-law classification -/

/-- Fixed-law identification quantifies over every original-DAG finite SCM
with that law, not just over the two models used to prove sharpness. -/
def IdentifiedAt (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) : Prop :=
  forall left right : FiniteHiddenDAGSCM signature projection,
    HasObservedLaw left law → HasObservedLaw right law →
      QProb.Equiv (left.interventionalValue (intervention action) (fun sample => sample y))
        (right.interventionalValue (intervention action) (fun sample => sample y))

private theorem native_effect_eq_observed_of_action_one
    (native : FiniteHiddenDAGSCM signature P) (law : FiniteProbRecord signature.Assignment)
    (observed : HasObservedLaw native law) (action : Bool)
    (full : QProb.Equiv (law.probVal (actionEvent action)) QProb.one) :
    QProb.Equiv (native.interventionalValue (intervention action) (fun sample => sample y))
      (law.probVal (fun sample => sample y)) := by
  have factual : QProb.Equiv
      (native.observationalDist.probVal (Kernel.agreesOn queryKernel.action (reference action))) QProb.one := by
    rw [queryKernel_actionCylinder]
    exact QProb.equiv_trans (observed (actionEvent action)) full
  have preserved := Kernel.distribution_eq_observational_of_action_one native.toLatentRootSCM
    queryKernel (reference action)
    (by rw [native.toLatentRootSCM_observationalDist]; exact factual) (fun sample => sample y)
  rw [← native.kernelDistribution_preserved, queryKernel_distribution,
    native.toLatentRootSCM_observationalDist] at preserved
  exact QProb.equiv_trans preserved (observed (fun sample => sample y))

/-- The complete fixed-distribution answer for the bow, including zeros:
this action's effect is identified exactly when that action has probability
one.  A positive other-action mass is refuted by actual attained endpoints,
not by graph-level ID failure or an unavailable observational expression. -/
theorem identified_iff_action_one (projection : FiniteLatentProjection signature)
    (present : projection.observedGraph.bidirected x y = true)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) :
    IdentifiedAt projection law action ↔ QProb.Equiv (law.probVal (actionEvent action)) QProb.one := by
  constructor
  · intro identified
    have same := identified (endpointModel projection present law false) (endpointModel projection present law true)
      (endpointModel_hasObservedLaw projection present law false)
      (endpointModel_hasObservedLaw projection present law true)
    have endpoints : QProb.Equiv (lower law action) (upper law action) :=
      QProb.equiv_trans (QProb.equiv_symm (native_lower_endpoint projection present law action))
        (QProb.equiv_trans same (native_upper_endpoint projection present law action))
    rcases Nat.eq_zero_or_pos (outside law action).num with zero | positive
    · exact (outside_zero_iff_action_one law action).mp zero
    · have strict := lower_lt_upper_of_outside_positive law action positive
      exact False.elim (QProb.lt_irrefl (upper law action)
        (QProb.lt_congr endpoints (QProb.equiv_refl _) strict))
  · intro full left right leftLaw rightLaw
    exact QProb.equiv_trans (native_effect_eq_observed_of_action_one left law leftLaw action full)
      (QProb.equiv_symm (native_effect_eq_observed_of_action_one right law rightLaw action full))

end BinaryBow
end Causality
end Thesis
