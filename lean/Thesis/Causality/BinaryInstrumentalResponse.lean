import Thesis.Causality.BinaryInstrumentalProfiles
import Thesis.Probability.FiniteProductSplicing

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Read the instrument and response tables from an arbitrary IV SCM

The observed parent signature already enforces the exclusion restriction:
`Z` has no observed parent, `X` reads only `Z`, and `Y` reads only `X`.
Absence of the projected edges `Z <-> X` and `Z <-> Y` additionally prevents
any noise coordinate used by the instrument from being read by either
response mechanism.  This is an actual structural property of the input
model, not a probabilistic independence assertion supplied by a caller.

The instrument and four response bits are read directly from each latent
assignment.  Splicing two independent copies then proves their joint law
equals the product of their actual marginal records.  Consequently *every*
such SCM, with arbitrary finite root alphabets and observational zeros, has
the sixteen-profile representation of its whole observed law and each
treatment intervention.  No monotonicity, positivity, or latent-size bound
is imposed, and no latent source is merged with the instrument.
-/

def graph : ObservedGraph signature where
  bidirected := fun first second => decide
    ((first.val = 1 ∧ second.val = 2) ∨ (first.val = 2 ∧ second.val = 1))
  bidirected_symmetric := by
    intro first second selected
    apply decide_eq_true
    rcases of_decide_eq_true selected with ⟨atX, atY⟩ | ⟨atY, atX⟩
    · exact Or.inr ⟨atY, atX⟩
    · exact Or.inl ⟨atX, atY⟩
  bidirected_irreflexive := by
    intro node
    apply decide_eq_false
    rintro (⟨one, two⟩ | ⟨two, one⟩) <;> omega

theorem graph_no_z_x : graph.bidirected z x = false := rfl
theorem graph_no_z_y : graph.bidirected z y = false := rfl
theorem graph_x_y : graph.bidirected x y = true := rfl

theorem node_cases : forall node : Fin signature.count, node = z ∨ node = x ∨ node = y := by
  decide +kernel

/-- Noise used by the instrument is unavailable to either response equation.
This predicate is derived below from actual projected-graph absence. -/
def NoInstrumentConfounding (model : ExactModel signature) : Prop :=
  forall root, model.latent.incident root z = true →
    model.latent.incident root x = false ∧ model.latent.incident root y = false

private theorem shared_root_edge (model : ExactModel signature) (root : Fin model.latent.count)
    (first second : Fin signature.count) (different : first ≠ second)
    (firstIncident : model.latent.incident root first = true)
    (secondIncident : model.latent.incident root second = true) :
    model.observedGraph.bidirected first second = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · cases same : Nat.beq first.val second.val with
    | false => rfl
    | true => exact False.elim (different (Fin.ext (Nat.eq_of_beq_eq_true same)))
  · exact finAny_eq_true_of _ root (Bool.and_eq_true_iff.mpr ⟨firstIncident, secondIncident⟩)

/-- The IV graph itself proves the required disjoint noise access.  No
counterfactual or independence theorem is assumed in this extraction. -/
theorem noInstrumentConfounding_of_projectedGraph (model : ExactModel signature)
    (matches : HasProjectedGraph model graph) : NoInstrumentConfounding model := by
  intro root atZ
  constructor
  · cases atX : model.latent.incident root x with
    | false => rfl
    | true =>
        have present := shared_root_edge model root z x (by decide) atZ atX
        have absent := (matches z x).trans graph_no_z_x
        exact False.elim (Bool.false_ne_true (absent.symm.trans present))
  · cases atY : model.latent.incident root y with
    | false => rfl
    | true =>
        have present := shared_root_edge model root z y (by decide) atZ atY
        have absent := (matches z y).trans graph_no_z_y
        exact False.elim (Bool.false_ne_true (absent.symm.trans present))

private def constantParents (child : Fin signature.count) (value : Bool) : signature.ParentValues child :=
  fun _ _ => value

private def inputs (model : ExactModel signature) (child : Fin signature.count)
    (unit : model.latent.Assignment) : model.latent.Inputs child := fun root _ => unit root

def instrumentRead (model : ExactModel signature) (unit : model.latent.Assignment) : Bool :=
  model.mechanism z (constantParents z false) (inputs model z unit)

def treatmentResponse (model : ExactModel signature) (unit : model.latent.Assignment) (instrument : Bool) : Bool :=
  model.mechanism x (constantParents x instrument) (inputs model x unit)

def outcomeResponse (model : ExactModel signature) (unit : model.latent.Assignment) (action : Bool) : Bool :=
  model.mechanism y (constantParents y action) (inputs model y unit)

/-- All four potential outputs are read from the supplied noise unit.
Only declared latent inputs and the one permitted observed parent are used. -/
def profileRead (model : ExactModel signature) (unit : model.latent.Assignment) : Profile :=
  fun bit => if bit.val = 0 then treatmentResponse model unit false
    else if bit.val = 1 then treatmentResponse model unit true
    else if bit.val = 2 then outcomeResponse model unit false
    else outcomeResponse model unit true

theorem profileRead_treatment (model : ExactModel signature) (unit : model.latent.Assignment) (instrument : Bool) :
    treatmentAt (profileRead model unit) instrument = treatmentResponse model unit instrument := by
  cases instrument <;> rfl

theorem profileRead_outcome (model : ExactModel signature) (unit : model.latent.Assignment) (action : Bool) :
    outcomeAt (profileRead model unit) action = outcomeResponse model unit action := by
  cases action <;> rfl

/-! ## Complementary readout locality at every supplied unit -/

def instrumentAllocation (model : ExactModel signature) : Fin model.latent.count → Bool :=
  fun root => model.latent.incident root z

theorem instrumentRead_splice (model : ExactModel signature) (first second : model.latent.Assignment) :
    instrumentRead model (FiniteProduct.splice (instrumentAllocation model) first second) = instrumentRead model first := by
  have same : inputs model z (FiniteProduct.splice (instrumentAllocation model) first second) = inputs model z first := by
    funext root incident
    simp only [inputs, FiniteProduct.splice, instrumentAllocation, incident, if_true]
  simp only [instrumentRead, same]

private theorem inputs_splice_right (model : ExactModel signature) (child : Fin signature.count)
    (excluded : forall root, model.latent.incident root child = true → model.latent.incident root z = false)
    (first second : model.latent.Assignment) :
    inputs model child (FiniteProduct.splice (instrumentAllocation model) first second) = inputs model child second := by
  funext root incident
  simp only [inputs, FiniteProduct.splice, instrumentAllocation, excluded root incident, Bool.false_eq_true, if_false]

private theorem instrument_excluded_at_x (model : ExactModel signature) (unconfounded : NoInstrumentConfounding model)
    (root : Fin model.latent.count) (atX : model.latent.incident root x = true) :
    model.latent.incident root z = false := by
  cases atZ : model.latent.incident root z with
  | false => rfl
  | true => exact False.elim (Bool.false_ne_true ((unconfounded root atZ).1.symm.trans atX))

private theorem instrument_excluded_at_y (model : ExactModel signature) (unconfounded : NoInstrumentConfounding model)
    (root : Fin model.latent.count) (atY : model.latent.incident root y = true) :
    model.latent.incident root z = false := by
  cases atZ : model.latent.incident root z with
  | false => rfl
  | true => exact False.elim (Bool.false_ne_true ((unconfounded root atZ).2.symm.trans atY))

theorem profileRead_splice (model : ExactModel signature) (unconfounded : NoInstrumentConfounding model)
    (first second : model.latent.Assignment) :
    profileRead model (FiniteProduct.splice (instrumentAllocation model) first second) = profileRead model second := by
  have treatmentInputs := inputs_splice_right model x (instrument_excluded_at_x model unconfounded) first second
  have outcomeInputs := inputs_splice_right model y (instrument_excluded_at_y model unconfounded) first second
  funext bit
  simp only [profileRead, treatmentResponse, outcomeResponse, treatmentInputs, outcomeInputs]

/-! ## Exact symbolic execution of the observed signature -/

private theorem x_parent {parent : Fin signature.count} (edge : signature.directed parent x = true) : parent = z := by
  have selected := of_decide_eq_true edge
  change (parent.val = 0 ∧ 1 = 1) ∨ (parent.val = 1 ∧ 1 = 2) at selected
  rcases selected with ⟨same, _⟩ | ⟨_, impossible⟩
  · exact Fin.ext same
  · cases impossible

private theorem y_parent {parent : Fin signature.count} (edge : signature.directed parent y = true) : parent = x := by
  have selected := of_decide_eq_true edge
  change (parent.val = 0 ∧ 2 = 1) ∨ (parent.val = 1 ∧ 2 = 2) at selected
  rcases selected with ⟨_, impossible⟩ | ⟨same, _⟩
  · cases impossible
  · exact Fin.ext same

theorem eval_z (model : ExactModel signature)
    (target : (node : Fin signature.count) → Option (signature.Value node)) (unit : model.latent.Assignment) :
    model.evalUnder target unit z = (target z).getD (instrumentRead model unit) := by
  change model.evalNodeUnder target unit z = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases forced : target z with
  | some value => rfl
  | none =>
      have same : (fun parent (_edge : signature.directed parent z = true) => model.evalNodeUnder target unit parent) =
          constantParents z false := by
        funext parent edge
        have absent : signature.directed parent z = false := by simp [signature, z]
        rw [absent] at edge
        cases edge
      rw [same]
      rfl

theorem eval_x (model : ExactModel signature)
    (target : (node : Fin signature.count) → Option (signature.Value node)) (unit : model.latent.Assignment) :
    model.evalUnder target unit x = (target x).getD (treatmentResponse model unit (model.evalUnder target unit z)) := by
  change model.evalNodeUnder target unit x = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases forced : target x with
  | some value => rfl
  | none =>
      have same : (fun parent (_edge : signature.directed parent x = true) => model.evalNodeUnder target unit parent) =
          constantParents x (model.evalUnder target unit z) := by
        funext parent edge
        have equal := x_parent edge
        subst parent
        rfl
      rw [same]
      rfl

theorem eval_y (model : ExactModel signature)
    (target : (node : Fin signature.count) → Option (signature.Value node)) (unit : model.latent.Assignment) :
    model.evalUnder target unit y = (target y).getD (outcomeResponse model unit (model.evalUnder target unit x)) := by
  change model.evalNodeUnder target unit y = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases forced : target y with
  | some value => rfl
  | none =>
      have same : (fun parent (_edge : signature.directed parent y = true) => model.evalNodeUnder target unit parent) =
          constantParents y (model.evalUnder target unit x) := by
        funext parent edge
        have equal := y_parent edge
        subst parent
        rfl
      rw [same]
      rfl

/-- The profile readout reproduces the entire factual assignment, not just
the queried outcome, independently of the model's hidden alphabet sizes. -/
theorem eval_observedAssignment (model : ExactModel signature) (unit : model.latent.Assignment) :
    model.eval unit = observedAssignment (instrumentRead model unit) (profileRead model unit) := by
  funext node
  rcases node_cases node with same | same | same
  · subst node
    change model.evalUnder (FiniteLatentSCM.noIntervention signature) unit z = instrumentRead model unit
    rw [eval_z]
    rfl
  · subst node
    change model.evalUnder (FiniteLatentSCM.noIntervention signature) unit x =
      treatmentAt (profileRead model unit) (instrumentRead model unit)
    rw [eval_x, eval_z]
    simp only [FiniteLatentSCM.noIntervention, Option.getD_none, profileRead_treatment]
  · subst node
    change model.evalUnder (FiniteLatentSCM.noIntervention signature) unit y =
      outcomeAt (profileRead model unit) (treatmentAt (profileRead model unit) (instrumentRead model unit))
    rw [eval_y, eval_x, eval_z]
    simp only [FiniteLatentSCM.noIntervention, Option.getD_none, profileRead_treatment, profileRead_outcome]

def intervention (action : Bool) : HardIntervention signature where
  value := fun node => if node.val = 1 then some action else none

theorem eval_doX_outcome (model : ExactModel signature) (unit : model.latent.Assignment) (action : Bool) :
    model.evalUnder (intervention action).value unit y = outcomeAt (profileRead model unit) action := by
  rw [eval_y, eval_x]
  simp [intervention, x, y, profileRead_outcome]

/-! ## Complete forward probability representation -/

def instrumentRecord (model : ExactModel signature) : FiniteProbRecord Bool := model.prior.map (instrumentRead model)
def responseRecord (model : ExactModel signature) : FiniteProbRecord Profile := model.prior.map (profileRead model)

/-- The record-level product is derived from the input SCM's actual root
product law and proved mechanism locality, not from an IV completeness axiom. -/
theorem response_joint_law (model : ExactModel signature) (unconfounded : NoInstrumentConfounding model)
    (event : Event (Bool × Profile)) :
    QProb.Equiv (model.prior.probVal (fun unit => event (instrumentRead model unit, profileRead model unit)))
      (((instrumentRecord model).product (responseRecord model)).probVal event) :=
  FiniteProduct.readouts_product_probVal model.prior model.factor model.product_law
    model.latent.valueEnumeration model.latent.value_complete model.latent.valueDecidableEq
    (instrumentAllocation model) (instrumentRead model) (profileRead model)
    (instrumentRead_splice model) (profileRead_splice model unconfounded) event

/-- Every observed event is preserved by the independent sixteen-profile
representation.  Agreement of only the eight cells is not substituted for
the whole-law statement needed by fixed-distribution causal bounds. -/
theorem observationalValue_response (model : ExactModel signature) (unconfounded : NoInstrumentConfounding model)
    (event : Event signature.Assignment) :
    QProb.Equiv (model.observationalValue event)
      ((observedRecord (instrumentRecord model) (responseRecord model)).probVal event) :=
  QProb.equiv_trans (model.observationalValue_eq event)
    (QProb.equiv_trans
      (model.prior.probVal_congr _ _ (fun unit => congrArg event (eval_observedAssignment model unit)))
      (QProb.equiv_trans
        (response_joint_law model unconfounded (fun pair => event (observedAssignment pair.1 pair.2)))
        (QProb.equiv_symm
          (((instrumentRecord model).product (responseRecord model)).map_probVal
            (fun pair => observedAssignment pair.1 pair.2) event))))

/-- Both treatment actions use the same response weights as observation.
The intervention reads the actual selected parent value, not its old equation. -/
theorem interventionalValue_response (model : ExactModel signature) (action : Bool) :
    QProb.Equiv (model.interventionalValue (intervention action).value (fun sample => sample y))
      ((effectRecord (responseRecord model) action).probVal id) :=
  QProb.equiv_trans (model.interventionalValue_eq (intervention action).value _)
    (QProb.equiv_trans
      (model.prior.probVal_congr _ _ (fun unit => eval_doX_outcome model unit action))
      (QProb.equiv_symm
        (QProb.equiv_trans ((responseRecord model).map_probVal (fun profile => outcomeAt profile action) id)
          (model.prior.map_probVal (profileRead model) (fun profile => outcomeAt profile action)))))

end BinaryInstrumental
end Causality
end Thesis
