import Thesis.Causality.ConsistencyBounds
import Thesis.Causality.Identification

namespace Thesis
namespace Causality
namespace BinaryBow

open Probability

/-!
# Arbitrary-law endpoint models for the binary confounded bow

The observed signature is `X -> Y`.  One shared finite root stores a complete
factual pair `(X_f,Y_f)` with any supplied exact rational observational law.
The treatment equation returns `X_f`.  The outcome equation returns `Y_f`
when its actual parent agrees with `X_f`, and a supplied Boolean value when
that parent differs.  False and true therefore give the prospective lower
and upper endpoint models without changing their whole factual law.

The shared-root alphabet is the explicitly enumerated finite observed
assignment type, not a chosen set of response profiles.  Zeros and repeated
weighted labels in the supplied law are retained.  The root law is a genuine
one-factor independent prior with a proved product law.  Mechanisms read
only the declared parent and incident-root inputs; no intervention evaluates
the old factual treatment equation in place of its current parent signal.

This module constructs the models and proves their unit-level executions
and whole observational-law preservation.  Sharp probability endpoints,
native hidden-DAG realization, and fixed-law classification are assembled
separately; a convenient subfamily is not substituted for the full class.
-/

/-- Both observed domains are Boolean, in the topological order `X,Y`. -/
def signature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by decide +kernel

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

/-- The bidirected edge is present between the two distinct observed nodes. -/
def graph : ObservedGraph signature where
  bidirected := fun first second => !(Nat.beq first.val second.val)
  bidirected_symmetric := by
    intro first second present
    simpa only [natBeq_comm second.val first.val] using present
  bidirected_irreflexive := by intro node; simp only [natBeq_refl, Bool.not_true]

/-- Exhaustive node cases are a closed finite statement, not Prop EM. -/
theorem node_cases : forall node : Fin signature.count, node = x ∨ node = y := by
  decide +kernel

/-- One shared root remembers the complete factual observed pair. -/
def latent : LatentExtension signature where
  count := 1
  Value := fun _ => signature.Assignment
  valueEnumeration := fun _ => signature.assignmentEnumeration
  value_complete := fun _ => signature.assignmentEnumeration_complete
  valueDecidableEq := fun _ => signature.assignmentDecidableEq
  incident := fun _ _ => true

def root : Fin latent.count := ⟨0, by decide⟩

/-- Lift the supplied factual law to the one-coordinate root assignment.
No labels or weights are dropped, including any zero-weight atoms. -/
def prior (law : FiniteProbRecord signature.Assignment) : FiniteProbRecord latent.Assignment :=
  law.map (fun factual _ => factual)

/-- The off-factual value is free, but the actual factual law is not.
The independent product law is rebuilt from this exact supplied record. -/
def model (law : FiniteProbRecord signature.Assignment) (offFactual : Bool) : ExactModel signature where
  latent := latent
  factor := fun _ => law
  prior := prior law
  product_law := by
    intro events
    simpa [prior, latent, LatentExtension.rectangularEvent,
      FiniteProduct.rectangularEvent, FiniteProduct.qProduct,
      QProb.mul, QProb.one, QProb.Equiv] using
      (law.map_probVal (fun factual _ => factual) (latent.rectangularEvent events))
  mechanism := fun child parents inputs =>
    let factual := inputs root rfl
    if atX : child.val = 0 then factual x
    else
      let atY : child.val = 1 := by
        have bounded : child.val < 2 := child.isLt
        omega
      if parents x (by simp [signature, x, atY]) = factual x then factual y else offFactual

/-- The root has at most two distinct observed recipients.  This remains
true for every supplied law and either off-factual outcome. -/
theorem model_isCanonical (law : FiniteProbRecord signature.Assignment) (offFactual : Bool) :
    (model law offFactual).IsCanonicalSemiMarkovian := by
  change forall (_source : Fin 1) (first second third : Fin 2),
    true = true → true = true → true = true →
      first = second ∨ first = third ∨ second = third
  decide +kernel

theorem model_hasProjectedGraph (law : FiniteProbRecord signature.Assignment) (offFactual : Bool) :
    HasProjectedGraph (model law offFactual) graph := by
  intro first second
  simp only [FiniteLatentSCM.observedGraph, model,
    LatentExtension.observedGraph, LatentExtension.projectedBidirected,
    latent, graph, finAny, Bool.and_self, Bool.false_or, Bool.and_true]

theorem model_compatible (law : FiniteProbRecord signature.Assignment) (offFactual : Bool) :
    Compatible (model law offFactual) graph :=
  ⟨model_isCanonical law offFactual, model_hasProjectedGraph law offFactual⟩

/-! ## Symbolic execution at every latent unit -/

/-- Treatment either takes its intervened value or returns the factual one. -/
theorem eval_x (law : FiniteProbRecord signature.Assignment) (offFactual : Bool)
    (target : (node : Fin signature.count) → Option (signature.Value node))
    (unit : latent.Assignment) :
    (model law offFactual).evalUnder target unit x = (target x).getD (unit root x) := by
  change (model law offFactual).evalNodeUnder target unit x = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases target x <;> rfl

/-- The outcome reads the current treatment parent, not the factual
treatment mechanism.  Intervening on the outcome itself is also respected. -/
theorem eval_y (law : FiniteProbRecord signature.Assignment) (offFactual : Bool)
    (target : (node : Fin signature.count) → Option (signature.Value node))
    (unit : latent.Assignment) :
    (model law offFactual).evalUnder target unit y =
      match target y with
      | some value => value
      | none => if (model law offFactual).evalUnder target unit x = unit root x
          then unit root y else offFactual := by
  change (model law offFactual).evalNodeUnder target unit y = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases target y <;> rfl

/-- Every factual observed assignment is exactly the pair stored at the
shared root, regardless of the off-factual behavior or of its probability. -/
theorem eval_factual (law : FiniteProbRecord signature.Assignment) (offFactual : Bool)
    (unit : latent.Assignment) : (model law offFactual).eval unit = unit root := by
  funext node
  rcases node_cases node with same | same
  · subst node
    simp only [FiniteLatentSCM.eval, eval_x, FiniteLatentSCM.noIntervention, Option.getD_none]
  · subst node
    simp [FiniteLatentSCM.eval, eval_y, eval_x, FiniteLatentSCM.noIntervention]

/-- All observed event probabilities equal the supplied law.  This proves
the whole law, not merely coordinate marginals or one selected query cell. -/
theorem observationalValue_preserved (law : FiniteProbRecord signature.Assignment)
    (offFactual : Bool) (event : Event signature.Assignment) :
    QProb.Equiv ((model law offFactual).observationalValue event) (law.probVal event) :=
  QProb.equiv_trans ((model law offFactual).observationalValue_eq event)
    (QProb.equiv_trans
      (law.map_probVal (fun factual _ => factual)
        (fun unit => event ((model law offFactual).eval unit)))
      (law.probVal_congr _ _ (fun factual =>
        congrArg event (eval_factual law offFactual (fun _ => factual)))))

/-- A single treatment intervention; the other observed coordinate remains
unforced.  Its value type is literally Boolean, so no dependent cast is
hidden in the operation used to calculate the bounds. -/
def intervention (action : Bool) : HardIntervention signature where
  value := fun node => if node.val = 0 then some action else none

theorem eval_intervened_y (law : FiniteProbRecord signature.Assignment) (offFactual action : Bool)
    (unit : latent.Assignment) :
    (model law offFactual).evalUnder (intervention action).value unit y =
      if action = unit root x then unit root y else offFactual := by
  rw [eval_y, eval_x]
  simp [intervention, x, y] <;> rfl

end BinaryBow
end Causality
end Thesis
