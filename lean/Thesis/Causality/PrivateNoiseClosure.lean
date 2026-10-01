import Thesis.Causality.PrivateNoise

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Protected mechanism sets under arbitrary private replacements

A readout can have responding descendants without affecting every coordinate.
The relevant invariant for a selected marginal is that its protected rows
read only protected parent values.  This is a property of the actual
mechanisms, not a demand that the ambient graph have no other parent edges.
Unprotected mechanisms may depend on the replaced vertex and may change.

Replacing a row outside such a set preserves the invariant and the complete
values inside it, under arbitrary interventions and on full observed
alphabets.  At probability level, the literal new private factor integrates
out of each protected event.  No non-influence assertion about all other
mechanisms, positivity condition, noise bias, or binary value restriction is
required.  Conditional countermodels use this local invariant to retain
their denominator in the same models that separate the numerator.
-/

/-- Selected rows use only selected parent coordinates, at every typed
latent input.  Rows outside the set are unrestricted; declared but unused
arrows from outside the set are allowed. -/
def FiniteLatentSCM.MechanismsClosedOn (base : ExactModel S) (nodes : NodeSet S) : Prop :=
  forall child, nodes child = true ->
    forall (first second : S.ParentValues child) (inputs : base.latent.Inputs child),
      (forall parent (edge : S.directed parent child = true), nodes parent = true ->
        first parent edge = second parent edge) ->
      base.mechanism child first inputs = base.mechanism child second inputs

/-- A replacement outside a protected set leaves its mechanism closure
intact.  The retained rows use the explicitly recovered old incident inputs;
the new replacement may inspect all of its own declared parents. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_mechanismsClosedOn
    (base : ExactModel S) (nodes : NodeSet S) (closed : base.MechanismsClosedOn nodes)
    (pivot : Fin S.count) (off : nodes pivot = false) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot) :
    (base.withPrivateBooleanNoise pivot noise replacement).MechanismsClosedOn nodes := by
  intro child selected first second inputs agree
  have different : child ≠ pivot := by
    intro same
    subst child
    rw [off] at selected
    cases selected
  rw [base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child different,
    base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child different]
  exact closed child selected first second _ agree

/-- Actual values in a closed protected set remain unchanged.  The
topological recursion compares only protected parent inputs; unrelated
responding descendants do not enter the argument.  Interventions may cut
either protected rows or the replaced row, and their labels are arbitrary. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_evalNodeUnder_eq_of_mechanismsClosedOn
    (base : ExactModel S) (nodes : NodeSet S) (closed : base.MechanismsClosedOn nodes)
    (pivot : Fin S.count) (off : nodes pivot = false) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (bit : Bool) (child : Fin S.count) (selected : nodes child = true) :
    (base.withPrivateBooleanNoise pivot noise replacement).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment base.latent bit old) child =
      base.evalNodeUnder intervention old child := by
  have different : child ≠ pivot := by
    intro same
    subst child
    rw [off] at selected
    cases selected
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases intervention child with
  | some value => rfl
  | none =>
      simp only [base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child different]
      unfold PrivateBooleanNoise.oldInputs
      simp only [PrivateBooleanNoise.assignment_castSucc]
      apply closed child selected
      intro parent edge protectedParent
      exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_mechanismsClosedOn nodes closed pivot off noise replacement
        intervention old bit parent protectedParent
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- The real independent private prior preserves every protected event
probability.  Full pointwise value agreement makes the event ignore the fresh
bit, and the finite product marginal law integrates that factor out. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_interventionalValue_equiv_of_mechanismsClosedOn
    (base : ExactModel S) (nodes : NodeSet S) (closed : base.MechanismsClosedOn nodes)
    (pivot : Fin S.count) (off : nodes pivot = false) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : S.Assignment -> Bool) (eventLocal : EventDependsOnlyOn nodes event) :
    QProb.Equiv ((base.withPrivateBooleanNoise pivot noise replacement).interventionalValue intervention event)
      (base.interventionalValue intervention event) := by
  let model := base.withPrivateBooleanNoise pivot noise replacement
  have eventEqual (pair : Bool × base.latent.Assignment) :
      event (model.evalUnder intervention (PrivateBooleanNoise.assignment base.latent pair.1 pair.2)) =
        event (base.evalUnder intervention pair.2) := by
    apply eventLocal
    intro child selected
    exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_mechanismsClosedOn nodes closed pivot off noise replacement
      intervention pair.2 pair.1 child selected
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun unit => event (model.evalUnder intervention unit))
  have unchanged := (noise.product base.prior).probVal_congr _ _ eventEqual
  have marginal := noise.product_probVal_right base.prior (fun unit => event (base.evalUnder intervention unit))
  exact QProb.equiv_trans (model.interventionalValue_eq intervention event)
    (QProb.equiv_trans pushed (QProb.equiv_trans unchanged
      (QProb.equiv_trans marginal (QProb.equiv_symm (base.interventionalValue_eq intervention event)))))

end Causality
end Thesis
