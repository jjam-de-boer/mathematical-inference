import Thesis.Causality.Learning

namespace Thesis
namespace Causality

open Probability

/-!
Executable compact structural surgery, independent of transition packaging.

This is the short, reference presentation of a hard intervention.  Starting
with an `ExactModel M` and an action, the file (1) changes the observed graph
and latent-incidence mask, (2) replaces selected structural equations by
constants, (3) proves by well-founded recursion that the resulting evaluator
agrees with `M.evalUnder action`, and (4) packages the model as an epistemic
record with no residual compact intervention.  `Atomic` gives the longer edit
program; `SurgeryEquivalence` proves that the two presentations agree at the
unit level.
-/

namespace SurgicalIntervention

/-! ## The mutilated signature and latent interface -/

abbrev signature (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    ObservedSignature :=
  M.mutilatedSignature action

/--
Remove latent inputs into every node fixed by the action.  The latent roots
themselves and their value spaces are retained; only their incident edges into
selected observed coordinates are cut.
-/
def latent (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    LatentExtension (signature M action) where
  count := M.latent.count
  Value := M.latent.Value
  valueEnumeration := M.latent.valueEnumeration
  value_complete := M.latent.value_complete
  valueDecidableEq := M.latent.valueDecidableEq
  incident := fun source child =>
    if FiniteLatentSCM.cutOf S action child then false
    else M.latent.incident source child

theorem directed_cut (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (parent child : Fin S.count) (value : S.Value child)
    (selected : action child = some value) :
    (signature M action).directed parent child = false := by
  simp [FiniteLatentSCM.mutilatedSignature,
    mutilatedDirected, FiniteLatentSCM.cutOf, selected]

theorem latent_cut (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (source : Fin M.latent.count) (child : Fin S.count)
    (value : S.Value child) (selected : action child = some value) :
    (latent M action).incident source child = false := by
  simp [latent, FiniteLatentSCM.cutOf, selected]

/--
Evaluate one equation in the surgically modified model.  The selected branch
returns the requested constant.  In the unselected branch, every remaining
parent and latent-input proof is transported back to the corresponding input
of `M`.
-/
def mechanism (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin (signature M action).count)
    (parents : (signature M action).ParentValues child)
    (latents : (latent M action).Inputs child) :
    (signature M action).Value child :=
  if selected : (action child).isSome = true then
    (action child).get selected
  else
    have actionNone : action child = none := by
      cases hAction : action child with
      | none => rfl
      | some value => simp [hAction] at selected
    M.mechanism child
      (fun parent edge => parents parent (by
        simpa [signature, FiniteLatentSCM.mutilatedSignature,
          mutilatedDirected, FiniteLatentSCM.cutOf, actionNone] using edge))
      (fun source incident => latents source (by
        simpa [latent, FiniteLatentSCM.cutOf, actionNone] using incident))

/--
The graph-changing SCM whose selected equations are constant.  Its latent
prior and factor records are unchanged, because an intervention changes
structural equations and incoming arrows, not exogenous randomness.
-/
def model (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    ExactModel (signature M action) where
  latent := latent M action
  factor := M.factor
  prior := M.prior
  product_law := M.product_law
  mechanism := mechanism M action

/--
The local semantic comparison.  Recursion follows the original topological
order: after the selected-node case, every recursive call concerns a strictly
earlier parent.  This is the substantive bridge from graph surgery to the
existing `evalUnder` semantics.
-/
theorem evalNode_eq (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (u : M.latent.Assignment) (child : Fin S.count) :
    (model M action).evalNodeUnder
        (FiniteLatentSCM.noIntervention (signature M action)) u child =
      M.evalNodeUnder action u child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  simp only [FiniteLatentSCM.noIntervention]
  cases selected : action child with
  | some value =>
      simp [model, mechanism, selected]
  | none =>
      simp [model, mechanism, selected]
      congr 1
      funext parent edge
      exact evalNode_eq M action u parent
termination_by child.val
decreasing_by
  exact S.directed_earlier (by
    simpa [signature, FiniteLatentSCM.mutilatedSignature,
      mutilatedDirected, FiniteLatentSCM.cutOf, selected] using edge)

/--
Structural surgery and equation override have the same full unit-level
outcome.  Extensionality reduces the assignment equality to `evalNode_eq` at
each observed coordinate.
-/
theorem eval_eq_evalUnder (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (u : M.latent.Assignment) :
    (model M action).eval u = M.evalUnder action u := by
  funext child
  exact evalNode_eq M action u child

/--
Package the surgically modified model as a record.  The compact intervention
field is reset to empty because its effect is now compiled into the model.
-/
def apply (R : CausalEpistemicRecord S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    CausalEpistemicRecord (signature R.model action) where
  model := model R.model action
  belief := R.belief
  intervention := HardIntervention.empty (signature R.model action)
  stack := R.acrossStack .surgery

/--
The three constituent obligations of a finite `do` construction: remove every
directed and latent input into selected nodes, then replace each selected
equation by its chosen value.
-/
structure Plan (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node)) where
  directedRemoved : forall parent child value,
    action child = some value ->
      (signature M action).directed parent child = false
  latentRemoved : forall source child value,
    action child = some value ->
      (latent M action).incident source child = false
  valueEffective : forall u child value,
    action child = some value -> (model M action).eval u child = value

def plan (M : ExactModel S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    Plan M action where
  directedRemoved := directed_cut M action
  latentRemoved := latent_cut M action
  valueEffective := by
    intro u child value selected
    rw [eval_eq_evalUnder]
    exact M.evalUnder_effectiveness action u child value selected

end SurgicalIntervention

end Causality
end Thesis
