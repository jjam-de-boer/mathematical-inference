import Thesis.Causality.PrivateNoise

namespace Thesis
namespace Causality

open Probability

/-!
# Semantic response of latent-dependent private-noise replacements

`PrivateNoise` proves full support for observable private readouts.  A
shared-latent collider also reads its actual shared mask from the incident
latent inputs.  Such a replacement is not an observable readout of the old
pivot value alone, so its support must not be justified by that narrower API.

The local theorem below permits any typed replacement mechanism.  If its
response at one explicit old unit and noise bit restores the old pivot, then
topological induction restores the entire intervened assignment.  No
non-influence of descendants is needed for this restoring statement.

The positivity theorem uses a displayed target-dependent noise bit that works
for every old unit realizing that target.  It integrates the actual positive
rectangle in `noise × old prior`, without choosing one latent realization
from the old model's positive mass.  The replacement may depend on incident
latent data, but it must still prove the restoring response on those units.

The observable-response bridge is separate.  A latent-dependent replacement
preserves full observational equality only after its actual local response
is proved to be the same function of the old observed assignment and fresh
bit in both models.  It is not treated as an ordinary observable readout
merely because its output value type is observed.
-/

variable {S : ObservedSignature.{0}}

/-- A local fixed-point response restores the whole old interventional
assignment, even when descendants read the pivot.  Old inputs and the fresh
bit are literal data; the mechanism still reads only declared parents and
incident latent coordinates. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_evalNodeUnder_eq_of_restores
    (base : ExactModel S) (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (bit : Bool)
    (restores : replacement (fun parent _edge => base.evalNodeUnder intervention old parent)
      (fun root _selected => old root) bit = base.evalNodeUnder intervention old pivot)
    (child : Fin S.count) :
    (base.withPrivateBooleanNoise pivot noise replacement).evalNodeUnder intervention
      (PrivateBooleanNoise.assignment base.latent bit old) child =
      base.evalNodeUnder intervention old child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases fixed : intervention child with
  | some value => rfl
  | none =>
      have parentsEqual :
          (fun parent (_edge : S.directed parent child = true) =>
            (base.withPrivateBooleanNoise pivot noise replacement).evalNodeUnder intervention
              (PrivateBooleanNoise.assignment base.latent bit old) parent) =
          (fun parent (_edge : S.directed parent child = true) => base.evalNodeUnder intervention old parent) := by
        funext parent edge
        exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_restores pivot noise replacement
          intervention old bit restores parent
      rw [parentsEqual]
      by_cases same : child = pivot
      · subst child
        rw [base.withPrivateBooleanNoise_mechanism_pivot]
        unfold PrivateBooleanNoise.oldInputs PrivateBooleanNoise.bit
        simp only [PrivateBooleanNoise.assignment_castSucc, PrivateBooleanNoise.assignment_last]
        have oldEquation : base.evalNodeUnder intervention old pivot =
            base.mechanism pivot (fun parent _edge => base.evalNodeUnder intervention old parent)
              (fun root _selected => old root) := by
          rw [FiniteLatentSCM.evalNodeUnder]
          unfold FiniteLatentSCM.equationUnder
          rw [fixed]
        rw [← oldEquation]
        exact restores
      · simp only [base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child same]
        unfold PrivateBooleanNoise.oldInputs
        simp only [PrivateBooleanNoise.assignment_castSucc]
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem FiniteLatentSCM.withPrivateBooleanNoise_evalUnder_eq_of_restores
    (base : ExactModel S) (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (bit : Bool)
    (restores : replacement (fun parent _edge => base.evalUnder intervention old parent)
      (fun root _selected => old root) bit = base.evalUnder intervention old pivot) :
    (base.withPrivateBooleanNoise pivot noise replacement).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent bit old) = base.evalUnder intervention old := by
  funext child
  exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_restores pivot noise replacement
    intervention old bit restores child

/-- An explicit restoring bit gives full-alphabet observational positivity
for a latent-dependent replacement.  The response condition is checked at
every old unit realizing a target, not at a latent witness chosen from an
existential support assertion. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_positive_of_restores
    (base : ExactModel S) (positive : ObservationallyPositive base) (pivot : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (restoreBit : S.Assignment -> Bool)
    (restore : forall target old, base.eval old = target ->
      replacement (fun parent _edge => target parent) (fun root _selected => old root)
        (restoreBit target) = target pivot) :
    ObservationallyPositive (base.withPrivateBooleanNoise pivot noise replacement) := by
  intro target
  let modified := base.withPrivateBooleanNoise pivot noise replacement
  let oldEvent := fun old : base.latent.Assignment => FiniteProbRecord.singletonEvent target (base.eval old)
  let rectangle := fun pair : Bool × base.latent.Assignment =>
    FiniteProbRecord.singletonEvent (restoreBit target) pair.1 && oldEvent pair.2
  let event := fun pair : Bool × base.latent.Assignment =>
    FiniteProbRecord.singletonEvent target (modified.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2))
  have oldPositive : 0 < FiniteProbRecord.eventMass base.prior.atoms oldEvent := by
    simpa only [FiniteLatentSCM.observationalDist, FiniteProbRecord.map, FiniteProbRecord.probVal,
      FiniteProbRecord.eventMass_map_labels, oldEvent] using positive target
  have rectanglePositive : 0 < FiniteProbRecord.eventMass (noise.product base.prior).atoms rectangle := by
    rw [FiniteProbRecord.product, FiniteProbRecord.eventMass_weightedCartesian]
    exact Nat.mul_pos (noisePositive (restoreBit target)) oldPositive
  have included : forall pair, rectangle pair = true -> event pair = true := by
    intro pair selected
    have parts := Bool.and_eq_true_iff.mp selected
    have sameBit : pair.1 = restoreBit target := of_decide_eq_true parts.1
    have oldTarget : base.eval pair.2 = target := of_decide_eq_true parts.2
    have restores : replacement (fun parent _edge => base.eval pair.2 parent)
        (fun root _selected => pair.2 root) pair.1 = base.eval pair.2 pivot := by
      rw [oldTarget, sameBit]
      exact restore target pair.2 oldTarget
    have restored := base.withPrivateBooleanNoise_evalUnder_eq_of_restores pivot noise replacement
      (FiniteLatentSCM.noIntervention S) pair.2 pair.1 restores
    exact decide_eq_true (restored.trans oldTarget)
  have bound := FiniteProbRecord.eventMass_mono (noise.product base.prior).atoms rectangle event included
  have pushedPositive := Nat.lt_of_lt_of_le rectanglePositive bound
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => FiniteProbRecord.singletonEvent target (modified.eval latent))
  exact (QProb.equiv_num_pos_iff (QProb.equiv_trans
    (modified.observationalValue_eq (FiniteProbRecord.singletonEvent target)) pushed)).mpr pushedPositive

/-! ## A proved observable response for a latent-dependent mechanism -/

/-- The local replacement may read incident latents, but its realized
response can still be an explicit common observable function.  Together with
non-influence of the pivot this proves the exact full assignment update.
The equality premise must be established on the model's actual old units. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_evalUnder_of_response
    (base : ExactModel S) (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (free : intervention pivot = none)
    (response : S.Assignment -> Bool -> S.Value pivot)
    (responseEq : forall old bit, replacement (fun parent _edge => base.evalUnder intervention old parent)
      (fun root _selected => old root) bit = response (base.evalUnder intervention old) bit)
    (old : base.latent.Assignment) (bit : Bool) :
    (base.withPrivateBooleanNoise pivot noise replacement).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent bit old) =
      S.replace (base.evalUnder intervention old) pivot (response (base.evalUnder intervention old) bit) := by
  funext child
  by_cases same : child = pivot
  · subst child
    rw [ObservedSignature.replace_at]
    exact (base.withPrivateBooleanNoise_evalNodeUnder_pivot pivot noise replacement intervention free old bit).trans
      (responseEq old bit)
  · rw [S.replace_ne _ pivot child _ same]
    exact base.withPrivateBooleanNoise_evalNodeUnder_eq_of_ne pivot noise replacement ignored
      intervention old bit child same

/-- The whole observational law is obtained by finite integration of the
proved response map against the actual old observed law and independent
noise.  This theorem does not identify arbitrary latent-dependent updates
with an observable map without their response proof. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_observationalValue_equiv_of_response
    (base : ExactModel S) (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore pivot) (response : S.Assignment -> Bool -> S.Value pivot)
    (responseEq : forall old bit, replacement (fun parent _edge => base.eval old parent)
      (fun root _selected => old root) bit = response (base.eval old) bit)
    (event : Event S.Assignment) :
    QProb.Equiv ((base.withPrivateBooleanNoise pivot noise replacement).observationalValue event)
      ((noise.product base.observationalDist).probVal
        (fun pair => event (S.replace pair.2 pivot (response pair.2 pair.1)))) := by
  let modified := base.withPrivateBooleanNoise pivot noise replacement
  have evaluation (pair : Bool × base.latent.Assignment) :
      modified.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2) =
        S.replace (base.eval pair.2) pivot (response (base.eval pair.2) pair.1) :=
    base.withPrivateBooleanNoise_evalUnder_of_response pivot noise replacement ignored
      (FiniteLatentSCM.noIntervention S) rfl response responseEq pair.2 pair.1
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => event (modified.eval latent))
  have observed := (noise.product base.prior).probVal_congr _ _ (fun pair => congrArg event (evaluation pair))
  have originals := noise.product_map_right_probVal base.prior base.eval
    (fun pair => event (S.replace pair.2 pivot (response pair.2 pair.1)))
  exact QProb.equiv_trans (modified.observationalValue_eq event)
    (QProb.equiv_trans pushed (QProb.equiv_trans observed (QProb.equiv_symm originals)))

/-- Two latent-dependent replacements preserve full observational equality
when they realize the same observable response and the unchanged mechanisms
ignore their pivot.  Their latent spaces may differ; each response proof is
checked separately before the finite observable slices are compared. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_observationally_equivalent_of_response
    (left right : ExactModel S) (observational : ObservationallyEquivalent left right)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (leftReplacement : S.ParentValues pivot -> left.latent.Inputs pivot -> Bool -> S.Value pivot)
    (rightReplacement : S.ParentValues pivot -> right.latent.Inputs pivot -> Bool -> S.Value pivot)
    (leftIgnored : left.OtherMechanismsIgnore pivot) (rightIgnored : right.OtherMechanismsIgnore pivot)
    (response : S.Assignment -> Bool -> S.Value pivot)
    (leftResponse : forall old bit, leftReplacement (fun parent _edge => left.eval old parent)
      (fun root _selected => old root) bit = response (left.eval old) bit)
    (rightResponse : forall old bit, rightReplacement (fun parent _edge => right.eval old parent)
      (fun root _selected => old root) bit = response (right.eval old) bit) :
    ObservationallyEquivalent (left.withPrivateBooleanNoise pivot noise leftReplacement)
      (right.withPrivateBooleanNoise pivot noise rightReplacement) := by
  intro event
  exact QProb.equiv_trans
    (left.withPrivateBooleanNoise_observationalValue_equiv_of_response pivot noise leftReplacement
      leftIgnored response leftResponse event)
    (QProb.equiv_trans
      (noise.product_probVal_equiv_of_slices left.observationalDist right.observationalDist
        (fun pair => event (S.replace pair.2 pivot (response pair.2 pair.1)))
        (fun pair => event (S.replace pair.2 pivot (response pair.2 pair.1)))
        (fun bit => observational (fun sample => event (S.replace sample pivot (response sample bit)))))
      (QProb.equiv_symm
        (right.withPrivateBooleanNoise_observationalValue_equiv_of_response pivot noise rightReplacement
          rightIgnored response rightResponse event)))

end Causality
end Thesis
