import Thesis.CausalTransport.HiddenDAGRealization
import Thesis.Examples.HiddenDAGRootPlacement

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGRealization

open Probability HiddenDAGCollapse HiddenDAGRootPlacement

/-!
# Execute original-DAG relays under a hard observed intervention

Keep the five-node original graph `U,X,V,Y,Z` and the canonical five-root
input family from `HiddenDAGRootPlacement`.  The source equations are
`X = privateX xor rootXY`, `Y = X xor rootXY xor rootYZ`, and
`Z = rootXZ xor rootYZ`.  All roots are independent unbiased bits.

The generic constructor must place the three shared channels at `U`, carry
them separately through the hidden relay `V`, and read the *intervened* `X`
value as the parent signal of `Y`.  With all original root bits true the
factual `Y` is false, but setting `X = true` makes `Y` true.  Re-evaluating the
old factual `X` equation behind the relay would fail this regression.

These are kernel-checked executions of the actual general constructor, not a
hand-written full-DAG model.  The unrestricted all-model preservation theorem
and probability preservation are separate obligations, not assumptions used
to obtain the displayed results.
-/

/-- Keep the actual root laws and incidence, replacing the constant source
equations by nontrivial private/shared noise and projected-parent reads. -/
def sourceModel : ExactModel signature :=
  { noiseModel with
    mechanism := fun child parents inputs =>
      if atX : child.val = 0 then
        Bool.xor
          (inputs privateRoot (by
            have same : child = x := Fin.ext atX
            subst child
            decide +kernel))
          (inputs xyRoot (by
            have same : child = x := Fin.ext atX
            subst child
            decide +kernel))
      else if atY : child.val = 1 then
        Bool.xor (parents x (by simp [signature, x, atY]))
          (Bool.xor
            (inputs xyRoot (by
              have same : child = y := Fin.ext atY
              subst child
              decide +kernel))
            (inputs yzRoot (by
              have same : child = y := Fin.ext atY
              subst child
              decide +kernel)))
      else
        let atZ : child.val = 2 := by
          have bounded : child.val < 3 := child.isLt
          omega
        Bool.xor
          (inputs xzRoot (by
            have same : child = z := Fin.ext atZ
            subst child
            decide +kernel))
          (inputs yzRoot (by
            have same : child = z := Fin.ext atZ
            subst child
            decide +kernel)) }

theorem source_compatible : Compatible sourceModel projection.observedGraph :=
  noiseModel_compatible

/-- Construct the entire full hidden-DAG SCM, including finite hidden-domain
presentations, declared-parent-only equations and actual independent noise. -/
def realized : FiniteHiddenDAGSCM signature projection :=
  sourceModel.toHiddenDAGSCM source_compatible

def allTrueRoots : sourceModel.latent.Assignment := fun _ => true

def encodedNoise : realized.NoiseAssignment :=
  HiddenDAGPlacedNoise.encode sourceModel source_compatible allTrueRoots

def forceXTrue : HardIntervention signature :=
  (HardIntervention.empty signature).set x true

theorem factual_source_y : sourceModel.eval allTrueRoots y = false := by
  decide +kernel

theorem forced_source_y : sourceModel.evalUnder forceXTrue.value allTrueRoots y = true := by
  decide +kernel

/-- The original-DAG factual evaluation reproduces the source equation at
this explicit encoded unit, without an external preservation interface. -/
theorem factual_realized_y :
    realized.evalObserved (HardIntervention.empty signature) encodedNoise y = false := by
  decide +kernel

/-- The observed parent signal survives its intervention through `X,V,Y`.
The relay reads actual full-DAG parent values, not the old source's factual
equation for `X`.  Shared channels still come from `U`, not fresh `V` noise. -/
theorem forced_realized_y :
    realized.evalObserved forceXTrue encodedNoise y = true := by
  decide +kernel

/-- Exhaust the observed coordinates at this intervention; the unrelated
`Z` and the forced `X` are checked as well as the hidden-relay recipient `Y`. -/
theorem forced_observed_values_agree : forall index : Fin signature.count,
    realized.evalObserved forceXTrue encodedNoise index =
      sourceModel.evalUnder forceXTrue.value allTrueRoots index := by
  decide +kernel

/-- A hidden node uses a genuine finite pair of signal vectors.  This is
the constructor's declared domain, not a restricted singleton witness. -/
theorem hidden_u_value_domain :
    realized.NodeValue u = HiddenDAGRelay.Payload sourceModel := by
  change HiddenDAGRelay.NodeValue sourceModel projection u = HiddenDAGRelay.Payload sourceModel
  exact HiddenDAGRelay.nodeValue_of_none (P := projection) sourceModel u (by decide +kernel)

end HiddenDAGRealization
end Examples
end Causality
end Thesis
