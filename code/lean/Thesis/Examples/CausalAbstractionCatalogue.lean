import Thesis.Examples.CausalAbstractionScale
import Thesis.CausalTransport.CatalogueInference

namespace Thesis.Examples.CausalAbstraction
open Probability Probability.Distros Causality CatalogueInference

/-!
A client of the existing catalogue engine. A common observed table can be
compared across different finite SCM signatures by supplying a readout and
an experimental action for each candidate. These protocols are explicit
hypothesis data, not inferred intervention correspondences.

The partial fine action do(X₁=true) has no image under the exact AND ω.
The cheap macro candidate here declares an unforced cause for that protocol.
Its root mass stays 1/4 while the fine coarse readout has mass 1/2. Data
therefore reject that candidate/protocol pair. This does not refute the
exact AND abstraction on its allowed domain, nor infer a unique causal DAG.
-/

/-- Heterogeneous actual SCMs sharing a finite observation interface.
An action outside the exact abstraction domain must be declared explicitly;
this adapter never converts `omega = none` to an empty do. -/
structure ScaleCandidate (observed : ObservedSignature.{0}) where
  signature : ObservedSignature.{0}
  model : ExactModel signature
  complexity : Nat
  readout : signature.Assignment → observed.Assignment
  action : HardIntervention signature

/-- Existing Regime A likelihood, applied to actual SCM predictions after
an explicit observation map. No likelihood or posterior engine is replaced. -/
def ScaleCandidate.weight (candidate : ScaleCandidate observed)
    (data : FiniteProbRecord observed.Assignment) : Nat :=
  regimeAWeight ((predictedTable candidate.model (.intervene candidate.action)).map candidate.readout) (.law data)

def partialFineAction : HardIntervention microSignature := fineAction (some true) none none

def partialFineData : FiniteProbRecord microSignature.Assignment :=
  predictedTable microModel (.intervene partialFineAction)

def partialCoarseData : FiniteProbRecord macroSignature.Assignment :=
  partialFineData.map (mergeAssignment Bool.and)

/-- Each finite label exposes its actual SCM, complexity, readout and
protocol through this accessor. Signatures may differ between labels. -/
def Grain.candidate : Grain → ScaleCandidate macroSignature
  | .fine =>
    { signature := Grain.fine.signature
      model := Grain.fine.model
      complexity := Grain.fine.complexity
      readout := mergeAssignment Bool.and
      action := partialFineAction }
  | .merged =>
    { signature := Grain.merged.signature
      model := Grain.merged.model
      complexity := Grain.merged.complexity
      readout := id
      action := coarseAction none none }
  | .collapsed =>
    { signature := Grain.collapsed.signature
      model := Grain.collapsed.model
      complexity := Grain.collapsed.complexity
      readout := fun state => coarseState (state (0 : Fin 1)) (state (0 : Fin 1))
      action := terminalAction none }

/-- The scored list contains the fine and the first merged grain. -/
def scaleCandidates : List Grain := [.fine, .merged]

theorem catalogue_uses_depth_one : scaleCandidates = scaleFamily 1 := rfl

def scaleCatalogue : Catalogue scaleCandidates.length Grain :=
  ofListByComplexity scaleCandidates (fun i => (scaleCandidates.get i).complexity) 3 (by decide +kernel)

def scaleWeights (i : Fin scaleCandidates.length) : Nat :=
  (scaleCatalogue.item i).candidate.weight partialCoarseData

private theorem scaleEvidencePositive : 0 < natIntegral scaleCatalogue.prior.record.atoms scaleWeights := by
  decide +kernel

/-- The posterior is constructed only with a proved positive evidence mass. -/
def scalePosterior : Distro (Fin scaleCandidates.length) :=
  scaleCatalogue.prior.reweightNat scaleWeights scaleEvidencePositive

theorem partial_intervention_outside_exact_domain : andOmega partialFineAction = none := rfl

/-- The data distinguish 1/2 from the macro protocol's 1/4. -/
theorem scale_predicted_masses :
    QProb.Equiv (partialCoarseData.probVal macroTrue) ⟨1, 2, by decide⟩ ∧
    QProb.Equiv ((predictedTable andMacro (.intervene (coarseAction none none))).probVal macroTrue)
      ⟨1, 4, by decide⟩ := by decide +kernel

/-- The native SCM Regime A function agrees: fine matches its measured fine
table, and the macro candidate fails the supplied common coarse table. -/
theorem scale_native_weights :
    regimeAModelWeight microModel [interveneExperiment partialFineAction (.law partialFineData)] = 1 ∧
    regimeAModelWeight andMacro [interveneExperiment (coarseAction none none) (.law partialCoarseData)] = 0 ∧
    scaleWeights ⟨0, by decide⟩ = 1 ∧ scaleWeights ⟨1, by decide⟩ = 0 := by decide +kernel

/-- Complexity prefers the cheap macro before data: masses 2/3 vs 1/3. -/
theorem scale_complexity_prior :
    QProb.Equiv (scaleCatalogue.prior.pmf ⟨0, by decide⟩) ⟨1, 3, by decide⟩ ∧
    QProb.Equiv (scaleCatalogue.prior.pmf ⟨1, by decide⟩) ⟨2, 3, by decide⟩ := by decide +kernel

/-- Actual posterior movement, using the existing supported update. -/
theorem scale_posterior_moves :
    posterior? scaleCatalogue.prior scaleWeights = some scalePosterior ∧
    catalogueExhausted scaleCatalogue.prior scaleWeights = false ∧
    QProb.Equiv (scalePosterior.pmf ⟨0, by decide⟩) QProb.one ∧
    QProb.Equiv (scalePosterior.pmf ⟨1, by decide⟩) QProb.zero := by
  constructor
  · unfold posterior?
    rw [dif_pos scaleEvidencePositive]
    rfl
  · decide +kernel

end Thesis.Examples.CausalAbstraction
