import Thesis.CausalTransport.ModelDescriptionCost
import Thesis.Examples.CausalAbstractionInverse

/-! # Dense model costs and class priors on concrete finite descriptions -/

namespace Thesis.Examples.ModelDescriptionCost

open Probability Probability.Distros Causality
open Causality.ModelDescriptionCost CatalogueInference FiniteSymmetry

private def labels : FiniteWitness Bool :=
  FiniteWitness.ofList [false, true] (by intro value; cases value <;> simp) (by decide)

private def reversed : FiniteWitness Bool :=
  FiniteWitness.ofList [true, false] (by intro value; cases value <;> simp) (by decide)

private def flip : ValueEquivalence Bool Bool :=
  ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

private def fair : Distro Bool :=
  ⟨⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩⟩

private def split : Distro Bool :=
  ⟨⟨[(false, 1), (false, 1), (true, 2)], 4, by decide, rfl⟩⟩

private theorem fair_split : fair.SameLaw split := by
  intro event
  cases hFalse : event false <;> cases hTrue : event true <;>
    simp [fair, split, FiniteProbRecord.probVal, FiniteProbRecord.eventMass,
      QProb.Equiv, hFalse, hTrue]

/-- Unreduced halves and duplicate occurrences both disappear before the
digit score, and relabelling can reorder the declared alphabet. -/
theorem same_distribution_cost :
    distributionCost labels fair = distributionCost reversed (split.map flip.forward) :=
  (distributionCost_sameLaw labels fair_split).trans
    (distributionCost_relabel labels reversed flip split)

theorem fair_cost : distributionCost labels fair = 8 := by decide +kernel

/-- Two observed vertices, one shared latent source, one directed edge, two
latent incidences, four treatment rows, and eight outcome rows. -/
theorem dense_bow_cost :
    (Layout.ofModel (Thesis.Examples.CausalAbstractionInverse.pairedModel false)).cost = 18 := by
  decide +kernel

private def classCost (label : Bool) : Nat := if label then 1 else 0

private theorem positive : 0 < natIntegral fair.record.atoms
    (fun label => complexityWeight 1 (classCost label)) := by decide +kernel

private def twoClass (i : Fin 2) : Bool := i.val == 1
private def threeClass (i : Fin 3) : Bool := i.val == 2

private theorem twoRepresented : ∀ c, ∃ i, twoClass i = c := by decide +kernel
private theorem threeRepresented : ∀ c, ∃ i, threeClass i = c := by decide +kernel

private def two := classComplexityCatalogue twoClass fair classCost 1 positive twoClass twoRepresented
private def three := classComplexityCatalogue threeClass fair classCost 1 positive threeClass threeRepresented

/-- The cheaper class gets two thirds of the prior both before and after
adding a second encoding of that class. -/
theorem duplicate_encoding_keeps_class_mass :
    QProb.Equiv ((aggregateClasses two.prior twoClass).pmf false) ⟨2, 3, by decide⟩ ∧
    QProb.Equiv ((aggregateClasses three.prior threeClass).pmf false) ⟨2, 3, by decide⟩ := by
  constructor <;> decide +kernel

end Thesis.Examples.ModelDescriptionCost
