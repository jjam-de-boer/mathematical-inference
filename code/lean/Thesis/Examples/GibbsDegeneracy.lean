import Thesis.Probability.FinitePhysicalDegeneracy

namespace Thesis.Examples.GibbsDegeneracy
open Probability ConstructiveReal
open Probability.Distros.RationalLinear
open ConstructiveReal.FiniteFibers

/-- Three distinct physical states: two have energy zero and one has energy
one in an unreduced presentation. Particle number is fixed. -/
private def model : FinitePhysicalModel 3 := {
  nonempty := by decide
  energy i := if i = 2 then ⟨2, 2, by decide⟩ else SignedRatio.zero
  particles _ := 1 }
private def original : FiniteGibbsFamily 3 1 :=
  ⟨model.nonempty, (fun _ => PositiveRatio.one), (fun _ i => model.energy i)⟩
private def grouping : FiniteGibbsGrouping 3 2 1 := {
  nonempty := by decide
  states := {
    label i := if i = 2 then 1 else 0
    representative j := if j = 0 then 0 else 2
    covers := by decide +kernel }
  response _ j := if j = 0 then SignedRatio.zero else SignedRatio.one }
private theorem compatible : grouping.Compatible original := ⟨by decide +kernel, by decide +kernel⟩

example : grouping.states.degeneracy (0 : Fin 2) = 2 := by decide +kernel
example : grouping.states.degeneracy (1 : Fin 2) = 1 := by decide +kernel
example (i : Fin 3) : model.particles i = 1 := rfl
private def computedGrouping := FiniteStateGrouping.ofSurjective grouping.states.label (by decide +kernel)
example : computedGrouping.representative (0 : Fin 2) = (0 : Fin 3) := by decide +kernel
example : computedGrouping.representative (1 : Fin 2) = (2 : Fin 3) := by decide +kernel

/-- The grouping theorem applies to the actual original family, without
changing unreduced energy values or assuming the desired aggregation. -/
example (beta : ConstructiveReal) (j : Fin 2) :
    Equiv (sumFiber grouping.states.label (original.mass (fun _ => beta)) j)
      (grouping.macroFamily.mass (fun _ => beta) j) := compatible.mass_aggregated (fun _ => beta) j

private def parameters : Fin 1 → ConstructiveReal := fun _ => lnTwo
private def half : SignedRatio := ⟨1, 2, by decide⟩
private def two : PositiveRatio := .ofNat 2 (by decide)
private def fiveHalves : SignedRatio := ⟨5, 2, by decide⟩
private def twoFifths : SignedRatio := ⟨2, 5, by decide⟩
private def fourFifths : SignedRatio := ⟨4, 5, by decide⟩
private def oneFifth : SignedRatio := ⟨1, 5, by decide⟩

private theorem exp_lnTwo : Equiv lnTwo.exp (ofSignedRatio two.toSignedRatio) :=
  equiv_trans (exp_congr (equiv_symm (positiveLn_two two (le_refl _)))) (exp_positiveLn _ two (le_refl _))
private theorem exp_neg_lnTwo : Equiv (neg lnTwo).exp (ofSignedRatio half) :=
  inverse_unique (ofSignedRatio two.toSignedRatio) _ _
    (equiv_trans (mul_congr (equiv_symm exp_lnTwo) (equiv_refl _)) (exp_mul_exp_neg lnTwo))
    (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))

private theorem base0 : Equiv (grouping.baseWeight parameters (0 : Fin 2)) one := by
  have score : Equiv (grouping.macroFamily.score parameters (0 : Fin 2)) zero :=
    equiv_trans (add_congr (zero_mul lnTwo) (equiv_refl zero)) (zero_add zero)
  exact equiv_trans (exp_congr (equiv_trans (neg_congr score) (equiv_symm (ofSignedRatio_neg SignedRatio.zero)))) exp_zero
private theorem base1 : Equiv (grouping.baseWeight parameters (1 : Fin 2)) (ofSignedRatio half) := by
  have score : Equiv (grouping.macroFamily.score parameters (1 : Fin 2)) lnTwo :=
    equiv_trans (add_congr (one_mul lnTwo) (equiv_refl zero)) (add_zero lnTwo)
  exact equiv_trans (exp_congr (neg_congr score)) exp_neg_lnTwo
private theorem macro_weight0 : Equiv ((grouping.macroFamily.asTilt parameters).weight one (0 : Fin 2)) (ofSignedRatio two.toSignedRatio) :=
  equiv_trans (grouping.macro_weight parameters 0) (equiv_trans (mul_congr (equiv_refl _) base0) (mul_one _))
private theorem macro_weight1 : Equiv ((grouping.macroFamily.asTilt parameters).weight one (1 : Fin 2)) (ofSignedRatio half) :=
  equiv_trans (grouping.macro_weight parameters 1) (equiv_trans (mul_congr (equiv_refl _) base1) (one_mul _))

private theorem partition_exact : Equiv (grouping.macroFamily.partition parameters) (ofSignedRatio fiveHalves) := by
  change Equiv (add ((grouping.macroFamily.asTilt parameters).weight one 0)
    (add ((grouping.macroFamily.asTilt parameters).weight one 1) zero)) _
  exact equiv_trans (add_congr macro_weight0 (equiv_trans (add_congr macro_weight1 (equiv_refl _)) (add_zero _)))
    (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))
private theorem inverse_exact : Equiv ((grouping.macroFamily.asTilt parameters).partitionInverse one) (ofSignedRatio twoFifths) :=
  inverse_unique (grouping.macroFamily.partition parameters) _ _
    ((grouping.macroFamily.partition parameters).mul_positiveInverse _ ((grouping.macroFamily.asTilt parameters).partition_positive one))
    (equiv_trans (mul_congr partition_exact (equiv_refl _))
      (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))
private theorem macro_mass0 : Equiv (grouping.macroFamily.mass parameters (0 : Fin 2)) (ofSignedRatio fourFifths) :=
  equiv_trans (mul_congr macro_weight0 inverse_exact)
    (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))
private theorem macro_mass1 : Equiv (grouping.macroFamily.mass parameters (1 : Fin 2)) (ofSignedRatio oneFifth) :=
  equiv_trans (mul_congr macro_weight1 inverse_exact)
    (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))

private theorem original_inverse : Equiv ((original.asTilt parameters).partitionInverse one) (ofSignedRatio twoFifths) :=
  equiv_trans (positiveInverse_congr (compatible.partition_eq parameters) _ _
    ((original.asTilt parameters).partition_positive one) ((grouping.macroFamily.asTilt parameters).partition_positive one)) inverse_exact
private theorem original_weight (i : Fin 3) : Equiv ((original.asTilt parameters).weight one i)
    (grouping.baseWeight parameters (grouping.states.label i)) :=
  equiv_trans (exp_congr (compatible.logWeight parameters i)) (grouping.micro_weight parameters i)
example : Equiv (original.mass parameters (0 : Fin 3)) (ofSignedRatio twoFifths) :=
  equiv_trans (mul_congr (equiv_trans (original_weight 0) base0) original_inverse) (one_mul _)
example : Equiv (original.mass parameters (1 : Fin 3)) (ofSignedRatio twoFifths) :=
  equiv_trans (mul_congr (equiv_trans (original_weight 1) base0) original_inverse) (one_mul _)
example : Equiv (original.mass parameters (2 : Fin 3)) (ofSignedRatio oneFifth) :=
  equiv_trans (mul_congr (equiv_trans (original_weight 2) base1) original_inverse)
    (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))

/-- The actual aggregated masses are 4/5 and 1/5. The lower-energy fiber
contains two physical states, each contributing 2/5 to its aggregate. -/
example : Equiv (sumFiber grouping.states.label (original.mass parameters) (0 : Fin 2)) (ofSignedRatio fourFifths) :=
  equiv_trans (compatible.mass_aggregated parameters 0) macro_mass0
example : Equiv (sumFiber grouping.states.label (original.mass parameters) (1 : Fin 2)) (ofSignedRatio oneFifth) :=
  equiv_trans (compatible.mass_aggregated parameters 1) macro_mass1

private theorem log0 : Equiv (grouping.logDegeneracy (0 : Fin 2)) one :=
  equiv_trans (positiveLog2_ofPositiveRatio (grouping.states.reference 0) (grouping.states.reference 0) (le_refl _))
    (ExactLog.interpret_ofSignedRatio SignedRatio.one)
private theorem log1 : Equiv (grouping.logDegeneracy (1 : Fin 2)) zero :=
  positiveLog2_one PositiveRatio.one (le_refl one)
private theorem correction_exact : Equiv (grouping.macroFamily.expectation parameters grouping.logDegeneracy) (ofSignedRatio fourFifths) := by
  have selector (j : Fin 2) : Equiv (grouping.logDegeneracy j) (realInteger (if j = 0 then 1 else 0)) := by
    have cases := (by decide +kernel : ∀ k : Fin 2, k = 0 ∨ k = 1) j
    rcases cases with rfl | rfl
    · exact log0
    · exact log1
  exact equiv_trans ((grouping.macroFamily.asTilt parameters).expectation_congr one _ _ selector)
    (equiv_trans (FiniteLinear.pair_unit 2 0 (grouping.macroFamily.mass parameters)) macro_mass0)

/-- The entropy correction is independently recovered as 4/5 bit, from the
computed macrostate masses and actual log multiplicities (1 and 0). -/
example : Equiv (original.entropy parameters) (add (grouping.macroFamily.entropy parameters) (ofSignedRatio fourFifths)) :=
  equiv_trans (compatible.entropy_correction parameters) (add_congr (equiv_refl _) correction_exact)

example (boltzmann : PositiveRatio) : Equiv
    (FiniteStatisticalMechanics.statisticalEntropy boltzmann (original.entropy parameters))
    (add (FiniteStatisticalMechanics.statisticalEntropy boltzmann (grouping.macroFamily.entropy parameters))
      (mul (ofSignedRatio boltzmann.toSignedRatio) (mul (ofSignedRatio fourFifths) lnTwo))) :=
  equiv_trans (compatible.physical_entropy_correction parameters boltzmann)
    (add_congr (equiv_refl _) (mul_congr (equiv_refl _)
      (equiv_trans (grouping.degeneracy_mean_units parameters) (mul_congr correction_exact (equiv_refl _)))))

end Thesis.Examples.GibbsDegeneracy
