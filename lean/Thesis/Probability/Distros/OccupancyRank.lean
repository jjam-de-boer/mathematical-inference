import Thesis.Probability.Distros.CovarianceOperator
import Thesis.Probability.Distros.RationalKernelBasis

namespace Thesis.Probability.Distros
open RationalVector

/-- The genuine covariance matrix of the displayed count coordinates. -/
def Distro.occupancyOperator (μ : Distro (List Nat)) (colours : Nat) : Operator colours colours :=
  μ.covarianceOperator (fun i => countResponse i.val)

def positiveColours (weights : List Nat) (i : Fin weights.length) : Bool := decide (0 < weights.getD i.val 0)
def positiveColourCount (weights : List Nat) : Nat := (positiveIndices (positiveColours weights)).length

/-- Select a positive coordinate by recursion on the actual weights. No
choice principle is used to extract an index from an existential statement. -/
def positiveColourIndex : (weights : List Nat) → 0 < weights.sum →
    {i : Fin weights.length // positiveColours weights i = true}
  | [], positive => False.elim (by change 0 < 0 at positive; omega)
  | weight :: weights, positive =>
      if first : 0 < weight then
        ⟨⟨0, by simp only [List.length_cons]; omega⟩, by change decide (0 < weight) = true; exact decide_eq_true first⟩
      else
        let previous := positiveColourIndex weights (by simp only [List.sum_cons] at positive; omega)
        ⟨previous.val.succ, by change decide (0 < weights.getD previous.val.val 0) = true; exact previous.property⟩

theorem Distro.occupancyOperator_kernel_iff_rows (μ : Distro (List Nat)) (colours : Nat) (coefficients : Vector colours) :
    (μ.occupancyOperator colours).Kernel coefficients ↔
      ∀ i ∈ List.range colours, SignedRatio.Equiv
        (μ.rationalCovarianceRow (List.range colours) countResponse (natCoefficients coefficients) i) SignedRatio.zero := by
  constructor
  · intro null i member
    let index : Fin colours := ⟨i, List.mem_range.mp member⟩
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.covarianceOperator_nat_row countResponse coefficients index)) (null index)
  · intro rows i
    exact SignedRatio.equiv_trans (μ.covarianceOperator_nat_row countResponse coefficients i)
      (rows i.val (List.mem_range.mpr i.isLt))

theorem coefficientsConstant_iff (weights : List Nat) (coefficients : Vector weights.length) :
    CoefficientsConstantOnPositive weights (natCoefficients coefficients) ↔ ConstantOn (positiveColours weights) coefficients := by
  constructor
  · rintro ⟨constant, same⟩
    refine ⟨constant, ?_⟩
    intro i positive
    have equal := same i.val i.isLt (of_decide_eq_true positive)
    rw [natCoefficients_fin] at equal
    exact equal
  · rintro ⟨constant, same⟩
    refine ⟨constant, ?_⟩
    intro i within positive
    let index : Fin weights.length := ⟨i, within⟩
    have equal := same index (decide_eq_true positive)
    change SignedRatio.Equiv (natCoefficients coefficients index.val) constant
    rw [natCoefficients_fin]
    exact equal

theorem multinomial_occupancyKernel (n : Nat) (weights : List Nat) (positive : 0 < weights.sum) (nonzero : 0 < n)
    (coefficients : Vector weights.length) :
    ((multinomialDistro n weights positive).occupancyOperator weights.length).Kernel coefficients ↔
      ConstantOn (positiveColours weights) coefficients := by
  have criterion := ((multinomialDistro n weights positive).occupancyOperator_kernel_iff_rows weights.length coefficients).trans
    (multinomial_covarianceRows_zero_iff n weights positive (natCoefficients coefficients))
  constructor
  · intro null
    rcases criterion.mp null with zero | constant
    · omega
    · exact (coefficientsConstant_iff weights coefficients).mp constant
  · intro constant
    exact criterion.mpr (Or.inr ((coefficientsConstant_iff weights coefficients).mpr constant))

theorem reinforcedCount_occupancyKernel (n increment : Nat) (weights : List Nat) (positive : 0 < weights.sum) (nonzero : 0 < n)
    (coefficients : Vector weights.length) :
    ((reinforcedCountDistro n weights increment positive).occupancyOperator weights.length).Kernel coefficients ↔
      ConstantOn (positiveColours weights) coefficients := by
  have criterion := ((reinforcedCountDistro n weights increment positive).occupancyOperator_kernel_iff_rows weights.length coefficients).trans
    (reinforcedCount_covarianceRows_zero_iff n increment weights positive (natCoefficients coefficients))
  constructor
  · intro null
    rcases criterion.mp null with zero | constant
    · omega
    · exact (coefficientsConstant_iff weights coefficients).mp constant
  · intro constant
    exact criterion.mpr (Or.inr ((coefficientsConstant_iff weights coefficients).mpr constant))

theorem multivariateHypergeometric_occupancyKernel (n : Nat) (stocks : List Nat)
    (positive : 0 < Combinatorics.binom stocks.sum n) (nonzero : 0 < n) (proper : n < stocks.sum)
    (coefficients : Vector stocks.length) :
    ((multivariateHypergeometricDistro n stocks positive).occupancyOperator stocks.length).Kernel coefficients ↔
      ConstantOn (positiveColours stocks) coefficients := by
  have criterion := ((multivariateHypergeometricDistro n stocks positive).occupancyOperator_kernel_iff_rows stocks.length coefficients).trans
    (multivariateHypergeometric_covarianceRows_zero_iff n stocks positive (natCoefficients coefficients))
  constructor
  · intro null
    rcases criterion.mp null with zero | full | constant
    · omega
    · omega
    · exact (coefficientsConstant_iff stocks coefficients).mp constant
  · intro constant
    exact criterion.mpr (Or.inr (Or.inr ((coefficientsConstant_iff stocks coefficients).mpr constant)))

/-- Explicit image basis and rank r-1 for a nonzero multinomial trial count. -/
def multinomial_covarianceRank (n : Nat) (weights : List Nat) (positive : 0 < weights.sum) (nonzero : 0 < n) :
    RankCertificate ((multinomialDistro n weights positive).occupancyOperator weights.length) (positiveColourCount weights - 1) :=
  contrastRank _ _ (positiveColourIndex weights positive).val (positiveColourIndex weights positive).property
    (multinomial_occupancyKernel n weights positive nonzero)

def multinomial_covarianceKernelBasis (n : Nat) (weights : List Nat) (positive : 0 < weights.sum) (nonzero : 0 < n) :=
  constantKernelBasis ((multinomialDistro n weights positive).occupancyOperator weights.length) (positiveColours weights)
    (positiveColourIndex weights positive).val (positiveColourIndex weights positive).property (multinomial_occupancyKernel n weights positive nonzero)

/-- Natural reinforcement changes covariance scale, while the same positive
coordinate columns remain an independent spanning image basis. -/
def reinforcedCount_covarianceRank (n increment : Nat) (weights : List Nat) (positive : 0 < weights.sum) (nonzero : 0 < n) :
    RankCertificate ((reinforcedCountDistro n weights increment positive).occupancyOperator weights.length) (positiveColourCount weights - 1) :=
  contrastRank _ _ (positiveColourIndex weights positive).val (positiveColourIndex weights positive).property
    (reinforcedCount_occupancyKernel n increment weights positive nonzero)

def reinforcedCount_covarianceKernelBasis (n increment : Nat) (weights : List Nat) (positive : 0 < weights.sum) (nonzero : 0 < n) :=
  constantKernelBasis ((reinforcedCountDistro n weights increment positive).occupancyOperator weights.length) (positiveColours weights)
    (positiveColourIndex weights positive).val (positiveColourIndex weights positive).property
    (reinforcedCount_occupancyKernel n increment weights positive nonzero)

/-- Proper nonempty sampling has rank r-1 for the positive-stock colours. -/
def multivariateHypergeometric_covarianceRank (n : Nat) (stocks : List Nat)
    (positive : 0 < Combinatorics.binom stocks.sum n) (nonzero : 0 < n) (proper : n < stocks.sum) :
    RankCertificate ((multivariateHypergeometricDistro n stocks positive).occupancyOperator stocks.length) (positiveColourCount stocks - 1) :=
  contrastRank _ _ (positiveColourIndex stocks (by omega)).val (positiveColourIndex stocks (by omega)).property
    (multivariateHypergeometric_occupancyKernel n stocks positive nonzero proper)

def multivariateHypergeometric_covarianceKernelBasis (n : Nat) (stocks : List Nat)
    (positive : 0 < Combinatorics.binom stocks.sum n) (nonzero : 0 < n) (proper : n < stocks.sum) :=
  constantKernelBasis ((multivariateHypergeometricDistro n stocks positive).occupancyOperator stocks.length) (positiveColours stocks)
    (positiveColourIndex stocks (by omega)).val (positiveColourIndex stocks (by omega)).property
    (multivariateHypergeometric_occupancyKernel n stocks positive nonzero proper)

end Thesis.Probability.Distros
