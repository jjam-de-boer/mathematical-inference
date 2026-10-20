import Thesis.Probability.Distros.OccupancyRank

namespace Thesis.Probability.Distros
open RationalVector

/-- Zero trials annihilate every covariance direction, including null
categories. These results identify the full operator, not only its quadratic form. -/
theorem multinomial_zero_covarianceOperator (weights : List Nat) (positive : 0 < weights.sum) (coefficients : Vector weights.length) :
    Equiv (((multinomialDistro 0 weights positive).occupancyOperator weights.length).apply coefficients) zero :=
  ((multinomialDistro 0 weights positive).occupancyOperator_kernel_iff_rows weights.length coefficients).mpr
    ((multinomial_covarianceRows_zero_iff 0 weights positive (natCoefficients coefficients)).mpr (Or.inl rfl))

theorem reinforcedCount_zero_covarianceOperator (increment : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (coefficients : Vector weights.length) :
    Equiv (((reinforcedCountDistro 0 weights increment positive).occupancyOperator weights.length).apply coefficients) zero :=
  ((reinforcedCountDistro 0 weights increment positive).occupancyOperator_kernel_iff_rows weights.length coefficients).mpr
    ((reinforcedCount_covarianceRows_zero_iff 0 increment weights positive (natCoefficients coefficients)).mpr (Or.inl rfl))

theorem multivariateHypergeometric_zero_covarianceOperator (stocks : List Nat)
    (positive : 0 < Combinatorics.binom stocks.sum 0) (coefficients : Vector stocks.length) :
    Equiv (((multivariateHypergeometricDistro 0 stocks positive).occupancyOperator stocks.length).apply coefficients) zero :=
  ((multivariateHypergeometricDistro 0 stocks positive).occupancyOperator_kernel_iff_rows stocks.length coefficients).mpr
    ((multivariateHypergeometric_covarianceRows_zero_iff 0 stocks positive (natCoefficients coefficients)).mpr (Or.inl rfl))

/-- Taking the entire population leaves a deterministic count vector. The
empty population is included, with an empty ambient coordinate space. -/
theorem multivariateHypergeometric_full_covarianceOperator (stocks : List Nat)
    (positive : 0 < Combinatorics.binom stocks.sum stocks.sum) (coefficients : Vector stocks.length) :
    Equiv (((multivariateHypergeometricDistro stocks.sum stocks positive).occupancyOperator stocks.length).apply coefficients) zero :=
  ((multivariateHypergeometricDistro stocks.sum stocks positive).occupancyOperator_kernel_iff_rows stocks.length coefficients).mpr
    ((multivariateHypergeometric_covarianceRows_zero_iff stocks.sum stocks positive (natCoefficients coefficients)).mpr (Or.inr (Or.inl rfl)))

def multinomial_covarianceRank_zero (weights : List Nat) (positive : 0 < weights.sum) :
    RankCertificate ((multinomialDistro 0 weights positive).occupancyOperator weights.length) 0 :=
  zeroRank _ (multinomial_zero_covarianceOperator weights positive)

def reinforcedCount_covarianceRank_zero (increment : Nat) (weights : List Nat) (positive : 0 < weights.sum) :
    RankCertificate ((reinforcedCountDistro 0 weights increment positive).occupancyOperator weights.length) 0 :=
  zeroRank _ (reinforcedCount_zero_covarianceOperator increment weights positive)

def multivariateHypergeometric_covarianceRank_zero (stocks : List Nat) (positive : 0 < Combinatorics.binom stocks.sum 0) :
    RankCertificate ((multivariateHypergeometricDistro 0 stocks positive).occupancyOperator stocks.length) 0 :=
  zeroRank _ (multivariateHypergeometric_zero_covarianceOperator stocks positive)

def multivariateHypergeometric_covarianceRank_full (stocks : List Nat) (positive : 0 < Combinatorics.binom stocks.sum stocks.sum) :
    RankCertificate ((multivariateHypergeometricDistro stocks.sum stocks positive).occupancyOperator stocks.length) 0 :=
  zeroRank _ (multivariateHypergeometric_full_covarianceOperator stocks positive)

/-- In the degenerate cases the full standard coordinate basis spans the
kernel; no constant-direction restriction remains. -/
def multinomial_covarianceKernelBasis_zero (weights : List Nat) (positive : 0 < weights.sum) :=
  zeroKernelBasis ((multinomialDistro 0 weights positive).occupancyOperator weights.length)
    (multinomial_zero_covarianceOperator weights positive)

def reinforcedCount_covarianceKernelBasis_zero (increment : Nat) (weights : List Nat) (positive : 0 < weights.sum) :=
  zeroKernelBasis ((reinforcedCountDistro 0 weights increment positive).occupancyOperator weights.length)
    (reinforcedCount_zero_covarianceOperator increment weights positive)

def multivariateHypergeometric_covarianceKernelBasis_zero (stocks : List Nat) (positive : 0 < Combinatorics.binom stocks.sum 0) :=
  zeroKernelBasis ((multivariateHypergeometricDistro 0 stocks positive).occupancyOperator stocks.length)
    (multivariateHypergeometric_zero_covarianceOperator stocks positive)

def multivariateHypergeometric_covarianceKernelBasis_full (stocks : List Nat) (positive : 0 < Combinatorics.binom stocks.sum stocks.sum) :=
  zeroKernelBasis ((multivariateHypergeometricDistro stocks.sum stocks positive).occupancyOperator stocks.length)
    (multivariateHypergeometric_full_covarianceOperator stocks positive)

end Thesis.Probability.Distros
