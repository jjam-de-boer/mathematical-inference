import Thesis.Probability.Distros.Basic

namespace Thesis
namespace Probability
namespace Distros

/-!
Categorical and discrete-uniform distros.

A categorical distro is a finite labelled urn: each index `i : Fin n` carries
a natural weight.  Discrete uniform is the special case in which every cell
has weight one, so the probability of each singleton is `1/n`.
-/

open Combinatorics

theorem natSum_ones (n : Nat) :
    natSum n (fun _ => 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natSum, ih]

theorem finWeight_one (n : Nat) :
    natSum n (finWeight (fun _ : Fin n => 1)) = n := by
  have hcongr :
      natSum n (finWeight (fun _ : Fin n => 1)) = natSum n (fun _ => 1) := by
    apply natSum_congr
    intro i hi
    simp [finWeight, hi]
  rw [hcongr, natSum_ones]

/-- Categorical distro with one atom per finite index. -/
def categoricalDistro (n : Nat) (weights : Fin n → Nat)
    (positive : 0 < natSum n (finWeight weights)) : Distro (Fin n) where
  record := ofFinWeights n weights positive

/-- Discrete uniform distro on `n` labelled cells, requiring `0 < n`. -/
def discreteUniformDistro (n : Nat) (positive : 0 < n) : Distro (Fin n) :=
  categoricalDistro n (fun _ => 1) (by
    have h : natSum n (finWeight (fun _ : Fin n => 1)) = n := finWeight_one n
    simpa [h] using positive)

theorem discreteUniform_den (n : Nat) (positive : 0 < n) :
    (discreteUniformDistro n positive).record.den = n := by
  simp [discreteUniformDistro, categoricalDistro, ofFinWeights,
    totalMass_finWeighted, finWeight_one]

theorem categorical_pmf (n : Nat) (weights : Fin n → Nat)
    (positive : 0 < natSum n (finWeight weights)) (value : Fin n) :
    QProb.Equiv
      ((categoricalDistro n weights positive).pmf value)
      ⟨weights value, (categoricalDistro n weights positive).record.den,
        (categoricalDistro n weights positive).record.den_pos⟩ := by
  simp [Distro.pmf, categoricalDistro, ofFinWeights, FiniteProbRecord.probVal,
    QProb.Equiv, eventMass_finWeighted_singleton]

theorem discreteUniform_pmf (n : Nat) (positive : 0 < n) (value : Fin n) :
    QProb.Equiv
      ((discreteUniformDistro n positive).pmf value)
      ⟨1, n, positive⟩ := by
  have hpmf := categorical_pmf n (fun _ => 1)
      (by simpa [finWeight_one] using positive) value
  have hden := discreteUniform_den n positive
  simp [discreteUniformDistro] at hden
  exact QProb.equiv_trans hpmf (by
    simp [QProb.Equiv, hden])

end Distros
end Probability
end Thesis
