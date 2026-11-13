import Thesis.Probability.Distros.LawEquivalence

namespace Thesis.Probability.Distros
open Combinatorics

/-! Point masses, their moments, and recognition of a single supported cell. -/

def Distro.pointMass (value : Ω) : Distro Ω :=
  ⟨⟨[(value, 1)], 1, Nat.zero_lt_one, rfl⟩⟩

theorem pointMass_mean (value : Ω) (embed : Ω → Nat) :
    QProb.Equiv (mean (⟨Distro.pointMass value, embed⟩ : NatDistro Ω)) (QProb.ofNat (embed value)) := by
  simp only [mean_expectNat, Distro.expectNat, Distro.pointMass, natIntegral,
    QProb.Equiv, QProb.ofNat, Nat.one_mul, Nat.mul_one, Nat.add_zero]

theorem pointMass_variance (value : Ω) (embed : Ω → Nat) :
    QProb.Equiv (variance (⟨Distro.pointMass value, embed⟩ : NatDistro Ω)) QProb.zero := by
  simp only [variance, secondMomentScaled, meanSq, mean, secondMoment, rawMoment,
    natAtoms, Distro.pointMass, List.map_cons, List.map_nil, weightedPowSum,
    QProb.sub, QProb.Equiv, QProb.zero, Nat.one_mul, Nat.mul_one, Nat.add_zero,
    Nat.pow_succ, Nat.pow_zero, Nat.sub_self]

theorem pointMass_pgf (value : Ω) (embed : Ω → Nat) (s : QProb) :
    QProb.Equiv (pgf (⟨Distro.pointMass value, embed⟩ : NatDistro Ω) s) (qpow s (embed value)) := by
  simp only [pgf, Distro.pointMass, List.map_cons, List.map_nil, QProb.listSum,
    QProb.Equiv, QProb.div, QProb.add, QProb.ofNat, QProb.zero, QProb.scale,
    Nat.one_mul, Nat.mul_one, Nat.add_zero, Nat.zero_mul]

theorem ofFinWeights_pointMass (n : Nat) (w : Fin n → Nat)
    (positive : 0 < natSum n (finWeight w)) (center : Fin n)
    (off : ∀ k, k ≠ center → w k = 0) :
    (⟨ofFinWeights n w positive⟩ : Distro (Fin n)).SameLaw (Distro.pointMass center) := by
  have total : natSum n (finWeight w) = w center := by
    have terms : natSum n (finWeight w) =
        natSum n (fun i => (if i = center.val then w center else 0) * 1) := by
      apply natSum_congr
      intro i hi
      simp only [finWeight, dif_pos hi, Nat.mul_one]
      by_cases eq : i = center.val
      · have index : (⟨i, hi⟩ : Fin n) = center := Fin.ext eq
        rw [index, if_pos eq]
      · rw [if_neg eq, off ⟨i, hi⟩ (fun h => eq (congrArg Fin.val h))]
    rw [terms, natSum_spike, if_pos center.isLt, Nat.mul_one]
  apply Distro.sameLaw_of_singletons _ _ (List.finRange n)
    (finRange_nodup _) (fun value => List.mem_finRange value)
  intro k
  change FiniteProbRecord.eventMass (finWeighted n w) (FiniteProbRecord.singletonEvent k) * 1 =
    FiniteProbRecord.eventMass [(center, 1)] (FiniteProbRecord.singletonEvent k) *
      FiniteProbRecord.totalMass (finWeighted n w)
  rw [eventMass_finWeighted_singleton, totalMass_finWeighted, total]
  by_cases eq : center = k
  · subst k
    simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
      decide_true, if_true, Nat.add_zero, Nat.one_mul, Nat.mul_one]
  · rw [off k (Ne.symm eq)]
    simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
      eq, decide_false, Bool.false_eq_true, if_false, Nat.zero_mul]

/-- The endpoint law transports every moment and PGF without a special
division by a zero success or colour parameter. -/
theorem Distro.SameLaw.pointMass_moments {μ : Distro Ω} {value : Ω}
    (h : μ.SameLaw (Distro.pointMass value)) (embed : Ω → Nat) :
    QProb.Equiv (mean (⟨μ, embed⟩ : NatDistro Ω)) (QProb.ofNat (embed value)) ∧
    QProb.Equiv (variance (⟨μ, embed⟩ : NatDistro Ω)) QProb.zero ∧
    (∀ s : QProb, QProb.Equiv (pgf (⟨μ, embed⟩ : NatDistro Ω) s) (qpow s (embed value))) := by
  have numeric := NatDistro.sameLaw_of_distro h embed
  exact ⟨QProb.equiv_trans numeric.mean (pointMass_mean value embed),
    QProb.equiv_trans numeric.variance (pointMass_variance value embed),
    fun s => QProb.equiv_trans (numeric.pgf s) (pointMass_pgf value embed s)⟩


end Thesis.Probability.Distros
