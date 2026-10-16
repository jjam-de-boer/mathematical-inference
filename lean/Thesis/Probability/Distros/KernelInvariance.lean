import Thesis.Probability.Distros.Gaussian
import Thesis.Probability.Distros.ChiSquared
import Thesis.Probability.Distros.LawEquivalence
namespace Thesis.Probability.Distros
open Combinatorics

/-- Positive proportional weights define the same normalized law. -/
theorem ofFinWeights_sameLaw_cross (length : Nat) (w v : Fin length → Nat)
    (hw : 0 < natSum length (finWeight w)) (hv : 0 < natSum length (finWeight v))
    (c d : Nat) (hc : 0 < c) (cross : ∀ i, c * w i = d * v i) :
    (⟨ofFinWeights length w hw⟩ : Distro (Fin length)).SameLaw ⟨ofFinWeights length v hv⟩ := by
  have total : c * natSum length (finWeight w) = d * natSum length (finWeight v) := by
    rw [← natSum_mul_left, ← natSum_mul_left]
    apply natSum_congr
    intro i hi
    simp only [finWeight, dif_pos hi]
    exact cross ⟨i, hi⟩
  apply Distro.sameLaw_of_singletons _ _ (List.finRange length) (finRange_nodup _) (fun i => List.mem_finRange i)
  intro i
  change FiniteProbRecord.eventMass (finWeighted length w) (FiniteProbRecord.singletonEvent i) *
      FiniteProbRecord.totalMass (finWeighted length v) =
    FiniteProbRecord.eventMass (finWeighted length v) (FiniteProbRecord.singletonEvent i) *
      FiniteProbRecord.totalMass (finWeighted length w)
  rw [eventMass_finWeighted_singleton, eventMass_finWeighted_singleton, totalMass_finWeighted, totalMass_finWeighted]
  apply Nat.eq_of_mul_eq_mul_left hc
  calc
    _ = (c * w i) * natSum length (finWeight v) := by ac_rfl
    _ = v i * (d * natSum length (finWeight v)) := by rw [cross]; ac_rfl
    _ = _ := by rw [← total]; ac_rfl

/-- The law depends on the rational kernel value rather than its numerator
and denominator presentation. -/
theorem discreteGaussian_sameLaw_kernel (radius : Nat) (p q : QProb)
    (hp : QProb.LE p QProb.one) (hq : QProb.LE q QProb.one) (same : QProb.Equiv p q) :
    (discreteGaussianDistro radius p hp).SameLaw (discreteGaussianDistro radius q hq) := by
  apply ofFinWeights_sameLaw_cross _ _ _ (discreteGaussianWeight_sum_pos radius p)
    (discreteGaussianWeight_sum_pos radius q) (q.den ^ (radius * radius)) (p.den ^ (radius * radius))
    (Nat.pow_pos q.den_pos)
  intro i
  have h := QProb.equiv_trans (QProb.equiv_symm (discreteGaussianWeight_kernel radius p i))
    (QProb.equiv_trans (qpow_congr same (natSqDiff i.val radius)) (discreteGaussianWeight_kernel radius q i))
  change discreteGaussianWeight radius p i * q.den ^ (radius * radius) =
    discreteGaussianWeight radius q i * p.den ^ (radius * radius) at h
  simpa only [Nat.mul_comm] using h

theorem discreteGaussian_numeric_sameLaw_kernel (radius : Nat) (p q : QProb)
    (hp : QProb.LE p QProb.one) (hq : QProb.LE q QProb.one) (same : QProb.Equiv p q) :
    (discreteGaussianNatDistro radius p hp).SameLaw (discreteGaussianNatDistro radius q hq) :=
  NatDistro.sameLaw_of_distro (discreteGaussian_sameLaw_kernel radius p q hp hq same) Fin.val

/-- Every finite squared-coordinate block preserves kernel equivalence. -/
theorem chiSquared_record_sameLaw_kernel (df radius : Nat) (p q : QProb)
    (hp : QProb.LE p QProb.one) (hq : QProb.LE q QProb.one) (same : QProb.Equiv p q) :
    (⟨chiSquaredRecord df radius p hp⟩ : Distro _).SameLaw ⟨chiSquaredRecord df radius q hq⟩ := by
  induction df with
  | zero => exact Distro.SameLaw.refl _
  | succ df ih =>
      exact (ih.product (discreteGaussian_sameLaw_kernel radius p q hp hq same)).map
        (fun pair => (⟨pair.1.val + natSqDiff pair.2.val radius,
          natSqDiff_cons_lt df radius pair.1 pair.2⟩ : Fin ((df + 1) * radius * radius + 1)))

theorem chiSquared_sameLaw_kernel (df radius : Nat) (p q : QProb)
    (hp : QProb.LE p QProb.one) (hq : QProb.LE q QProb.one) (same : QProb.Equiv p q) :
    (chiSquaredDistro df radius p hp).SameLaw (chiSquaredDistro df radius q hq) :=
  NatDistro.sameLaw_of_distro (chiSquared_record_sameLaw_kernel df radius p q hp hq same) Fin.val

end Thesis.Probability.Distros
