import Thesis.Probability.Distros.Moments

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Variance and finite concentration.  Squared deviations are cleared to the
record's positive natural denominator, then related back to the witnessed
variance.  Rational-radius Chebyshev uses `|X - E[X]| ≥ ε` with its positive
denominators cleared; it makes no central-limit assertion.
-/

theorem natSqDiff_balance (k radius : Nat) :
    k * k + radius * radius = natSqDiff k radius + 2 * k * radius := by
  have poly (x d : Nat) : x * x + (x + d) * (x + d) = d * d + 2 * x * (x + d) := by
    have twice (v : Nat) : 2 * v = v + v := by omega
    simp only [Nat.mul_add, Nat.add_mul, twice]
    ac_rfl
  by_cases h : k ≤ radius
  · have hx : k + (radius - k) = radius := Nat.add_sub_of_le h
    have hs : natSqDiff k radius = (radius - k) * (radius - k) := by
      simp only [natSqDiff, if_pos h]
    rw [hs]
    simpa only [hx] using poly k (radius - k)
  · have hr : radius ≤ k := by omega
    have hx : radius + (k - radius) = k := Nat.add_sub_of_le hr
    have hs : natSqDiff k radius = (k - radius) * (k - radius) := by
      simp only [natSqDiff, if_neg h]
    rw [hs]
    have hp := poly radius (k - radius)
    rw [hx] at hp
    calc
      _ = radius * radius + k * k := Nat.add_comm _ _
      _ = (k - radius) * (k - radius) + 2 * radius * k := hp
      _ = _ := by ac_rfl

/-- Cleared squared deviations recover the usual variance after dividing by
`record.den²`.  No choice of reduced rational presentation is required. -/
theorem deviationDistro_mean (μ : NatDistro Ω) :
    QProb.Equiv (mean (deviationDistro μ))
      (QProb.scale (μ.distro.record.den * μ.distro.record.den) (variance μ)) := by
  let d := μ.distro.record.den
  let m := (mean μ).num
  let a := natIntegral μ.distro.record.atoms (sqDev μ.embed m d)
  let s := natIntegral μ.distro.record.atoms (fun x => μ.embed x * μ.embed x)
  have hm : natIntegral μ.distro.record.atoms μ.embed = m := by
    simp only [m, mean_expectNat, Distro.expectNat]
  have point (x : Ω) :
      (μ.embed x * d) * (μ.embed x * d) + m * m =
        sqDev μ.embed m d x + μ.embed x * (d * m + d * m) := by
    have h := natSqDiff_balance m (μ.embed x * d)
    change m * m + (μ.embed x * d) * (μ.embed x * d) =
      sqDev μ.embed m d x + 2 * m * (μ.embed x * d) at h
    rw [Nat.add_comm] at h
    have twice : 2 * m = m + m := by omega
    rw [twice] at h
    simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using h
  have balance := natIntegral_congr μ.distro.record.atoms _ _ point
  have square : (fun x => (μ.embed x * d) * (μ.embed x * d)) =
      (fun x => (μ.embed x * μ.embed x) * (d * d)) := by
    funext x
    ac_rfl
  rw [natIntegral_add, natIntegral_add, square,
    natIntegral_mul _ (fun x => μ.embed x * μ.embed x) (d * d),
    natIntegral_mul _ μ.embed (d * m + d * m),
    natIntegral_constant, hm, μ.distro.record.total_mass] at balance
  change s * (d * d) + d * (m * m) = a + m * (d * m + d * m) at balance
  have twice : m * (d * m + d * m) = d * (m * m) + d * (m * m) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [twice] at balance
  have reduced : a + d * (m * m) = s * (d * d) := by omega
  let candidate : QProb := ⟨a, d * (d * d),
    Nat.mul_pos μ.distro.record.den_pos
      (Nat.mul_pos μ.distro.record.den_pos μ.distro.record.den_pos)⟩
  have hs : (secondMoment μ).num = s := by
    rw [secondMoment, rawMoment_expectNat]
    simp only [Distro.expectNat, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rfl
  have varianceCandidate : QProb.Equiv (variance μ) candidate := by
    apply variance_eq_of_balance
    change (a * (d * d) + (m * m) * (d * (d * d))) * d =
      (secondMoment μ).num * ((d * (d * d)) * (d * d))
    rw [hs]
    calc
      _ = (a + d * (m * m)) * (d * (d * d)) := by
        simp only [Nat.add_mul]
        ac_rfl
      _ = _ := by rw [reduced]; ac_rfl
  refine QProb.equiv_trans ?_ (QProb.equiv_symm
    (QProb.scale_congr (d * d) varianceCandidate))
  rw [mean_expectNat]
  change a * (d * (d * d)) = ((d * d) * a) * d
  ac_rfl

/-- Variance form of the existing integer-threshold Chebyshev inequality. -/
theorem chebyshev_variance (μ : NatDistro Ω) (t : Nat) (ht : 0 < t) :
    QProb.LE
      (QProb.scale t (μ.distro.record.probVal (fun value =>
        decide (t ≤ sqDev μ.embed (mean μ).num μ.distro.record.den value))))
      (QProb.scale (μ.distro.record.den * μ.distro.record.den) (variance μ)) :=
  QProb.le_congr (QProb.equiv_refl _) (deviationDistro_mean μ) (chebyshev μ t ht)

/-- Chebyshev at a positive rational radius `ε`.  The event is precisely
`|X - E[X]| ≥ ε`, expressed by squaring and clearing positive denominators. -/
theorem chebyshev_rational (μ : NatDistro Ω) (ε : QProb) (positive : 0 < ε.num) :
    QProb.LE
      (μ.distro.record.probVal (fun value => decide
        (ε.num * ε.num * (μ.distro.record.den * μ.distro.record.den) ≤
          sqDev μ.embed (mean μ).num μ.distro.record.den value * (ε.den * ε.den))))
      (QProb.div (variance μ) (QProb.mul ε ε) (Nat.mul_pos positive positive)) := by
  let d := μ.distro.record.den
  let δ := deviationDistro μ
  let scaled : NatDistro Ω := ⟨μ.distro, fun x => δ.embed x * (ε.den * ε.den)⟩
  let t := ε.num * ε.num * (d * d)
  have ht : 0 < t := Nat.mul_pos (Nat.mul_pos positive positive)
    (Nat.mul_pos μ.distro.record.den_pos μ.distro.record.den_pos)
  have hm : QProb.Equiv (mean scaled)
      (QProb.scale (ε.den * ε.den) (QProb.scale (d * d) (variance μ))) := by
    rw [mean_expectNat]
    exact QProb.equiv_trans (Distro.expectNat_scale μ.distro δ.embed (ε.den * ε.den))
      (QProb.scale_congr _ (by simpa only [mean_expectNat] using deviationDistro_mean μ))
  have hd := QProb.div_congr hm (QProb.equiv_refl (QProb.ofNat t)) ht ht
  have simplify : QProb.Equiv
      (QProb.div (QProb.scale (ε.den * ε.den) (QProb.scale (d * d) (variance μ)))
        (QProb.ofNat t) ht)
      (QProb.div (variance μ) (QProb.mul ε ε) (Nat.mul_pos positive positive)) := by
    simp only [QProb.Equiv, QProb.div, QProb.scale, QProb.ofNat, QProb.mul, t]
    ac_rfl
  exact QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_trans hd simplify)
    (markov_div scaled t ht)

end Thesis.Probability.Distros
