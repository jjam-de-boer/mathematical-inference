import Thesis.Probability.Distros.LawEquivalence

namespace Thesis.Probability.Distros

/-- Markov's inequality for arbitrary nonnegative rational observables and
positive rational thresholds. The event compares their exact fraction values. -/
theorem Distro.markov_rational (μ : Distro Ω) (f : Ω → QProb) (threshold : QProb)
    (positive : 0 < threshold.num) :
    QProb.LE (μ.record.probVal (fun x => decide (threshold.num * (f x).den ≤ (f x).num * threshold.den)))
      (QProb.div (μ.expectation f) threshold positive) := by
  let d := observableDenominator μ.record.atoms f
  have hd := observableDenominator_pos μ.record.atoms f
  let g := fun x => (f x).num * (d / (f x).den)
  have cleared (atom : Ω × Nat) (member : atom ∈ μ.record.atoms) :
      QProb.Equiv (f atom.1) (⟨g atom.1, d, hd⟩ : QProb) := by
    have dvd := observableDenominator_dvd μ.record.atoms f atom member
    change (f atom.1).den ∣ d at dvd
    change (f atom.1).num * d = ((f atom.1).num * (d / (f atom.1).den)) * (f atom.1).den
    rw [Nat.mul_assoc, Nat.div_mul_cancel dvd]
  have events := μ.probVal_congr_on_support
    (fun x => decide (threshold.num * (f x).den ≤ (f x).num * threshold.den))
    (fun x => decide (threshold.num * d ≤ g x * threshold.den)) (by
      intro atom member
      apply decide_eq_decide.mpr
      exact ⟨QProb.le_congr (QProb.equiv_refl threshold) (cleared atom member),
        QProb.le_congr (QProb.equiv_refl threshold) (QProb.equiv_symm (cleared atom member))⟩)
  have expectation := QProb.equiv_trans (μ.expectation_congr_on_support f (fun x => ⟨g x, d, hd⟩) cleared)
    (μ.expectation_commonDen g d hd)
  let numeric : NatDistro Ω := ⟨μ, fun x => g x * threshold.den⟩
  let t := threshold.num * d
  have ht : 0 < t := Nat.mul_pos positive hd
  have hmean : QProb.Equiv (mean numeric) (QProb.scale threshold.den (μ.expectNat g)) := by
    rw [mean_expectNat]
    exact μ.expectNat_scale g threshold.den
  have simplify : QProb.Equiv
      (QProb.div (QProb.scale threshold.den (μ.expectNat g)) (QProb.ofNat t) ht)
      (QProb.div (QProb.div (μ.expectNat g) (QProb.ofNat d) hd) threshold positive) := by
    simp only [QProb.Equiv, QProb.div, QProb.scale, QProb.ofNat, t, Nat.mul_one]
    ac_rfl
  have rhs := QProb.equiv_trans (QProb.div_congr hmean (QProb.equiv_refl _) ht ht)
    (QProb.equiv_trans simplify (QProb.equiv_symm
      (QProb.div_congr expectation (QProb.equiv_refl threshold) positive positive)))
  exact QProb.le_congr (QProb.equiv_symm events) rhs (markov_div numeric t ht)

end Thesis.Probability.Distros
