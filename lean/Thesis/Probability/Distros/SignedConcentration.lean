import Thesis.Probability.Distros.SignedCovariance
import Thesis.Probability.Distros.Concentration

namespace Thesis.Probability.Distros

/-- Almost-sure statements ignore zero-weight occurrences but retain all
positive occurrences, including repeated outcome labels. -/
def Distro.AlmostSurely (μ : Distro Ω) (predicate : Ω → Prop) : Prop :=
  ∀ atom ∈ μ.record.atoms, 0 < atom.2 → predicate atom.1

theorem natIntegral_eq_zero_iff (atoms : List (Ω × Nat)) (f : Ω → Nat) :
    natIntegral atoms f = 0 ↔ ∀ atom ∈ atoms, 0 < atom.2 → f atom.1 = 0 := by
  induction atoms with
  | nil => simp only [natIntegral, List.not_mem_nil, false_implies, implies_true]
  | cons atom atoms ih =>
      constructor
      · intro total other member weight
        have head : atom.2 * f atom.1 = 0 := by change _ + _ = 0 at total; omega
        have tail : natIntegral atoms f = 0 := by change _ + _ = 0 at total; omega
        rcases List.mem_cons.mp member with same | member
        · subst other
          by_contra nonzero
          have pos := Nat.mul_pos weight (Nat.pos_of_ne_zero nonzero)
          omega
        · exact ih.mp tail other member weight
      · intro zero
        have tail := ih.mpr (fun other member => zero other (List.mem_cons_of_mem _ member))
        change atom.2 * f atom.1 + natIntegral atoms f = 0
        rw [tail]
        by_cases weight : atom.2 = 0
        · rw [weight, Nat.zero_mul]
        · rw [zero atom (List.mem_cons_self ..) (Nat.pos_of_ne_zero weight), Nat.mul_zero]

theorem signedAtomMass_congr_positive (atoms : List (Ω × Nat)) (f g : Ω → Int)
    (same : ∀ atom ∈ atoms, 0 < atom.2 → f atom.1 = g atom.1) :
    FiniteProbRecord.signedAtomMass atoms f = FiniteProbRecord.signedAtomMass atoms g := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      simp only [FiniteProbRecord.signedAtomMass, List.map_cons, List.sum_cons]
      rw [ih (fun other member => same other (List.mem_cons_of_mem _ member))]
      by_cases weight : atom.2 = 0
      · simp only [weight, Int.natCast_zero, Int.zero_mul]
      · rw [same atom (List.mem_cons_self ..) (Nat.pos_of_ne_zero weight)]

private theorem totalMass_positive_witness (atoms : List (Ω × Nat))
    (positive : 0 < FiniteProbRecord.totalMass atoms) : ∃ atom ∈ atoms, 0 < atom.2 := by
  induction atoms with
  | nil => change 0 < 0 at positive; omega
  | cons atom atoms ih =>
      by_cases weight : 0 < atom.2
      · exact ⟨atom, List.mem_cons_self .., weight⟩
      · have tail : 0 < FiniteProbRecord.totalMass atoms := by change atom.2 + _ > 0 at positive; omega
        rcases ih tail with ⟨other, member, weight⟩
        exact ⟨other, List.mem_cons_of_mem _ member, weight⟩

/-- Cleared squared deviation of an arbitrary integer observable. The
conversion to Nat is exact because the integer square is nonnegative. -/
def Distro.squaredDeviationInt (μ : Distro Ω) (f : Ω → Int) (x : Ω) : Nat :=
  (((μ.record.den : Int) * f x - μ.record.signedMass f) *
    ((μ.record.den : Int) * f x - μ.record.signedMass f)).toNat

theorem Distro.squaredDeviationInt_cast (μ : Distro Ω) (f : Ω → Int) (x : Ω) :
    (μ.squaredDeviationInt f x : Int) =
      ((μ.record.den : Int) * f x - μ.record.signedMass f) *
      ((μ.record.den : Int) * f x - μ.record.signedMass f) := by
  apply Int.toNat_of_nonneg
  simpa only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_one] using
    Int.sq_nonneg ((μ.record.den : Int) * f x - μ.record.signedMass f)

theorem Distro.varianceInt_num_cast (μ : Distro Ω) (f : Ω → Int) :
    ((μ.varianceInt f).num : Int) = (μ.signedCovariance f f).num :=
  Int.toNat_of_nonneg (μ.signedCovariance_self_nonnegative f)

theorem Distro.squaredDeviationInt_mass (μ : Distro Ω) (f : Ω → Int) :
    natIntegral μ.record.atoms (μ.squaredDeviationInt f) = μ.record.den * (μ.varianceInt f).num := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_mul, μ.varianceInt_num_cast]
  calc
    _ = FiniteProbRecord.signedAtomMass μ.record.atoms (fun x => (μ.squaredDeviationInt f x : Int)) :=
      (signedAtomMass_natIntegral _ _).symm
    _ = _ := by
      rw [FiniteProbRecord.signedAtomMass_congr _ _ _ (μ.squaredDeviationInt_cast f)]
      exact μ.signedCovariance_centered f f

/-- The squared-deviation expectation equals `den² * Var(f)`, including
signed observables and records with repeated labels or zero weights. -/
theorem Distro.squaredDeviationInt_expectation (μ : Distro Ω) (f : Ω → Int) :
    QProb.Equiv (μ.expectNat (μ.squaredDeviationInt f))
      (QProb.scale (μ.record.den * μ.record.den) (μ.varianceInt f)) := by
  change natIntegral μ.record.atoms (μ.squaredDeviationInt f) * (μ.record.den * μ.record.den) =
    ((μ.record.den * μ.record.den) * (μ.varianceInt f).num) * μ.record.den
  rw [μ.squaredDeviationInt_mass]
  ac_rfl

/-- Integer-observable Chebyshev at every positive rational radius. The
Boolean event is exactly the squared, denominator-cleared distance from E[f]. -/
theorem Distro.chebyshevInt_rational (μ : Distro Ω) (f : Ω → Int) (ε : QProb) (positive : 0 < ε.num) :
    QProb.LE (μ.record.probVal (fun x => decide
      (ε.num * ε.num * (μ.record.den * μ.record.den) ≤ μ.squaredDeviationInt f x * (ε.den * ε.den))))
      (QProb.div (μ.varianceInt f) (QProb.mul ε ε) (Nat.mul_pos positive positive)) := by
  let d := μ.record.den
  let scaled : NatDistro Ω := ⟨μ, fun x => μ.squaredDeviationInt f x * (ε.den * ε.den)⟩
  let t := ε.num * ε.num * (d * d)
  have ht : 0 < t := Nat.mul_pos (Nat.mul_pos positive positive) (Nat.mul_pos μ.record.den_pos μ.record.den_pos)
  have hm : QProb.Equiv (mean scaled)
      (QProb.scale (ε.den * ε.den) (QProb.scale (d * d) (μ.varianceInt f))) := by
    rw [mean_expectNat]
    exact QProb.equiv_trans (μ.expectNat_scale _ _) (QProb.scale_congr _ (μ.squaredDeviationInt_expectation f))
  have divided := QProb.div_congr hm (QProb.equiv_refl (QProb.ofNat t)) ht ht
  have simplify : QProb.Equiv
      (QProb.div (QProb.scale (ε.den * ε.den) (QProb.scale (d * d) (μ.varianceInt f))) (QProb.ofNat t) ht)
      (QProb.div (μ.varianceInt f) (QProb.mul ε ε) (Nat.mul_pos positive positive)) := by
    simp only [QProb.Equiv, QProb.div, QProb.scale, QProb.ofNat, QProb.mul, t]
    ac_rfl
  exact QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_trans divided simplify) (markov_div scaled t ht)

theorem Distro.varianceInt_zero_iff_centered (μ : Distro Ω) (f : Ω → Int) :
    (μ.varianceInt f).num = 0 ↔ μ.AlmostSurely (fun x => (μ.record.den : Int) * f x = μ.record.signedMass f) := by
  constructor
  · intro zero atom member weight
    have integral : natIntegral μ.record.atoms (μ.squaredDeviationInt f) = 0 := by
      rw [μ.squaredDeviationInt_mass, zero, Nat.mul_zero]
    have point := (natIntegral_eq_zero_iff _ _).mp integral atom member weight
    have square := μ.squaredDeviationInt_cast f atom.1
    rw [point, Int.natCast_zero] at square
    have centered : (μ.record.den : Int) * f atom.1 - μ.record.signedMass f = 0 := by
      rcases Int.mul_eq_zero.mp square.symm with zero | zero <;> exact zero
    omega
  · intro centered
    have integral : natIntegral μ.record.atoms (μ.squaredDeviationInt f) = 0 := by
      apply (natIntegral_eq_zero_iff _ _).mpr
      intro atom member weight
      simp only [squaredDeviationInt, centered atom member weight, Int.sub_self, Int.zero_mul, Int.toNat_zero]
    rw [μ.squaredDeviationInt_mass] at integral
    rcases Nat.mul_eq_zero.mp integral with zero | zero
    · have positive := μ.record.den_pos; omega
    · exact zero

/-- Zero variance is equivalent to an almost-surely constant integer
observable, with an actual constant chosen from positive finite support. -/
theorem Distro.varianceInt_zero_iff_constant (μ : Distro Ω) (f : Ω → Int) :
    (μ.varianceInt f).num = 0 ↔ ∃ c : Int, μ.AlmostSurely (fun x => f x = c) := by
  constructor
  · intro zero
    have centered := (μ.varianceInt_zero_iff_centered f).mp zero
    rcases totalMass_positive_witness μ.record.atoms (by rw [μ.record.total_mass]; exact μ.record.den_pos) with
      ⟨chosen, member, weight⟩
    refine ⟨f chosen.1, fun atom belongs positive => ?_⟩
    apply Int.eq_of_mul_eq_mul_left (by have positive := Int.natCast_pos.mpr μ.record.den_pos; omega)
    exact (centered atom belongs positive).trans (centered chosen member weight).symm
  · rintro ⟨c, constant⟩
    apply (μ.varianceInt_zero_iff_centered f).mpr
    have integral : μ.record.signedMass f = (μ.record.den : Int) * c := by
      change FiniteProbRecord.signedAtomMass μ.record.atoms f = _
      rw [signedAtomMass_congr_positive _ f (fun _ => c) constant,
        FiniteProbRecord.signedAtomMass_const, μ.record.total_mass]
    intro atom member weight
    rw [constant atom member weight, integral]

end Thesis.Probability.Distros
