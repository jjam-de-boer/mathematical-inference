import Thesis.Probability.Distros.LawEquivalence
import Thesis.Probability.FiniteSignedMass
namespace Thesis.Probability.Distros

/-- An integer numerator over a positive natural denominator, used for
signed moments rather than probabilities. -/
structure SignedMoment where
  num : Int
  den : Nat
  den_pos : 0 < den

def SignedMoment.Equiv (p q : SignedMoment) : Prop := p.num * (q.den : Int) = q.num * (p.den : Int)

instance (p q : SignedMoment) : Decidable (p.Equiv q) :=
  inferInstanceAs (Decidable (_ = _))

/-- Covariance on the record's actual denominator. -/
def Distro.covariance (μ : Distro Ω) (f g : Ω → Nat) : SignedMoment :=
  ⟨(μ.record.den : Int) * (natIntegral μ.record.atoms (fun x => f x * g x) : Int) -
    (natIntegral μ.record.atoms f : Int) * (natIntegral μ.record.atoms g : Int),
    μ.record.den * μ.record.den, Nat.mul_pos μ.record.den_pos μ.record.den_pos⟩

theorem signedAtomMass_natIntegral (atoms : List (Ω × Nat)) (f : Ω → Nat) :
    FiniteProbRecord.signedAtomMass atoms (fun value => (f value : Int)) =
      (natIntegral atoms f : Int) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [FiniteProbRecord.signedAtomMass, List.map_cons, List.sum_cons,
        natIntegral, Int.natCast_add, Int.natCast_mul] at ih ⊢
      rw [ih]

theorem signedAtomMass_sub (atoms : List (Ω × Nat)) (f g : Ω → Int) :
    FiniteProbRecord.signedAtomMass atoms (fun x => f x - g x) =
      FiniteProbRecord.signedAtomMass atoms f - FiniteProbRecord.signedAtomMass atoms g := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [FiniteProbRecord.signedAtomMass, List.map_cons, List.sum_cons] at ih ⊢
      rw [Int.mul_sub, ih]
      omega

/-- The numerator is exactly the centered product integral, after clearing
both means; its denominator represents E[fg] - E[f]E[g]. -/
theorem Distro.covariance_centered (μ : Distro Ω) (f g : Ω → Nat) :
    μ.record.signedMass (fun x =>
      ((μ.record.den : Int) * (f x : Int) - (natIntegral μ.record.atoms f : Int)) *
      ((μ.record.den : Int) * (g x : Int) - (natIntegral μ.record.atoms g : Int))) =
      (μ.record.den : Int) * (μ.covariance f g).num := by
  let D : Int := μ.record.den
  let F : Int := natIntegral μ.record.atoms f
  let G : Int := natIntegral μ.record.atoms g
  have point (x : Ω) : (D * (f x : Int) - F) * (D * (g x : Int) - G) =
      D * D * (f x : Int) * (g x : Int) - D * G * (f x : Int) -
      D * F * (g x : Int) + F * G := by
    simp only [Int.sub_mul, Int.mul_sub]
    have a : D * (f x : Int) * (D * (g x : Int)) = D * D * (f x : Int) * (g x : Int) := by ac_rfl
    have b : F * (D * (g x : Int)) = D * F * (g x : Int) := by ac_rfl
    have c : D * (f x : Int) * G = D * G * (f x : Int) := by ac_rfl
    rw [a, b, c]
    omega
  change FiniteProbRecord.signedAtomMass μ.record.atoms _ = _
  rw [FiniteProbRecord.signedAtomMass_congr _ _ _ point]
  rw [FiniteProbRecord.signedAtomMass_add, signedAtomMass_sub,
    signedAtomMass_sub]
  have first : FiniteProbRecord.signedAtomMass μ.record.atoms
      (fun x => D * D * (f x : Int) * (g x : Int)) =
      D * D * (natIntegral μ.record.atoms (fun x => f x * g x) : Int) := by
    have eq : (fun x => D * D * (f x : Int) * (g x : Int)) =
        (fun x => (D * D) * ((f x * g x : Nat) : Int)) := by
      funext x; rw [Int.natCast_mul]; ac_rfl
    rw [eq, FiniteProbRecord.signedAtomMass_mul_left, signedAtomMass_natIntegral]
  rw [first, FiniteProbRecord.signedAtomMass_mul_left, FiniteProbRecord.signedAtomMass_mul_left,
    signedAtomMass_natIntegral, signedAtomMass_natIntegral,
    FiniteProbRecord.signedAtomMass_const, μ.record.total_mass]
  change D * D * (natIntegral μ.record.atoms (fun x => f x * g x) : Int) - D * G * F - D * F * G + D * (F * G) =
    D * (D * (natIntegral μ.record.atoms (fun x => f x * g x) : Int) - F * G)
  simp only [Int.mul_sub]
  have eq : D * G * F = D * F * G := by ac_rfl
  rw [eq]
  simp only [Int.mul_assoc]
  omega

def SignedMoment.ofQProb (q : QProb) : SignedMoment := ⟨q.num, q.den, q.den_pos⟩

/-- The diagonal signed covariance recovers the existing witnessed variance. -/
theorem Distro.covariance_self_variance (μ : Distro Ω) (f : Ω → Nat) :
    SignedMoment.Equiv (μ.covariance f f) (SignedMoment.ofQProb (variance ⟨μ, f⟩)) := by
  let numeric : NatDistro Ω := ⟨μ, f⟩
  let D := μ.record.den
  let F := natIntegral μ.record.atoms f
  let H := natIntegral μ.record.atoms (fun x => f x * f x)
  let V := (variance numeric).num
  let T := (variance numeric).den
  have balance := variance_balance numeric
  rw [mean_expectNat, secondMoment, rawMoment_expectNat] at balance
  have point : (fun x => f x ^ 2) = (fun x => f x * f x) := by
    funext x; simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [point] at balance
  change (V * (D * D) + F * F * T) * D = H * (T * (D * D)) at balance
  have simplify : (V * (D * D) + F * F * T) * D = (H * T * D) * D := by
    rw [balance]; ac_rfl
  have eq := Nat.eq_of_mul_eq_mul_right μ.record.den_pos simplify
  have cast := congrArg (fun x : Nat => (x : Int)) eq
  simp only [Int.natCast_add, Int.natCast_mul] at cast
  change ((D : Int) * (H : Int) - (F : Int) * (F : Int)) * (T : Int) =
    (V : Int) * ((D * D : Nat) : Int)
  rw [Int.sub_mul, Int.natCast_mul]
  have permute : (D : Int) * (H : Int) * (T : Int) = (H : Int) * (T : Int) * (D : Int) := by ac_rfl
  rw [permute]
  omega

end Thesis.Probability.Distros
