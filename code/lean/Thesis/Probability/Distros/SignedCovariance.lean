import Thesis.Probability.Distros.SignedMoments
/-! Signed expectation, covariance and nonnegative integer-observable
variance. Law transport and algebra preserve the existing Nat API. -/

namespace Thesis.Probability.Distros

namespace SignedMoment

def add (p q : SignedMoment) : SignedMoment :=
  ⟨p.num * (q.den : Int) + q.num * (p.den : Int), p.den * q.den, Nat.mul_pos p.den_pos q.den_pos⟩
def mul (p q : SignedMoment) : SignedMoment :=
  ⟨p.num * q.num, p.den * q.den, Nat.mul_pos p.den_pos q.den_pos⟩
def neg (p : SignedMoment) : SignedMoment := ⟨-p.num, p.den, p.den_pos⟩
def sub (p q : SignedMoment) : SignedMoment := add p (neg q)
def scale (c : Int) (p : SignedMoment) : SignedMoment := ⟨c * p.num, p.den, p.den_pos⟩
def ofInt (c : Int) : SignedMoment := ⟨c, 1, Nat.zero_lt_one⟩

theorem Equiv.refl (p : SignedMoment) : p.Equiv p := rfl

theorem Equiv.symm {p q : SignedMoment} (h : p.Equiv q) : q.Equiv p := Eq.symm h

theorem Equiv.trans {p q r : SignedMoment} (h : p.Equiv q) (h' : q.Equiv r) : p.Equiv r := by
  have nonzero : (q.den : Int) ≠ 0 := by
    intro eq
    have h : q.den = 0 := Int.ofNat_inj.mp eq
    have pos := q.den_pos
    omega
  apply Int.eq_of_mul_eq_mul_right nonzero
  change (p.num * (r.den : Int)) * (q.den : Int) = (r.num * (p.den : Int)) * (q.den : Int)
  calc
    _ = (p.num * (q.den : Int)) * (r.den : Int) := by ac_rfl
    _ = (q.num * (r.den : Int)) * (p.den : Int) := by rw [h]; ac_rfl
    _ = _ := by rw [h']; ac_rfl

theorem add_congr {p p' q q' : SignedMoment} (h : p.Equiv p') (h' : q.Equiv q') :
    (add p q).Equiv (add p' q') := by
  change (p.num * (q.den : Int) + q.num * (p.den : Int)) * ((p'.den * q'.den : Nat) : Int) =
    (p'.num * (q'.den : Int) + q'.num * (p'.den : Int)) * ((p.den * q.den : Nat) : Int)
  simp only [Int.natCast_mul, Int.add_mul]
  calc
    _ = (p.num * (p'.den : Int)) * ((q.den : Int) * (q'.den : Int)) +
        (q.num * (q'.den : Int)) * ((p.den : Int) * (p'.den : Int)) := by ac_rfl
    _ = _ := by rw [h, h']; ac_rfl

theorem mul_congr {p p' q q' : SignedMoment} (h : p.Equiv p') (h' : q.Equiv q') :
    (mul p q).Equiv (mul p' q') := by
  change (p.num * q.num) * ((p'.den * q'.den : Nat) : Int) =
    (p'.num * q'.num) * ((p.den * q.den : Nat) : Int)
  simp only [Int.natCast_mul]
  calc
    _ = (p.num * (p'.den : Int)) * (q.num * (q'.den : Int)) := by ac_rfl
    _ = _ := by rw [h, h']; ac_rfl

theorem neg_congr {p q : SignedMoment} (h : p.Equiv q) : (neg p).Equiv (neg q) := by
  change -p.num * (q.den : Int) = -q.num * (p.den : Int)
  rw [Int.neg_mul, Int.neg_mul, h]

theorem sub_congr {p p' q q' : SignedMoment} (h : p.Equiv p') (h' : q.Equiv q') :
    (sub p q).Equiv (sub p' q') := add_congr h (neg_congr h')

theorem scale_congr (c : Int) {p q : SignedMoment} (h : p.Equiv q) : (scale c p).Equiv (scale c q) := by
  change (c * p.num) * (q.den : Int) = (c * q.num) * (p.den : Int)
  rw [Int.mul_assoc, Int.mul_assoc, h]

end SignedMoment

/-- Signed expectation retains the positive probability denominator. -/
def Distro.signedExpectation (μ : Distro Ω) (f : Ω → Int) : SignedMoment :=
  ⟨μ.record.signedMass f, μ.record.den, μ.record.den_pos⟩

/-- Covariance of arbitrary integer-valued observables. -/
def Distro.signedCovariance (μ : Distro Ω) (f g : Ω → Int) : SignedMoment :=
  ⟨(μ.record.den : Int) * μ.record.signedMass (fun x => f x * g x) - μ.record.signedMass f * μ.record.signedMass g,
    μ.record.den * μ.record.den, Nat.mul_pos μ.record.den_pos μ.record.den_pos⟩

theorem signedAtomMass_pos_neg (atoms : List (Ω × Nat)) (f : Ω → Int) :
    FiniteProbRecord.signedAtomMass atoms f =
      (natIntegral atoms (fun x => (f x).toNat) : Int) - (natIntegral atoms (fun x => (-f x).toNat) : Int) := by
  rw [← signedAtomMass_natIntegral, ← signedAtomMass_natIntegral, ← signedAtomMass_sub]
  apply FiniteProbRecord.signedAtomMass_congr
  intro x
  exact (Int.toNat_sub_toNat_neg (f x)).symm

theorem Distro.SameLaw.signedExpectation {μ ν : Distro Ω} (same : μ.SameLaw ν) (f : Ω → Int) :
    (μ.signedExpectation f).Equiv (ν.signedExpectation f) := by
  have positive := same.expectNat (fun x => (f x).toNat)
  have negative := same.expectNat (fun x => (-f x).toNat)
  change natIntegral μ.record.atoms (fun x => (f x).toNat) * ν.record.den =
    natIntegral ν.record.atoms (fun x => (f x).toNat) * μ.record.den at positive
  change natIntegral μ.record.atoms (fun x => (-f x).toNat) * ν.record.den =
    natIntegral ν.record.atoms (fun x => (-f x).toNat) * μ.record.den at negative
  have hp := congrArg (fun n : Nat => (n : Int)) positive
  have hn := congrArg (fun n : Nat => (n : Int)) negative
  simp only [Int.natCast_mul] at hp hn
  change FiniteProbRecord.signedAtomMass μ.record.atoms f * (ν.record.den : Int) =
    FiniteProbRecord.signedAtomMass ν.record.atoms f * (μ.record.den : Int)
  rw [signedAtomMass_pos_neg, signedAtomMass_pos_neg, Int.sub_mul, Int.sub_mul, hp, hn]

theorem Distro.signedCovariance_expectations (μ : Distro Ω) (f g : Ω → Int) :
    (μ.signedCovariance f g).Equiv
      (SignedMoment.sub (μ.signedExpectation (fun x => f x * g x))
        (SignedMoment.mul (μ.signedExpectation f) (μ.signedExpectation g))) := by
  simp only [SignedMoment.Equiv, signedCovariance, signedExpectation,
    SignedMoment.sub, SignedMoment.add, SignedMoment.neg, SignedMoment.mul, Int.natCast_mul,
    Int.sub_mul, Int.add_mul, Int.neg_mul]
  congr 1 <;> ac_rfl

theorem Distro.SameLaw.signedCovariance {μ ν : Distro Ω} (same : μ.SameLaw ν) (f g : Ω → Int) :
    (μ.signedCovariance f g).Equiv (ν.signedCovariance f g) :=
  (μ.signedCovariance_expectations f g).trans
    ((SignedMoment.sub_congr (same.signedExpectation _) (SignedMoment.mul_congr
      (same.signedExpectation f) (same.signedExpectation g))).trans
        (ν.signedCovariance_expectations f g).symm)

namespace SignedMoment

theorem eq_of_num_den {p q : SignedMoment} (num : p.num = q.num) (den : p.den = q.den) : p = q := by
  cases p
  cases q
  cases num
  cases den
  rfl

theorem add_of_num (p a b : SignedMoment) (ha : p.den = a.den) (hb : p.den = b.den)
    (num : p.num = a.num + b.num) : p.Equiv (add a b) := by
  change p.num * ((a.den * b.den : Nat) : Int) =
    (a.num * (b.den : Int) + b.num * (a.den : Int)) * (p.den : Int)
  rw [← ha, ← hb, num, Int.natCast_mul, Int.add_mul, Int.add_mul]
  ac_rfl

theorem sum3_of_num (p a b c : SignedMoment) (ha : p.den = a.den) (hb : p.den = b.den)
    (hc : p.den = c.den) (num : p.num = a.num + b.num + c.num) : p.Equiv (add (add a b) c) := by
  let middle : SignedMoment := ⟨a.num + b.num, p.den, p.den_pos⟩
  exact (add_of_num p middle c rfl hc num).trans
    (add_congr (add_of_num middle a b ha hb rfl) (Equiv.refl c))

theorem ofQProb_congr {p q : QProb} (same : QProb.Equiv p q) : (ofQProb p).Equiv (ofQProb q) := by
  have h := congrArg (fun n : Nat => (n : Int)) same
  simpa only [Int.natCast_mul] using h

end SignedMoment

theorem Distro.signedCovariance_nat (μ : Distro Ω) (f g : Ω → Nat) :
    μ.signedCovariance (fun x => (f x : Int)) (fun x => (g x : Int)) = μ.covariance f g := by
  apply SignedMoment.eq_of_num_den
  · simp only [signedCovariance, covariance, FiniteProbRecord.signedMass]
    have fg : (fun x => (f x : Int) * (g x : Int)) = (fun x => ((f x * g x : Nat) : Int)) := by
      funext x; exact (Int.natCast_mul _ _).symm
    rw [fg, signedAtomMass_natIntegral, signedAtomMass_natIntegral, signedAtomMass_natIntegral]
  · rfl

theorem Distro.signedExpectation_map (μ : Distro Ω) (encode : Ω → X) (f : X → Int) :
    (μ.map encode).signedExpectation f = μ.signedExpectation (fun x => f (encode x)) := by
  apply SignedMoment.eq_of_num_den
  · exact FiniteProbRecord.signedMass_map _ _ _
  · rfl

theorem Distro.signedCovariance_map (μ : Distro Ω) (encode : Ω → X) (f g : X → Int) :
    (μ.map encode).signedCovariance f g = μ.signedCovariance (fun x => f (encode x)) (fun x => g (encode x)) := by
  apply SignedMoment.eq_of_num_den
  · simp only [signedCovariance, Distro.map, FiniteProbRecord.signedMass_map]
    rfl
  · rfl

theorem Distro.signedCovariance_symm (μ : Distro Ω) (f g : Ω → Int) :
    μ.signedCovariance f g = μ.signedCovariance g f := by
  apply SignedMoment.eq_of_num_den
  · change _ - _ = _ - _
    have fg : (fun x => f x * g x) = (fun x => g x * f x) := funext (fun x => Int.mul_comm _ _)
    rw [fg, Int.mul_comm (μ.record.signedMass f) (μ.record.signedMass g)]
  · rfl

theorem Distro.signedCovariance_add_left_num (μ : Distro Ω) (f g h : Ω → Int) :
    (μ.signedCovariance (fun x => f x + g x) h).num =
      (μ.signedCovariance f h).num + (μ.signedCovariance g h).num := by
  simp only [signedCovariance, FiniteProbRecord.signedMass, FiniteProbRecord.signedAtomMass_add,
    Int.mul_add, Int.add_mul]
  omega

theorem Distro.signedCovariance_add_left (μ : Distro Ω) (f g h : Ω → Int) :
    (μ.signedCovariance (fun x => f x + g x) h).Equiv
      (SignedMoment.add (μ.signedCovariance f h) (μ.signedCovariance g h)) :=
  SignedMoment.add_of_num _ _ _ rfl rfl (μ.signedCovariance_add_left_num f g h)

theorem Distro.signedCovariance_add_right_num (μ : Distro Ω) (f g h : Ω → Int) :
    (μ.signedCovariance f (fun x => g x + h x)).num =
      (μ.signedCovariance f g).num + (μ.signedCovariance f h).num := by
  rw [μ.signedCovariance_symm f, μ.signedCovariance_add_left_num,
    μ.signedCovariance_symm g, μ.signedCovariance_symm h]

theorem Distro.signedCovariance_add_right (μ : Distro Ω) (f g h : Ω → Int) :
    (μ.signedCovariance f (fun x => g x + h x)).Equiv
      (SignedMoment.add (μ.signedCovariance f g) (μ.signedCovariance f h)) :=
  SignedMoment.add_of_num _ _ _ rfl rfl (μ.signedCovariance_add_right_num f g h)

theorem Distro.signedCovariance_scale_left (μ : Distro Ω) (c : Int) (f g : Ω → Int) :
    μ.signedCovariance (fun x => c * f x) g = SignedMoment.scale c (μ.signedCovariance f g) := by
  apply SignedMoment.eq_of_num_den
  · have point : (fun x => (c * f x) * g x) = (fun x => c * (f x * g x)) :=
      funext (fun x => Int.mul_assoc _ _ _)
    simp only [signedCovariance, SignedMoment.scale, point, FiniteProbRecord.signedMass_mul_left,
      Int.mul_sub]
    congr 1 <;> ac_rfl
  · rfl

theorem Distro.signedCovariance_scale_right (μ : Distro Ω) (c : Int) (f g : Ω → Int) :
    μ.signedCovariance f (fun x => c * g x) = SignedMoment.scale c (μ.signedCovariance f g) := by
  rw [μ.signedCovariance_symm f, μ.signedCovariance_scale_left, μ.signedCovariance_symm g]

theorem Distro.signedCovariance_constant (μ : Distro Ω) (c : Int) (f : Ω → Int) :
    (μ.signedCovariance (fun _ => c) f).Equiv (SignedMoment.ofInt 0) := by
  simp only [SignedMoment.Equiv, signedCovariance, SignedMoment.ofInt,
    FiniteProbRecord.signedMass_mul_left, FiniteProbRecord.signedMass_const,
    Int.natCast_mul, Int.cast_ofNat_Int, Int.mul_one, Int.zero_mul]
  have eq : (μ.record.den : Int) * (c * μ.record.signedMass f) =
      ((μ.record.den : Int) * c) * μ.record.signedMass f := by ac_rfl
  rw [eq, Int.sub_self]

theorem signedMass_product_left (μ : FiniteProbRecord Ω) (ν : FiniteProbRecord X) (f : Ω → Int) :
    (μ.product ν).signedMass (fun pair => f pair.1) = μ.signedMass f * (ν.den : Int) := by
  have h := FiniteProbRecord.signedMass_product μ ν f (fun _ => 1)
  simpa only [Int.mul_one, FiniteProbRecord.signedMass_const] using h

theorem signedMass_product_right (μ : FiniteProbRecord Ω) (ν : FiniteProbRecord X) (f : X → Int) :
    (μ.product ν).signedMass (fun pair => f pair.2) = (μ.den : Int) * ν.signedMass f := by
  have h := FiniteProbRecord.signedMass_product μ ν (fun _ => 1) f
  simpa only [Int.one_mul, Int.mul_one, FiniteProbRecord.signedMass_const] using h

/-- Independent integer observables have exactly zero covariance. -/
theorem Distro.signedCovariance_independent (μ : Distro Ω) (ν : Distro X) (f : Ω → Int) (g : X → Int) :
    ((μ.product ν).signedCovariance (fun pair => f pair.1) (fun pair => g pair.2)).Equiv
      (SignedMoment.ofInt 0) := by
  change (((μ.record.product ν.record).den : Int) * (μ.record.product ν.record).signedMass
      (fun pair => f pair.1 * g pair.2) - (μ.record.product ν.record).signedMass (fun pair => f pair.1) *
        (μ.record.product ν.record).signedMass (fun pair => g pair.2)) * 1 = 0 * _
  rw [FiniteProbRecord.signedMass_product, signedMass_product_left, signedMass_product_right]
  simp only [FiniteProbRecord.product, Int.natCast_mul, Int.mul_one, Int.zero_mul]
  have eq : ((μ.record.den : Int) * (ν.record.den : Int)) * (μ.record.signedMass f * ν.record.signedMass g) =
      (μ.record.signedMass f * (ν.record.den : Int)) * ((μ.record.den : Int) * ν.record.signedMass g) := by ac_rfl
  rw [eq, Int.sub_self]

/-- The covariance numerator is a centered product integral with both
means cleared on the original probability denominator. -/
theorem Distro.signedCovariance_centered (μ : Distro Ω) (f g : Ω → Int) :
    μ.record.signedMass (fun x =>
      ((μ.record.den : Int) * f x - μ.record.signedMass f) *
      ((μ.record.den : Int) * g x - μ.record.signedMass g)) =
      (μ.record.den : Int) * (μ.signedCovariance f g).num := by
  let D : Int := μ.record.den
  let F := μ.record.signedMass f
  let G := μ.record.signedMass g
  have point (x : Ω) : (D * f x - F) * (D * g x - G) =
      D * D * (f x * g x) - D * G * f x - D * F * g x + F * G := by
    simp only [Int.sub_mul, Int.mul_sub]
    have a : D * f x * (D * g x) = D * D * (f x * g x) := by ac_rfl
    have b : F * (D * g x) = D * F * g x := by ac_rfl
    have c : D * f x * G = D * G * f x := by ac_rfl
    rw [a, b, c]
    omega
  change FiniteProbRecord.signedAtomMass μ.record.atoms _ = _
  rw [FiniteProbRecord.signedAtomMass_congr _ _ _ point,
    FiniteProbRecord.signedAtomMass_add, signedAtomMass_sub, signedAtomMass_sub,
    FiniteProbRecord.signedAtomMass_mul_left, FiniteProbRecord.signedAtomMass_mul_left,
    FiniteProbRecord.signedAtomMass_mul_left, FiniteProbRecord.signedAtomMass_const,
    μ.record.total_mass]
  change D * D * μ.record.signedMass (fun x => f x * g x) - D * G * F - D * F * G + D * (F * G) =
    D * (D * μ.record.signedMass (fun x => f x * g x) - F * G)
  rw [Int.mul_sub]
  have eq : D * G * F = D * F * G := by ac_rfl
  rw [eq]
  simp only [Int.mul_assoc]
  omega

theorem signedAtomMass_nonnegative (atoms : List (Ω × Nat)) (f : Ω → Int)
    (nonnegative : ∀ x, 0 ≤ f x) : 0 ≤ FiniteProbRecord.signedAtomMass atoms f := by
  induction atoms with
  | nil => exact Int.le_refl 0
  | cons atom atoms ih =>
      simp only [FiniteProbRecord.signedAtomMass, List.map_cons, List.sum_cons] at ih ⊢
      exact Int.add_nonneg (Int.mul_nonneg (Int.natCast_nonneg _) (nonnegative _)) ih

theorem Distro.signedCovariance_self_nonnegative (μ : Distro Ω) (f : Ω → Int) :
    0 ≤ (μ.signedCovariance f f).num := by
  have centered := μ.signedCovariance_centered f f
  have h := signedAtomMass_nonnegative μ.record.atoms (fun x =>
    ((μ.record.den : Int) * f x - μ.record.signedMass f) *
    ((μ.record.den : Int) * f x - μ.record.signedMass f)) (fun x => by
      simpa only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_one] using
        Int.sq_nonneg ((μ.record.den : Int) * f x - μ.record.signedMass f))
  change 0 ≤ μ.record.signedMass _ at h
  rw [centered, Int.mul_comm] at h
  exact Int.nonneg_of_mul_nonneg_left h (Int.natCast_pos.mpr μ.record.den_pos)

/-- Variance of an integer observable is nonnegative rational. Its
nonnegativity proof is the finite centered-square identity. -/
def Distro.varianceInt (μ : Distro Ω) (f : Ω → Int) : QProb :=
  ⟨(μ.signedCovariance f f).num.toNat, (μ.signedCovariance f f).den, (μ.signedCovariance f f).den_pos⟩

theorem Distro.varianceInt_signed (μ : Distro Ω) (f : Ω → Int) :
    (SignedMoment.ofQProb (μ.varianceInt f)).Equiv (μ.signedCovariance f f) := by
  change ((μ.signedCovariance f f).num.toNat : Int) * ((μ.signedCovariance f f).den : Int) =
    (μ.signedCovariance f f).num * ((μ.signedCovariance f f).den : Int)
  rw [Int.toNat_of_nonneg (μ.signedCovariance_self_nonnegative f)]

/-- Extending the observable domain preserves the existing witnessed Nat variance. -/
theorem Distro.varianceInt_nat (μ : Distro Ω) (f : Ω → Nat) :
    QProb.Equiv (μ.varianceInt (fun x => (f x : Int))) (variance ⟨μ, f⟩) := by
  have h := μ.varianceInt_signed (fun x => (f x : Int))
  rw [μ.signedCovariance_nat f f] at h
  have result := h.trans (μ.covariance_self_variance f)
  apply Int.ofNat_inj.mp
  simpa only [Int.natCast_mul] using result

theorem Distro.signedCovariance_sum_self_num (μ : Distro Ω) (f g : Ω → Int) :
    (μ.signedCovariance (fun x => f x + g x) (fun x => f x + g x)).num =
      (μ.signedCovariance f f).num + (μ.signedCovariance g g).num +
        2 * (μ.signedCovariance f g).num := by
  rw [μ.signedCovariance_add_left_num, μ.signedCovariance_add_right_num, μ.signedCovariance_add_right_num,
    μ.signedCovariance_symm g f]
  omega

/-- Dependent integer observables retain the covariance term in the
variance of their sum; negative covariance is represented exactly. -/
theorem Distro.varianceInt_add (μ : Distro Ω) (f g : Ω → Int) :
    (SignedMoment.ofQProb (μ.varianceInt (fun x => f x + g x))).Equiv
      (SignedMoment.add
        (SignedMoment.add (SignedMoment.ofQProb (μ.varianceInt f)) (SignedMoment.ofQProb (μ.varianceInt g)))
        (SignedMoment.scale 2 (μ.signedCovariance f g))) := by
  refine (μ.varianceInt_signed _).trans ?_
  refine (SignedMoment.sum3_of_num (μ.signedCovariance (fun x => f x + g x) (fun x => f x + g x)) (μ.signedCovariance f f) (μ.signedCovariance g g)
    (SignedMoment.scale 2 (μ.signedCovariance f g)) rfl rfl rfl (μ.signedCovariance_sum_self_num f g)).trans ?_
  exact SignedMoment.add_congr
    (SignedMoment.add_congr (μ.varianceInt_signed f).symm (μ.varianceInt_signed g).symm)
      (SignedMoment.Equiv.refl _)

/-- The covariance sum law also applies to the original Nat variance API. -/
theorem Distro.variance_add_covariance (μ : Distro Ω) (f g : Ω → Nat) :
    (SignedMoment.ofQProb (variance (⟨μ, fun x => f x + g x⟩ : NatDistro Ω))).Equiv
      (SignedMoment.add
        (SignedMoment.add (SignedMoment.ofQProb (variance (⟨μ, f⟩ : NatDistro Ω)))
          (SignedMoment.ofQProb (variance (⟨μ, g⟩ : NatDistro Ω))))
        (SignedMoment.scale 2 (μ.covariance f g))) := by
  have law := μ.varianceInt_add (fun x => (f x : Int)) (fun x => (g x : Int))
  have sum : (fun x => (f x : Int) + (g x : Int)) = (fun x => ((f x + g x : Nat) : Int)) := by
    funext x; exact (Int.natCast_add _ _).symm
  rw [sum, μ.signedCovariance_nat f g] at law
  exact (SignedMoment.ofQProb_congr (μ.varianceInt_nat _)).symm.trans
    (law.trans (SignedMoment.add_congr
      (SignedMoment.add_congr (SignedMoment.ofQProb_congr (μ.varianceInt_nat f))
        (SignedMoment.ofQProb_congr (μ.varianceInt_nat g))) (SignedMoment.Equiv.refl _)))

theorem Distro.SameLaw.varianceInt {μ ν : Distro Ω} (same : μ.SameLaw ν) (f : Ω → Int) :
    QProb.Equiv (μ.varianceInt f) (ν.varianceInt f) := by
  have h := (μ.varianceInt_signed f).trans ((same.signedCovariance f f).trans (ν.varianceInt_signed f).symm)
  apply Int.ofNat_inj.mp
  simpa only [Int.natCast_mul] using h

theorem Distro.varianceInt_map (μ : Distro Ω) (encode : Ω → X) (f : X → Int) :
    (μ.map encode).varianceInt f = μ.varianceInt (fun x => f (encode x)) := by
  simp only [varianceInt, signedCovariance_map]

theorem Distro.covariance_symm (μ : Distro Ω) (f g : Ω → Nat) : μ.covariance f g = μ.covariance g f := by
  rw [← μ.signedCovariance_nat f g, ← μ.signedCovariance_nat g f, μ.signedCovariance_symm]

theorem Distro.covariance_map (μ : Distro Ω) (encode : Ω → X) (f g : X → Nat) :
    (μ.map encode).covariance f g = μ.covariance (fun x => f (encode x)) (fun x => g (encode x)) := by
  rw [← Distro.signedCovariance_nat, Distro.signedCovariance_map, Distro.signedCovariance_nat]

theorem Distro.SameLaw.covariance {μ ν : Distro Ω} (same : μ.SameLaw ν) (f g : Ω → Nat) :
    (μ.covariance f g).Equiv (ν.covariance f g) := by
  rw [← μ.signedCovariance_nat, ← ν.signedCovariance_nat]
  exact same.signedCovariance _ _

theorem Distro.covariance_add_left (μ : Distro Ω) (f g h : Ω → Nat) :
    (μ.covariance (fun x => f x + g x) h).Equiv
      (SignedMoment.add (μ.covariance f h) (μ.covariance g h)) := by
  have law := μ.signedCovariance_add_left (fun x => (f x : Int)) (fun x => (g x : Int)) (fun x => (h x : Int))
  have sum : (fun x => (f x : Int) + (g x : Int)) = (fun x => ((f x + g x : Nat) : Int)) := by
    funext x; exact (Int.natCast_add _ _).symm
  rw [sum, μ.signedCovariance_nat, μ.signedCovariance_nat, μ.signedCovariance_nat] at law
  exact law

theorem Distro.covariance_add_right (μ : Distro Ω) (f g h : Ω → Nat) :
    (μ.covariance f (fun x => g x + h x)).Equiv
      (SignedMoment.add (μ.covariance f g) (μ.covariance f h)) := by
  rw [μ.covariance_symm f, μ.covariance_symm f g, μ.covariance_symm f h]
  exact μ.covariance_add_left g h f

theorem Distro.covariance_scale_left (μ : Distro Ω) (c : Nat) (f g : Ω → Nat) :
    μ.covariance (fun x => c * f x) g = SignedMoment.scale (c : Int) (μ.covariance f g) := by
  have law := μ.signedCovariance_scale_left (c : Int) (fun x => (f x : Int)) (fun x => (g x : Int))
  have product : (fun x => (c : Int) * (f x : Int)) = (fun x => ((c * f x : Nat) : Int)) := by
    funext x; exact (Int.natCast_mul _ _).symm
  rw [product, μ.signedCovariance_nat, μ.signedCovariance_nat] at law
  exact law

theorem Distro.covariance_scale_right (μ : Distro Ω) (c : Nat) (f g : Ω → Nat) :
    μ.covariance f (fun x => c * g x) = SignedMoment.scale (c : Int) (μ.covariance f g) := by
  rw [μ.covariance_symm f, μ.covariance_scale_left, μ.covariance_symm g]

theorem Distro.covariance_independent (μ : Distro Ω) (ν : Distro X) (f : Ω → Nat) (g : X → Nat) :
    ((μ.product ν).covariance (fun pair => f pair.1) (fun pair => g pair.2)).Equiv (SignedMoment.ofInt 0) := by
  rw [← Distro.signedCovariance_nat]
  exact μ.signedCovariance_independent ν (fun x => (f x : Int)) (fun x => (g x : Int))

end Thesis.Probability.Distros
