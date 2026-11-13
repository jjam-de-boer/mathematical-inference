import Thesis.Probability.Distros.RationalClearing

namespace Thesis.Probability.SignedRatio

theorem mul_neg (a b : SignedRatio) : Equiv (mul a (neg b)) (neg (mul a b)) := by
  simp only [Equiv, mul, neg, Int.mul_neg]

theorem mul_sub (a b c : SignedRatio) :
    Equiv (mul a (sub b c)) (sub (mul a b) (mul a c)) :=
  equiv_trans (mul_add a b (neg c)) (add_congr (equiv_refl _) (mul_neg a c))

theorem sub_mul (a b c : SignedRatio) :
    Equiv (mul (sub a b) c) (sub (mul a c) (mul b c)) :=
  equiv_trans (add_mul a (neg b) c) (add_congr (equiv_refl _) (neg_mul b c))

theorem sub_add_sub (a b c d : SignedRatio) :
    Equiv (sub (add a b) (add c d)) (add (sub a c) (sub b d)) :=
  equiv_trans (add_congr (equiv_refl _) (neg_add c d)) (add_interchange a b (neg c) (neg d))

theorem add_self_scaleNat_two (a : SignedRatio) : Equiv (add a a) (scaleNat 2 a) := by
  change (a.num * (a.den : Int) + a.num * (a.den : Int)) * (a.den : Int) =
    ((1 + 1) * a.num) * ((a.den * a.den : Nat) : Int)
  simp only [Int.natCast_mul, Int.add_mul, Int.one_mul, Int.mul_assoc]

theorem scaleNat_mul_product (m n : Nat) (a b : SignedRatio) :
    Equiv (scaleNat (m * n) (mul a b)) (mul (scaleNat m a) (scaleNat n b)) := by
  simp only [Equiv, scaleNat, mul, Int.natCast_mul]
  ac_rfl

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.Distros

/-- Rational integration factors on the actual Cartesian product of weighted
atom records. Duplicate labels and all zero-weight occurrences are retained. -/
theorem rationalAtomSum_product (left : List (Ω × Nat)) (right : List (X × Nat))
    (f : Ω → SignedRatio) (g : X → SignedRatio) :
    SignedRatio.Equiv
      (FiniteProbRecord.rationalAtomSum (left.flatMap (fun a => right.map (fun b => ((a.1, b.1), a.2 * b.2))))
        (fun pair => SignedRatio.mul (f pair.1) (g pair.2)))
      (SignedRatio.mul (FiniteProbRecord.rationalAtomSum left f) (FiniteProbRecord.rationalAtomSum right g)) := by
  have row (a : Ω × Nat) : SignedRatio.Equiv
      (SignedRatio.listSum (right.map (fun b => SignedRatio.scaleNat (a.2 * b.2) (SignedRatio.mul (f a.1) (g b.1)))))
      (SignedRatio.mul (SignedRatio.scaleNat a.2 (f a.1)) (FiniteProbRecord.rationalAtomSum right g)) := by
    refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr right _ _
      (fun b => SignedRatio.scaleNat_mul_product a.2 b.2 (f a.1) (g b.1))) ?_
    exact SignedRatio.equiv_symm (by
      simpa only [FiniteProbRecord.rationalAtomSum, List.map_map, Function.comp_def] using
        (SignedRatio.mul_listSum (SignedRatio.scaleNat a.2 (f a.1))
          (right.map (fun b => SignedRatio.scaleNat b.2 (g b.1)))))
  have grouped := SignedRatio.listSum_flatMap left
    (fun a => right.map (fun b => SignedRatio.scaleNat (a.2 * b.2) (SignedRatio.mul (f a.1) (g b.1))))
  refine SignedRatio.equiv_trans (by
    simpa only [FiniteProbRecord.rationalAtomSum, List.map_flatMap, List.map_map, Function.comp_def] using grouped) ?_
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr left _ _ row) ?_
  exact SignedRatio.equiv_symm (by
    simpa only [FiniteProbRecord.rationalAtomSum, List.map_map, Function.comp_def] using
      (SignedRatio.listSum_mul (left.map (fun a => SignedRatio.scaleNat a.2 (f a.1)))
        (FiniteProbRecord.rationalAtomSum right g)))

/-- Independent-product factorization for arbitrary signed rational responses. -/
theorem Distro.rationalExpectation_product (μ : Distro Ω) (ν : Distro X)
    (f : Ω → SignedRatio) (g : X → SignedRatio) :
    SignedRatio.Equiv ((μ.product ν).rationalExpectation (fun pair => SignedRatio.mul (f pair.1) (g pair.2)))
      (SignedRatio.mul (μ.rationalExpectation f) (ν.rationalExpectation g)) := by
  refine SignedRatio.equiv_trans (SignedRatio.divideNat_congr
    (rationalAtomSum_product μ.record.atoms ν.record.atoms f g) (μ.record.den * ν.record.den)
      (Nat.mul_pos μ.record.den_pos ν.record.den_pos)) ?_
  simp only [SignedRatio.Equiv, SignedRatio.divideNat, SignedRatio.mul,
    Distro.rationalExpectation, FiniteProbRecord.rationalMean, Int.natCast_mul]
  ac_rfl

theorem Distro.rationalExpectation_product_left (μ : Distro Ω) (ν : Distro X) (f : Ω → SignedRatio) :
    SignedRatio.Equiv ((μ.product ν).rationalExpectation (fun pair => f pair.1)) (μ.rationalExpectation f) :=
  SignedRatio.equiv_trans ((μ.product ν).rationalExpectation_congr _ _ (fun pair => SignedRatio.equiv_symm (SignedRatio.mul_one (f pair.1))))
    (SignedRatio.equiv_trans (μ.rationalExpectation_product ν f (fun _ => SignedRatio.one))
      (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (ν.rationalExpectation_constant SignedRatio.one))
        (SignedRatio.mul_one _)))

theorem Distro.rationalExpectation_product_right (μ : Distro Ω) (ν : Distro X) (g : X → SignedRatio) :
    SignedRatio.Equiv ((μ.product ν).rationalExpectation (fun pair => g pair.2)) (ν.rationalExpectation g) :=
  SignedRatio.equiv_trans ((μ.product ν).rationalExpectation_congr _ _ (fun pair => SignedRatio.equiv_symm (SignedRatio.one_mul (g pair.2))))
    (SignedRatio.equiv_trans (μ.rationalExpectation_product ν (fun _ => SignedRatio.one) g)
      (SignedRatio.equiv_trans (SignedRatio.mul_congr (μ.rationalExpectation_constant SignedRatio.one) (SignedRatio.equiv_refl _))
        (SignedRatio.one_mul _)))

theorem Distro.rationalCovariance_symm (μ : Distro Ω) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f g) (μ.rationalCovariance g f) :=
  ratio_sub_congr (μ.rationalExpectation_congr _ _ (fun x => SignedRatio.mul_comm (f x) (g x)))
    (SignedRatio.mul_comm _ _)

theorem Distro.rationalCovariance_add_left (μ : Distro Ω) (f g h : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance (fun x => SignedRatio.add (f x) (g x)) h)
      (SignedRatio.add (μ.rationalCovariance f h) (μ.rationalCovariance g h)) :=
  SignedRatio.equiv_trans (ratio_sub_congr
    (SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _ (fun x => SignedRatio.add_mul (f x) (g x) (h x)))
      (μ.rationalExpectation_add _ _))
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (μ.rationalExpectation_add f g) (SignedRatio.equiv_refl _))
      (SignedRatio.add_mul _ _ _))) (SignedRatio.sub_add_sub _ _ _ _)

theorem Distro.rationalCovariance_add_right (μ : Distro Ω) (f g h : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f (fun x => SignedRatio.add (g x) (h x)))
      (SignedRatio.add (μ.rationalCovariance f g) (μ.rationalCovariance f h)) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_symm _ _)
    (SignedRatio.equiv_trans (μ.rationalCovariance_add_left g h f)
      (SignedRatio.add_congr (μ.rationalCovariance_symm g f) (μ.rationalCovariance_symm h f)))

theorem Distro.rationalCovariance_scale_left (μ : Distro Ω) (c : SignedRatio) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance (fun x => SignedRatio.mul c (f x)) g)
      (SignedRatio.mul c (μ.rationalCovariance f g)) :=
  SignedRatio.equiv_trans (ratio_sub_congr
    (SignedRatio.equiv_trans (μ.rationalExpectation_congr _ _ (fun x => SignedRatio.mul_assoc c (f x) (g x)))
      (μ.rationalExpectation_mul_left c _))
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (μ.rationalExpectation_mul_left c f) (SignedRatio.equiv_refl _))
      (SignedRatio.mul_assoc _ _ _))) (SignedRatio.equiv_symm (SignedRatio.mul_sub _ _ _))

theorem Distro.rationalCovariance_scale_right (μ : Distro Ω) (c : SignedRatio) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance f (fun x => SignedRatio.mul c (g x)))
      (SignedRatio.mul c (μ.rationalCovariance f g)) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_symm _ _)
    (SignedRatio.equiv_trans (μ.rationalCovariance_scale_left c g f)
      (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (μ.rationalCovariance_symm g f)))

theorem Distro.rationalCovariance_constant_left (μ : Distro Ω) (c : SignedRatio) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalCovariance (fun _ => c) f) SignedRatio.zero :=
  SignedRatio.equiv_trans (ratio_sub_congr (μ.rationalExpectation_mul_left c f)
    (SignedRatio.mul_congr (μ.rationalExpectation_constant c) (SignedRatio.equiv_refl _)))
    ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_refl _))

theorem Distro.rationalCovariance_independent (μ : Distro Ω) (ν : Distro X)
    (f : Ω → SignedRatio) (g : X → SignedRatio) :
    SignedRatio.Equiv ((μ.product ν).rationalCovariance (fun pair => f pair.1) (fun pair => g pair.2)) SignedRatio.zero :=
  SignedRatio.equiv_trans (ratio_sub_congr (μ.rationalExpectation_product ν f g)
    (SignedRatio.mul_congr (μ.rationalExpectation_product_left ν f) (μ.rationalExpectation_product_right ν g)))
    ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_refl _))

/-- Dependent rational observables retain both covariance cross terms. -/
theorem Distro.rationalVariance_add (μ : Distro Ω) (f g : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalVariance (fun x => SignedRatio.add (f x) (g x)))
      (SignedRatio.add (SignedRatio.add (μ.rationalVariance f) (μ.rationalVariance g))
        (SignedRatio.scaleNat 2 (μ.rationalCovariance f g))) := by
  have expand := SignedRatio.equiv_trans (μ.rationalCovariance_add_left f g (fun x => SignedRatio.add (f x) (g x)))
    (SignedRatio.add_congr (μ.rationalCovariance_add_right f f g) (μ.rationalCovariance_add_right g f g))
  refine SignedRatio.equiv_trans expand ?_
  refine SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _)
    (SignedRatio.add_congr (μ.rationalCovariance_symm g f) (SignedRatio.equiv_refl _))) ?_
  refine SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.equiv_refl _)
    (SignedRatio.add_comm _ _)) ?_
  exact SignedRatio.equiv_trans (SignedRatio.add_interchange _ _ _ _)
    (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.add_self_scaleNat_two _))

theorem Distro.rationalVariance_scale (μ : Distro Ω) (c : SignedRatio) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalVariance (fun x => SignedRatio.mul c (f x)))
      (SignedRatio.mul (SignedRatio.mul c c) (μ.rationalVariance f)) :=
  SignedRatio.equiv_trans (μ.rationalCovariance_scale_left c f (fun x => SignedRatio.mul c (f x)))
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (μ.rationalCovariance_scale_right c f f))
      (SignedRatio.equiv_symm (SignedRatio.mul_assoc _ _ _)))

end Thesis.Probability.Distros
