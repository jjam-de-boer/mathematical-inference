import Thesis.Probability.Distros.Basic

namespace Thesis.Probability.Distros

open Combinatorics

/-!
Finite expectations and independent sums.  Natural observables are summed
on the record's existing denominator; variance retains its witnessed
`QProb.sub` definition.  All identities apply to arbitrary outcome types.
-/

/-- The unnormalised integral of a natural observable. -/
def natIntegral (atoms : List (Ω × Nat)) (f : Ω → Nat) : Nat :=
  match atoms with
  | [] => 0
  | atom :: rest => atom.2 * f atom.1 + natIntegral rest f

theorem natIntegral_congr (atoms : List (Ω × Nat)) (f g : Ω → Nat)
    (h : forall value, f value = g value) : natIntegral atoms f = natIntegral atoms g := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp only [natIntegral, h, ih]

theorem natIntegral_map (atoms : List (Ω × Nat)) (g : Ω → X) (f : X → Nat) :
    natIntegral (atoms.map (fun atom => (g atom.1, atom.2))) f =
      natIntegral atoms (fun value => f (g value)) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp only [List.map_cons, natIntegral, ih]

theorem natIntegral_add (atoms : List (Ω × Nat)) (f g : Ω → Nat) :
    natIntegral atoms (fun value => f value + g value) =
      natIntegral atoms f + natIntegral atoms g := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp only [natIntegral, Nat.mul_add, ih]; ac_rfl

theorem natIntegral_mul (atoms : List (Ω × Nat)) (f : Ω → Nat) (c : Nat) :
    natIntegral atoms (fun value => f value * c) = natIntegral atoms f * c := by
  induction atoms with
  | nil => simp only [natIntegral, Nat.zero_mul]
  | cons atom rest ih => simp only [natIntegral, ih, Nat.add_mul, Nat.mul_assoc]

theorem natIntegral_constant (atoms : List (Ω × Nat)) (c : Nat) :
    natIntegral atoms (fun _ => c) = FiniteProbRecord.totalMass atoms * c := by
  induction atoms with
  | nil => simp only [natIntegral, FiniteProbRecord.totalMass, Nat.zero_mul]
  | cons atom rest ih =>
      simp only [natIntegral, FiniteProbRecord.totalMass, ih, Nat.add_mul]

theorem natIntegral_append (left right : List (Ω × Nat)) (f : Ω → Nat) :
    natIntegral (left ++ right) f = natIntegral left f + natIntegral right f := by
  induction left with
  | nil => simp only [List.nil_append, natIntegral, Nat.zero_add]
  | cons atom rest ih => simp only [List.cons_append, natIntegral, ih, Nat.add_assoc]

theorem natIntegral_finWeighted (n : Nat) (w : Fin n → Nat) (f : Nat → Nat) :
    natIntegral (finWeighted n w) (fun value => f value.val) =
      natSum n (fun k => finWeight w k * f k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finWeighted, natIntegral_append, natIntegral_map,
        natIntegral, Fin.val_castSucc, Fin.val_last, Nat.add_zero]
      rw [ih]
      have hprefix : natSum n (fun k => finWeight (fun j => w j.castSucc) k * f k) =
          natSum n (fun k => finWeight w k * f k) := by
        apply natSum_congr
        intro k hk
        simp only [finWeight, dif_pos hk, dif_pos (Nat.lt_succ_of_lt hk)]
        rfl
      have last : finWeight w n = w (Fin.last n) := by
        simp only [finWeight, dif_pos (Nat.lt_succ_self n)]
        exact congrArg w (Fin.ext rfl)
      rw [hprefix, natSum_succ, last]

theorem natIntegral_product (left : List (Ω × Nat)) (right : List (X × Nat))
    (f : Ω → Nat) (g : X → Nat) :
    natIntegral (FiniteProbRecord.weightedCartesian left right)
        (fun pair => f pair.1 * g pair.2) =
      natIntegral left f * natIntegral right g := by
  have row (atom : Ω × Nat) :
      natIntegral (right.map (fun other => ((atom.1, other.1), atom.2 * other.2)))
          (fun pair => f pair.1 * g pair.2) =
        atom.2 * f atom.1 * natIntegral right g := by
    induction right with
    | nil => simp only [List.map_nil, natIntegral, Nat.mul_zero]
    | cons other rest ih =>
        simp only [List.map_cons, natIntegral, ih, Nat.mul_add]; ac_rfl
  induction left with
  | nil => simp only [FiniteProbRecord.weightedCartesian, List.flatMap_nil,
      natIntegral, Nat.zero_mul]
  | cons atom rest ih =>
      simp only [FiniteProbRecord.weightedCartesian, List.flatMap_cons,
        natIntegral_append, row] at *
      rw [ih]
      simp only [natIntegral, Nat.add_mul, Nat.mul_assoc]

theorem natIntegral_product_left (left : List (Ω × Nat)) (right : List (X × Nat))
    (f : Ω → Nat) :
    natIntegral (FiniteProbRecord.weightedCartesian left right) (fun pair => f pair.1) =
      natIntegral left f * FiniteProbRecord.totalMass right := by
  have h := natIntegral_product left right f (fun _ => 1)
  simpa only [Nat.mul_one, natIntegral_constant] using h

theorem natIntegral_product_right (left : List (Ω × Nat)) (right : List (X × Nat))
    (g : X → Nat) :
    natIntegral (FiniteProbRecord.weightedCartesian left right) (fun pair => g pair.2) =
      FiniteProbRecord.totalMass left * natIntegral right g := by
  have h := natIntegral_product left right (fun _ => 1) g
  simpa only [Nat.one_mul, natIntegral_constant, Nat.mul_one] using h

namespace Distro

/-- Expectation of a natural observable, allowing values above one. -/
def expectNat (μ : Distro Ω) (f : Ω → Nat) : QProb :=
  ⟨natIntegral μ.record.atoms f, μ.record.den, μ.record.den_pos⟩

theorem expectNat_map (μ : Distro Ω) (g : Ω → X) (f : X → Nat) :
    (μ.map g).expectNat f = μ.expectNat (fun value => f (g value)) := by
  simp only [expectNat, map, FiniteProbRecord.map, natIntegral_map]

theorem expectNat_add (μ : Distro Ω) (f g : Ω → Nat) :
    QProb.Equiv (μ.expectNat (fun value => f value + g value))
      (QProb.add (μ.expectNat f) (μ.expectNat g)) := by
  simp only [expectNat, natIntegral_add, QProb.Equiv, QProb.add, Nat.add_mul]
  ac_rfl

theorem expectNat_constant (μ : Distro Ω) (c : Nat) :
    QProb.Equiv (μ.expectNat (fun _ => c)) (QProb.ofNat c) := by
  simp only [expectNat, natIntegral_constant, μ.record.total_mass, QProb.Equiv,
    QProb.ofNat, Nat.mul_one, Nat.mul_comm]

theorem expectNat_scale (μ : Distro Ω) (f : Ω → Nat) (c : Nat) :
    QProb.Equiv (μ.expectNat (fun value => f value * c))
      (QProb.scale c (μ.expectNat f)) := by
  simp only [expectNat, natIntegral_mul, QProb.Equiv, QProb.scale]
  ac_rfl

/-- Independent product, before choosing any observable. -/
def product (μ : Distro Ω) (ν : Distro X) : Distro (Ω × X) :=
  ⟨μ.record.product ν.record⟩

theorem expectNat_product (μ : Distro Ω) (ν : Distro X) (f : Ω → Nat) (g : X → Nat) :
    QProb.Equiv ((μ.product ν).expectNat (fun pair => f pair.1 * g pair.2))
      (QProb.mul (μ.expectNat f) (ν.expectNat g)) := by
  simp only [expectNat, product, FiniteProbRecord.product, natIntegral_product,
    QProb.Equiv, QProb.mul]

end Distro

theorem rawMoment_expectNat (μ : NatDistro Ω) (power : Nat) :
    rawMoment μ power = μ.distro.expectNat (fun value => μ.embed value ^ power) := by
  have h (atoms : List (Ω × Nat)) :
      weightedPowSum power (atoms.map (fun atom => (μ.embed atom.1, atom.2))) =
        natIntegral atoms (fun value => μ.embed value ^ power) := by
    induction atoms with
    | nil => rfl
    | cons atom rest ih => simp only [List.map_cons, weightedPowSum, natIntegral, ih]
  simp only [rawMoment, natAtoms, Distro.expectNat, h]

theorem mean_expectNat (μ : NatDistro Ω) :
    mean μ = μ.distro.expectNat μ.embed := by
  simp only [mean, rawMoment_expectNat, Nat.pow_one]

/-- Independent natural-valued sum, retaining both sampled outcomes. -/
def independentSum (μ : NatDistro Ω) (ν : NatDistro X) : NatDistro (Ω × X) :=
  ⟨μ.distro.product ν.distro, fun pair => μ.embed pair.1 + ν.embed pair.2⟩

theorem independentSum_mean (μ : NatDistro Ω) (ν : NatDistro X) :
    QProb.Equiv (mean (independentSum μ ν)) (QProb.add (mean μ) (mean ν)) := by
  simp only [mean_expectNat, independentSum, Distro.expectNat, Distro.product,
    FiniteProbRecord.product, natIntegral_add, natIntegral_product_left,
    natIntegral_product_right, μ.distro.record.total_mass, ν.distro.record.total_mass,
    QProb.Equiv, QProb.add]
  ac_rfl

theorem independentSum_secondMoment (μ : NatDistro Ω) (ν : NatDistro X) :
    QProb.Equiv (secondMoment (independentSum μ ν))
      (QProb.add (QProb.add (secondMoment μ) (secondMoment ν))
        (QProb.scale 2 (QProb.mul (mean μ) (mean ν)))) := by
  have square (a b : Nat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by
    have htwo : 2 * (a * b) = a * b + a * b := by omega
    rw [htwo]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.add_mul, Nat.mul_add]
    ac_rfl
  simp only [secondMoment, rawMoment_expectNat, mean_expectNat, independentSum,
    Distro.expectNat, Distro.product, FiniteProbRecord.product, square,
    natIntegral_add]
  have hcross : natIntegral
      (FiniteProbRecord.weightedCartesian μ.distro.record.atoms ν.distro.record.atoms)
      (fun pair => 2 * (μ.embed pair.1 * ν.embed pair.2)) =
        2 * (natIntegral μ.distro.record.atoms μ.embed *
          natIntegral ν.distro.record.atoms ν.embed) := by
    have hf : (fun pair : Ω × X => 2 * (μ.embed pair.1 * ν.embed pair.2)) =
        (fun pair => (μ.embed pair.1 * ν.embed pair.2) * 2) := by
      funext pair
      exact Nat.mul_comm _ _
    rw [hf]
    rw [natIntegral_mul, natIntegral_product, Nat.mul_comm _ 2]
  rw [natIntegral_product_left μ.distro.record.atoms ν.distro.record.atoms
      (fun value => μ.embed value ^ 2),
    natIntegral_product_right μ.distro.record.atoms ν.distro.record.atoms
      (fun value => ν.embed value ^ 2), hcross]
  simp only [
    μ.distro.record.total_mass, ν.distro.record.total_mass,
    QProb.Equiv, QProb.add, QProb.scale, QProb.mul, Nat.add_mul]
  ac_rfl

/-- Rational addition can be cancelled without selecting canonical fractions. -/
theorem qprob_add_cancel_right (p q r : QProb)
    (h : QProb.Equiv (QProb.add p r) (QProb.add q r)) : QProb.Equiv p q := by
  have h' : p.num * q.den * (r.den * r.den) + r.num * p.den * q.den * r.den =
      q.num * p.den * (r.den * r.den) + r.num * p.den * q.den * r.den := by
    calc
      _ = (p.num * r.den + r.num * p.den) * (q.den * r.den) := by
        simp only [Nat.add_mul]; ac_rfl
      _ = (q.num * r.den + r.num * q.den) * (p.den * r.den) := h
      _ = _ := by simp only [Nat.add_mul]; ac_rfl
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos r.den_pos r.den_pos)
    (Nat.add_right_cancel h')

theorem qprob_add_four (a b c d : QProb) :
    QProb.Equiv (QProb.add (QProb.add a b) (QProb.add c d))
      (QProb.add (QProb.add a c) (QProb.add b d)) := by
  simp only [QProb.Equiv, QProb.add, Nat.add_mul]
  ac_rfl

theorem qprob_square_add (a b : QProb) :
    QProb.Equiv (QProb.mul (QProb.add a b) (QProb.add a b))
      (QProb.add (QProb.add (QProb.mul a a) (QProb.mul b b))
        (QProb.scale 2 (QProb.mul a b))) := by
  have twice (n : Nat) : 2 * n = n + n := by omega
  simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.scale, twice,
    Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem meanSq_equiv_mul (μ : NatDistro Ω) :
    QProb.Equiv (meanSq μ) (QProb.mul (mean μ) (mean μ)) := by
  exact QProb.equiv_refl _

/-- The defining witnessed subtraction recovers the second moment. -/
theorem variance_balance (μ : NatDistro Ω) :
    QProb.Equiv (QProb.add (variance μ) (QProb.mul (mean μ) (mean μ)))
      (secondMoment μ) := by
  exact QProb.equiv_trans
    (QProb.sub_add (secondMomentScaled μ) (meanSq μ) (meanSq_le_secondMoment μ))
    (secondMomentScaled_equiv μ)

/-- A proposed variance is determined by the checked second-moment balance. -/
theorem variance_eq_of_balance (μ : NatDistro Ω) (value : QProb)
    (balance : QProb.Equiv (QProb.add value (QProb.mul (mean μ) (mean μ)))
      (secondMoment μ)) : QProb.Equiv (variance μ) value := by
  apply qprob_add_cancel_right _ _ (QProb.mul (mean μ) (mean μ))
  exact QProb.equiv_trans (variance_balance μ) (QProb.equiv_symm balance)

theorem closedMoments_cauchy (μ : NatDistro Ω) (m s : QProb)
    (hm : QProb.Equiv (mean μ) m) (hs : QProb.Equiv (secondMoment μ) s) :
    QProb.LE (QProb.mul m m) s :=
  QProb.le_congr (QProb.equiv_trans (meanSq_equiv_mul μ) (QProb.mul_congr hm hm))
    (QProb.equiv_trans (secondMomentScaled_equiv μ) hs) (meanSq_le_secondMoment μ)

/-- Closed moment formulas transport the original variance witness. -/
theorem variance_closed_moments (μ : NatDistro Ω) (m s : QProb)
    (hm : QProb.Equiv (mean μ) m) (hs : QProb.Equiv (secondMoment μ) s) :
    QProb.Equiv (variance μ)
      (QProb.sub s (QProb.mul m m) (closedMoments_cauchy μ m s hm hs)) :=
  QProb.sub_congr (QProb.equiv_trans (secondMomentScaled_equiv μ) hs)
    (QProb.equiv_trans (meanSq_equiv_mul μ) (QProb.mul_congr hm hm))
    (meanSq_le_secondMoment μ) (closedMoments_cauchy μ m s hm hs)

/-- Independent sums have additive variance, using the existing subtraction witness. -/
theorem independentSum_variance (μ : NatDistro Ω) (ν : NatDistro X) :
    QProb.Equiv (variance (independentSum μ ν))
      (QProb.add (variance μ) (variance ν)) := by
  let m := QProb.add (mean μ) (mean ν)
  let cross := QProb.scale 2 (QProb.mul (mean μ) (mean ν))
  let squares := QProb.add (QProb.mul (mean μ) (mean μ))
    (QProb.mul (mean ν) (mean ν))
  have combined : QProb.Equiv
      (QProb.add (QProb.add (variance μ) (variance ν)) (QProb.mul m m))
      (QProb.add (QProb.add (secondMoment μ) (secondMoment ν)) cross) := by
    refine QProb.equiv_trans
      (QProb.add_congr (QProb.equiv_refl _) (qprob_square_add (mean μ) (mean ν))) ?_
    refine QProb.equiv_trans
      (QProb.equiv_symm (QProb.add_assoc _ squares cross)) ?_
    exact QProb.add_congr
      (QProb.equiv_trans (qprob_add_four _ _ _ _)
        (QProb.add_congr (variance_balance μ) (variance_balance ν))) (QProb.equiv_refl _)
  apply qprob_add_cancel_right _ _ (QProb.mul m m)
  refine QProb.equiv_trans ?_ (QProb.equiv_symm combined)
  refine QProb.equiv_trans
    (QProb.add_congr (QProb.equiv_refl _)
      (QProb.mul_congr (QProb.equiv_symm (independentSum_mean μ ν))
        (QProb.equiv_symm (independentSum_mean μ ν)))) ?_
  exact QProb.equiv_trans (variance_balance (independentSum μ ν))
    (independentSum_secondMoment μ ν)

/-- Unnormalised integral for arbitrary nonnegative rational observables. -/
def rationalIntegral (atoms : List (Ω × Nat)) (f : Ω → QProb) : QProb :=
  QProb.listSum (atoms.map (fun atom => QProb.scale atom.2 (f atom.1)))

theorem rationalIntegral_congr (atoms : List (Ω × Nat)) (f g : Ω → QProb)
    (h : forall value, QProb.Equiv (f value) (g value)) :
    QProb.Equiv (rationalIntegral atoms f) (rationalIntegral atoms g) :=
  QProb.listSum_map_congr atoms _ _ (fun atom => QProb.scale_congr atom.2 (h atom.1))

theorem rationalIntegral_map (atoms : List (Ω × Nat)) (g : Ω → X) (f : X → QProb) :
    rationalIntegral (atoms.map (fun atom => (g atom.1, atom.2))) f =
      rationalIntegral atoms (fun value => f (g value)) := by
  simp only [rationalIntegral, List.map_map, Function.comp_def]

theorem rationalIntegral_add (atoms : List (Ω × Nat)) (f g : Ω → QProb) :
    QProb.Equiv (rationalIntegral atoms (fun value => QProb.add (f value) (g value)))
      (QProb.add (rationalIntegral atoms f) (rationalIntegral atoms g)) := by
  induction atoms with
  | nil =>
      simp only [rationalIntegral, List.map_nil, QProb.listSum]
      exact QProb.equiv_symm (QProb.add_zero _)
  | cons atom rest ih =>
      have scaleAdd : QProb.Equiv
          (QProb.scale atom.2 (QProb.add (f atom.1) (g atom.1)))
          (QProb.add (QProb.scale atom.2 (f atom.1)) (QProb.scale atom.2 (g atom.1))) := by
        simp only [QProb.Equiv, QProb.scale, QProb.add, Nat.mul_add, Nat.add_mul]
        ac_rfl
      exact QProb.equiv_trans (QProb.add_congr scaleAdd ih) (qprob_add_four _ _ _ _)

theorem rationalIntegral_nat (atoms : List (Ω × Nat)) (f : Ω → Nat) :
    QProb.Equiv (rationalIntegral atoms (fun value => QProb.ofNat (f value)))
      (QProb.ofNat (natIntegral atoms f)) := by
  induction atoms with
  | nil => exact QProb.equiv_refl _
  | cons atom rest ih =>
      refine QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) ih) ?_
      simp only [natIntegral, QProb.Equiv, QProb.add, QProb.scale, QProb.ofNat,
        Nat.mul_one]

theorem rationalIntegral_product (left : List (Ω × Nat)) (right : List (X × Nat))
    (f : Ω → QProb) (g : X → QProb) :
    QProb.Equiv (rationalIntegral (FiniteProbRecord.weightedCartesian left right)
        (fun pair => QProb.mul (f pair.1) (g pair.2)))
      (QProb.mul (rationalIntegral left f) (rationalIntegral right g)) := by
  have row (atom : Ω × Nat) : QProb.Equiv
      (QProb.listSum (right.map (fun other =>
        QProb.scale (atom.2 * other.2) (QProb.mul (f atom.1) (g other.1)))))
      (QProb.mul (QProb.scale atom.2 (f atom.1)) (rationalIntegral right g)) := by
    refine QProb.equiv_trans (QProb.listSum_map_congr right _
      (fun other => QProb.mul (QProb.scale atom.2 (f atom.1))
        (QProb.scale other.2 (g other.1))) (fun other => ?_)) ?_
    · change QProb.Equiv
        (QProb.scale (atom.2 * other.2) (QProb.mul (f atom.1) (g other.1)))
        (QProb.mul (QProb.scale atom.2 (f atom.1)) (QProb.scale other.2 (g other.1)))
      simp only [QProb.Equiv, QProb.scale, QProb.mul]; ac_rfl
    · simpa only [rationalIntegral, List.map_map, Function.comp_def] using
        QProb.equiv_symm (QProb.mul_listSum (QProb.scale atom.2 (f atom.1))
          (right.map (fun other => QProb.scale other.2 (g other.1))))
  simp only [rationalIntegral, FiniteProbRecord.weightedCartesian,
    List.map_flatMap, List.map_map, Function.comp_def]
  refine QProb.equiv_trans (QProb.listSum_flatMap left _) ?_
  refine QProb.equiv_trans (QProb.listSum_map_congr left _ _ row) ?_
  simpa only [rationalIntegral, List.map_map, Function.comp_def] using
    QProb.equiv_symm (QProb.listSum_mul
      (left.map (fun atom => QProb.scale atom.2 (f atom.1))) (rationalIntegral right g))

namespace Distro

/-- Finite expectation of a nonnegative rational observable. -/
def expectation (μ : Distro Ω) (f : Ω → QProb) : QProb :=
  QProb.div (rationalIntegral μ.record.atoms f) (QProb.ofNat μ.record.den) μ.record.den_pos

theorem expectation_congr (μ : Distro Ω) (f g : Ω → QProb)
    (h : forall value, QProb.Equiv (f value) (g value)) :
    QProb.Equiv (μ.expectation f) (μ.expectation g) :=
  QProb.div_congr (rationalIntegral_congr _ _ _ h) (QProb.equiv_refl _)
    μ.record.den_pos μ.record.den_pos

theorem expectation_map (μ : Distro Ω) (g : Ω → X) (f : X → QProb) :
    (μ.map g).expectation f = μ.expectation (fun value => f (g value)) := by
  simp only [expectation, map, FiniteProbRecord.map, rationalIntegral_map]

theorem expectation_add (μ : Distro Ω) (f g : Ω → QProb) :
    QProb.Equiv (μ.expectation (fun value => QProb.add (f value) (g value)))
      (QProb.add (μ.expectation f) (μ.expectation g)) := by
  exact QProb.equiv_trans
    (QProb.div_congr (rationalIntegral_add _ _ _) (QProb.equiv_refl _)
      μ.record.den_pos μ.record.den_pos)
    (QProb.div_add_same_denominator _ _ _ μ.record.den_pos)

theorem expectation_nat (μ : Distro Ω) (f : Ω → Nat) :
    QProb.Equiv (μ.expectation (fun value => QProb.ofNat (f value))) (μ.expectNat f) := by
  refine QProb.equiv_trans
    (QProb.div_congr (rationalIntegral_nat _ _) (QProb.equiv_refl _)
      μ.record.den_pos μ.record.den_pos) ?_
  simp only [expectNat, QProb.Equiv, QProb.div, QProb.ofNat,
    Nat.mul_one, Nat.one_mul]

theorem expectation_product (μ : Distro Ω) (ν : Distro X)
    (f : Ω → QProb) (g : X → QProb) :
    QProb.Equiv ((μ.product ν).expectation (fun pair => QProb.mul (f pair.1) (g pair.2)))
      (QProb.mul (μ.expectation f) (ν.expectation g)) := by
  refine QProb.equiv_trans
    (QProb.div_congr (rationalIntegral_product μ.record.atoms ν.record.atoms f g)
      (QProb.equiv_refl _) (Nat.mul_pos μ.record.den_pos ν.record.den_pos)
      (Nat.mul_pos μ.record.den_pos ν.record.den_pos)) ?_
  simp only [expectation, product, FiniteProbRecord.product,
    QProb.Equiv, QProb.div, QProb.mul, QProb.ofNat, Nat.mul_one]
  ac_rfl

end Distro

theorem qpow_add (s : QProb) (a b : Nat) :
    QProb.Equiv (qpow s (a + b)) (QProb.mul (qpow s a) (qpow s b)) := by
  simp only [QProb.Equiv, QProb.mul, qpow_num, qpow_den, Nat.pow_add]

theorem pgf_expectation (μ : NatDistro Ω) (s : QProb) :
    pgf μ s = μ.distro.expectation (fun value => qpow s (μ.embed value)) := rfl

/-- The PGF of an independent sum factors at every nonnegative rational argument. -/
theorem independentSum_pgf (μ : NatDistro Ω) (ν : NatDistro X) (s : QProb) :
    QProb.Equiv (pgf (independentSum μ ν) s) (QProb.mul (pgf μ s) (pgf ν s)) := by
  rw [pgf_expectation, pgf_expectation, pgf_expectation]
  exact QProb.equiv_trans
    (Distro.expectation_congr (μ.distro.product ν.distro)
      (fun pair => qpow s (μ.embed pair.1 + ν.embed pair.2))
      (fun pair => QProb.mul (qpow s (μ.embed pair.1)) (qpow s (ν.embed pair.2)))
      (fun pair => qpow_add s _ _))
    (Distro.expectation_product μ.distro ν.distro
      (fun value => qpow s (μ.embed value)) (fun value => qpow s (ν.embed value)))

namespace NatDistro

/-- Map outcomes and choose their numeric observable. -/
def map (μ : NatDistro Ω) (g : Ω → X) (value : X → Nat) : NatDistro X :=
  ⟨μ.distro.map g, value⟩

theorem rawMoment_map (μ : NatDistro Ω) (g : Ω → X) (value : X → Nat) (power : Nat) :
    rawMoment (μ.map g value) power =
      rawMoment ⟨μ.distro, fun x => value (g x)⟩ power := by
  simp only [rawMoment_expectNat, map, Distro.expectNat_map]

theorem mean_map (μ : NatDistro Ω) (g : Ω → X) (value : X → Nat) :
    mean (μ.map g value) = mean ⟨μ.distro, fun x => value (g x)⟩ :=
  rawMoment_map μ g value 1

theorem variance_map (μ : NatDistro Ω) (g : Ω → X) (value : X → Nat) :
    variance (μ.map g value) = variance ⟨μ.distro, fun x => value (g x)⟩ := by
  unfold variance QProb.sub secondMomentScaled meanSq secondMoment
  simp only [rawMoment_map, mean_map]
  rfl

theorem pgf_map (μ : NatDistro Ω) (g : Ω → X) (value : X → Nat) (s : QProb) :
    pgf (μ.map g value) s = pgf ⟨μ.distro, fun x => value (g x)⟩ s := by
  simp only [pgf_expectation, map, Distro.expectation_map]

end NatDistro

end Thesis.Probability.Distros
