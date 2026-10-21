import Thesis.Probability.EntropyIncrement

namespace Thesis.Probability

/-- Additive, symmetric comparison of exact entropy contributions. -/
def EntropyWithin (p q : QProb) (error : ExactLog) : Prop :=
  ExactLog.LE (entropyTerm p) (ExactLog.add (entropyTerm q) error) ∧
  ExactLog.LE (entropyTerm q) (ExactLog.add (entropyTerm p) error)

private theorem dyadic_linear (m e : Nat) :
    ExactLog.scaleRatio ⟨1, 2 ^ e, Nat.pow_pos (by decide)⟩
      (ExactLog.log (PositiveRatio.ofNat (2 ^ m) (Nat.pow_pos (by decide)))) =
    ExactLog.ofSignedRatio ⟨(m : Int), 2 ^ e, Nat.pow_pos (by decide)⟩ := by
  apply ExactLog.ext
  · apply PositiveRatio.ext <;>
      simp only [ExactLog.scaleRatio, ExactLog.log, PositiveRatio.ofNat, PositiveRatio.pow,
        ExactLog.ofSignedRatio, Int.toNat_natCast, Int.toNat_neg_natCast, Nat.pow_zero, Nat.pow_one]
  · simp only [ExactLog.scaleRatio, ExactLog.log, ExactLog.ofSignedRatio, Nat.one_mul]

private theorem precision_coefficient (n : Nat) : 2 * n + 5 ≤ 2 ^ (2 * n + 6) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have scaled := Nat.mul_le_mul_left 4 ih
      have next : 2 ^ (2 * (n + 1) + 6) = 4 * 2 ^ (2 * n + 6) := by
        rw [show 2 * (n + 1) + 6 = (2 * n + 6) + 2 by omega, Nat.pow_add, show 2 ^ 2 = 4 by decide, Nat.mul_comm]
      rw [next]
      omega

private theorem linear_error (n : Nat) :
    ExactLog.LE (ExactLog.scaleRatio ⟨1, 2 ^ (3 * n + 6), Nat.pow_pos (by decide)⟩
      (ExactLog.log (PositiveRatio.ofNat (2 ^ (2 * n + 5)) (Nat.pow_pos (by decide)))))
      (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩) := by
  rw [dyadic_linear]
  apply (ExactLog.ofSignedRatio_le_iff _ _).mpr
  have scaled := Nat.mul_le_mul_right (2 ^ n) (precision_coefficient n)
  have powers : 2 ^ (2 * n + 6) * 2 ^ n = 2 ^ (3 * n + 6) := by rw [← Nat.pow_add]; congr 1; omega
  rw [powers] at scaled
  simpa only [Int.one_mul, ← Int.natCast_mul, Int.ofNat_le] using scaled

private theorem small_pair (p q : QProb) (pBound : p.num ≤ p.den) (qBound : q.num ≤ q.den) (n : Nat)
    (first : QProb.LE p ⟨1, 2 ^ (2 * n + 4), Nat.pow_pos (by decide)⟩)
    (second : QProb.LE q ⟨1, 2 ^ (2 * n + 4), Nat.pow_pos (by decide)⟩) :
    EntropyWithin p q (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩) := by
  have pSmall := entropyTerm_boundary_precision p pBound n first
  have qSmall := entropyTerm_boundary_precision q qBound n second
  have pNonnegative := entropyTerm_nonnegative p (by simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using pBound)
  have qNonnegative := entropyTerm_nonnegative q (by simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using qBound)
  have firstLift := (ExactLog.add_le_add_right_iff ExactLog.zero (entropyTerm q)
    (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩)).mpr qNonnegative
  have secondLift := (ExactLog.add_le_add_right_iff ExactLog.zero (entropyTerm p)
    (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩)).mpr pNonnegative
  rw [ExactLog.zero_add] at firstLift secondLift
  exact ⟨ExactLog.le_trans pSmall firstLift, ExactLog.le_trans qSmall secondLift⟩

/-- Common-denominator two-point modulus, including both zero boundaries. -/
theorem entropyTerm_continuity_same_den (den a b n : Nat) (denPositive : 0 < den)
    (aBound : a ≤ den) (bBound : b ≤ den) (ordered : b ≤ a)
    (close : (a - b) * 2 ^ (3 * n + 6) ≤ den) :
    EntropyWithin ⟨a, den, denPositive⟩ ⟨b, den, denPositive⟩
      (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩) := by
  let T := 2 ^ (2 * n + 5)
  let R := 2 ^ (n + 1)
  let E := 2 ^ (3 * n + 6)
  let S := 2 ^ (2 * n + 4)
  have tPositive : 0 < T := Nat.pow_pos (by decide)
  have rPositive : 0 < R := Nat.pow_pos (by decide)
  have sPositive : 0 < S := Nat.pow_pos (by decide)
  have factors : T * R = E := by dsimp [T, R, E]; rw [← Nat.pow_add]; congr 1; omega
  have twice : T = 2 * S := by dsimp [T, S]; rw [show 2 * n + 5 = (2 * n + 4) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have recovered : a - b + b = a := Nat.sub_add_cancel ordered
  by_cases large : den ≤ b * T
  · have bPositive : 0 < b := by
      by_cases zero : b = 0
      · simp only [zero, Nat.zero_mul] at large
        omega
      · exact Nat.pos_of_ne_zero zero
    have aPositive : 0 < a := Nat.lt_of_lt_of_le bPositive ordered
    have gap : (a - b) * R ≤ b := by
      have multiplied : ((a - b) * R) * T ≤ b * T := by
        have chained := Nat.le_trans close large
        change (a - b) * E ≤ b * T at chained
        rw [← factors] at chained
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using chained
      exact Nat.le_of_mul_le_mul_right multiplied tPositive
    have ratioBound : a * (R - 1) ≤ R * b := by
      have removed : R - 1 + 1 = R := Nat.sub_add_cancel rPositive
      have smallGap : (a - b) * (R - 1) ≤ b := Nat.le_trans (Nat.mul_le_mul_left (a - b) (Nat.sub_le R 1)) gap
      have bound := Nat.add_le_add_left smallGap (b * (R - 1))
      calc
        a * (R - 1) = b * (R - 1) + (a - b) * (R - 1) := by rw [← Nat.add_mul, Nat.add_comm b, recovered]
        _ ≤ b * (R - 1) + b := bound
        _ = b * ((R - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = R * b := by rw [removed, Nat.mul_comm]
    let p : QProb := ⟨a, den, denPositive⟩
    let q : QProb := ⟨b, den, denPositive⟩
    have pBounded : QProb.LE p QProb.one := by simpa only [p, QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using aBound
    have qBelow : QProb.LE q p := Nat.mul_le_mul_right den ordered
    have increments := entropyTerm_increment_bounds p q aPositive bPositive pBounded qBelow
    have gapPresentation : QProb.Equiv (QProb.sub p q qBelow) ⟨a - b, den, denPositive⟩ := by
      change (a * den - b * den) * den = (a - b) * (den * den)
      rw [← Nat.mul_sub_right_distrib]; ac_rfl
    have gapSmall : QProb.LE (QProb.sub p q qBelow) ⟨1, E, Nat.pow_pos (by decide)⟩ :=
      QProb.le_congr (QProb.equiv_symm gapPresentation) (QProb.equiv_refl _)
        (by simpa only [QProb.LE, Nat.one_mul] using close)
    have scoreBound : ExactLog.LE (ExactLog.log ⟨den, a, denPositive, aPositive⟩)
        (ExactLog.log (PositiveRatio.ofNat T tPositive)) := by
      apply (ExactLog.log_le_log_iff _ _).mpr
      have bound := Nat.le_trans large (Nat.mul_le_mul_right T ordered)
      simpa only [PositiveRatio.LE, PositiveRatio.toQProb, PositiveRatio.ofNat, QProb.LE, Nat.mul_one, Nat.mul_comm] using bound
    have scoreNonnegative : ExactLog.LE ExactLog.zero (ExactLog.log (PositiveRatio.ofNat T tPositive)) := by
      apply (ExactLog.log_le_log_iff PositiveRatio.one _).mpr
      simpa only [PositiveRatio.LE, PositiveRatio.toQProb, PositiveRatio.ofNat, PositiveRatio.one, QProb.LE, Nat.mul_one, Nat.one_mul] using tPositive
    have linearBound := ExactLog.le_trans (ExactLog.scaleRatio_mono (QProb.sub p q qBelow) scoreBound)
      (ExactLog.scaleRatio_weight_mono gapSmall _ scoreNonnegative)
    have firstError := ExactLog.le_trans linearBound (linear_error n)
    have ratioOrder : ExactLog.LE (ExactLog.log (PositiveRatio.mul
        ⟨a, den, aPositive, denPositive⟩ (PositiveRatio.inv ⟨b, den, bPositive, denPositive⟩)))
        (ExactLog.log ⟨R, R - 1, rPositive, by
          dsimp [R]
          have power : 1 < 2 ^ (n + 1) := by rw [Nat.pow_succ]; have h : 0 < 2 ^ n := Nat.pow_pos (by decide); omega
          exact Nat.sub_pos_of_lt power⟩) := by
      apply (ExactLog.log_le_log_iff _ _).mpr
      change (a * den) * (R - 1) ≤ R * (den * b)
      have multiplied := Nat.mul_le_mul_right den ratioBound
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using multiplied
    have rLarge : 1 < R := by dsimp [R]; rw [Nat.pow_succ]; have h : 0 < 2 ^ n := Nat.pow_pos (by decide); omega
    have ratioError := ExactLog.le_trans ratioOrder
      (log_inverse_complement_bound R (2 ^ n) rLarge (Nat.pow_pos (by decide)) (by dsimp [R]; rw [Nat.pow_succ]; omega))
    have rationalError : ExactLog.divideNat (ExactLog.log (PositiveRatio.ofNat 2 (by decide))) (2 ^ n) (Nat.pow_pos (by decide)) =
        ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩ := by
      apply ExactLog.ext
      · rfl
      · exact Nat.one_mul _
    rw [rationalError] at ratioError
    exact ⟨ExactLog.le_trans increments.1 ((ExactLog.add_le_add_left_iff _ _ (entropyTerm q)).mpr firstError),
      ExactLog.le_trans increments.2 ((ExactLog.add_le_add_left_iff _ _ (entropyTerm p)).mpr ratioError)⟩
  · have bSmall : b * T ≤ den := Nat.le_of_lt (Nat.lt_of_not_ge large)
    have gapSmall : (a - b) * T ≤ den := by
      have monotone : T ≤ E := by rw [← factors]; exact Nat.le_mul_of_pos_right _ rPositive
      exact Nat.le_trans (Nat.mul_le_mul_left (a - b) monotone) close
    have aSmall : a * S ≤ den := by
      have sum := Nat.add_le_add bSmall gapSmall
      have combined : a * T ≤ 2 * den := by simpa only [← Nat.add_mul, Nat.add_comm b, recovered, Nat.two_mul] using sum
      rw [twice] at combined
      have cancel : 2 * (a * S) ≤ 2 * den := by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using combined
      exact Nat.le_of_mul_le_mul_left cancel (by decide)
    have bSmallS : b * S ≤ den := Nat.le_trans (Nat.mul_le_mul_right S ordered) aSmall
    exact small_pair ⟨a, den, denPositive⟩ ⟨b, den, denPositive⟩ aBound bBound n
      (by simpa only [QProb.LE, Nat.one_mul] using aSmall)
      (by simpa only [QProb.LE, Nat.one_mul] using bSmallS)

/-- Full two-point modulus for arbitrary unreduced rational probabilities.
The hypotheses express absolute closeness without signed probability weights. -/
theorem entropyTerm_continuity (p q : QProb) (pBound : p.num ≤ p.den) (qBound : q.num ≤ q.den) (n : Nat)
    (leftClose : QProb.LE p (QProb.add q ⟨1, 2 ^ (3 * n + 6), Nat.pow_pos (by decide)⟩))
    (rightClose : QProb.LE q (QProb.add p ⟨1, 2 ^ (3 * n + 6), Nat.pow_pos (by decide)⟩)) :
    EntropyWithin p q (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩) := by
  have gap (x y : QProb)
      (close : QProb.LE x (QProb.add y ⟨1, 2 ^ (3 * n + 6), Nat.pow_pos (by decide)⟩)) :
      (x.num * y.den - y.num * x.den) * 2 ^ (3 * n + 6) ≤ x.den * y.den := by
    have cleared : (x.num * y.den) * 2 ^ (3 * n + 6) ≤
        (y.num * x.den) * 2 ^ (3 * n + 6) + x.den * y.den := by
      simpa only [QProb.LE, QProb.add, Nat.one_mul, Nat.mul_one, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using close
    rw [Nat.sub_mul]
    omega
  let den := p.den * q.den
  have denPositive : 0 < den := Nat.mul_pos p.den_pos q.den_pos
  have firstBound : p.num * q.den ≤ den := Nat.mul_le_mul_right q.den pBound
  have secondBound : q.num * p.den ≤ den := by
    simpa only [den, Nat.mul_comm p.den q.den] using Nat.mul_le_mul_right p.den qBound
  have comparison : EntropyWithin ⟨p.num * q.den, den, denPositive⟩ ⟨q.num * p.den, den, denPositive⟩
      (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩) := by
    rcases Nat.le_total (q.num * p.den) (p.num * q.den) with forward | backward
    · exact entropyTerm_continuity_same_den den _ _ n denPositive firstBound secondBound forward (gap p q leftClose)
    · have swapped := entropyTerm_continuity_same_den den _ _ n denPositive secondBound firstBound backward
        (by simpa only [den, Nat.mul_comm q.den p.den] using gap q p rightClose)
      exact ⟨swapped.2, swapped.1⟩
  have firstSame : QProb.Equiv (⟨p.num * q.den, den, denPositive⟩ : QProb) p := by
    change (p.num * q.den) * p.den = p.num * (p.den * q.den)
    ac_rfl
  have secondSame : QProb.Equiv (⟨q.num * p.den, den, denPositive⟩ : QProb) q := by
    change (q.num * p.den) * q.den = q.num * (p.den * q.den)
    ac_rfl
  exact ⟨(ExactLog.le_congr (entropyTerm_congr firstSame)
      (ExactLog.add_congr (entropyTerm_congr secondSame) (ExactLog.equiv_refl _))).mp comparison.1,
    (ExactLog.le_congr (entropyTerm_congr secondSame)
      (ExactLog.add_congr (entropyTerm_congr firstSame) (ExactLog.equiv_refl _))).mp comparison.2⟩

/-- An explicit positive rational two-point continuity modulus for every
requested positive rational error. It imposes no denominator cap on inputs. -/
def entropyContinuityThreshold (tolerance : QProb) : QProb :=
  ⟨1, 2 ^ (3 * (tolerance.den.log2 + 1) + 6), Nat.pow_pos (by decide)⟩

theorem entropyTerm_uniform_continuity (tolerance : QProb) (positive : 0 < tolerance.num)
    (p q : QProb) (pBound : p.num ≤ p.den) (qBound : q.num ≤ q.den)
    (leftClose : QProb.LE p (QProb.add q (entropyContinuityThreshold tolerance)))
    (rightClose : QProb.LE q (QProb.add p (entropyContinuityThreshold tolerance))) :
    EntropyWithin p q (ExactLog.ofSignedRatio tolerance.toSignedRatio) := by
  have comparison := entropyTerm_continuity p q pBound qBound (tolerance.den.log2 + 1) leftClose rightClose
  have errorBound : ExactLog.LE (ExactLog.ofSignedRatio ⟨1, 2 ^ (tolerance.den.log2 + 1), Nat.pow_pos (by decide)⟩)
      (ExactLog.ofSignedRatio tolerance.toSignedRatio) := by
    apply (ExactLog.ofSignedRatio_le_iff _ _).mpr
    have power : tolerance.den ≤ 2 ^ (tolerance.den.log2 + 1) := Nat.le_of_lt Nat.lt_log2_self
    have scaled : 2 ^ (tolerance.den.log2 + 1) ≤ tolerance.num * 2 ^ (tolerance.den.log2 + 1) :=
      Nat.le_mul_of_pos_left _ positive
    simpa only [QProb.toSignedRatio, Int.one_mul, ← Int.natCast_mul, Int.ofNat_le] using Nat.le_trans power scaled
  exact ⟨ExactLog.le_trans comparison.1 ((ExactLog.add_le_add_left_iff _ _ (entropyTerm q)).mpr errorBound),
    ExactLog.le_trans comparison.2 ((ExactLog.add_le_add_left_iff _ _ (entropyTerm p)).mpr errorBound)⟩

end Thesis.Probability
