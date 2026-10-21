import Thesis.Probability.EntropySmallMass
import Thesis.Probability.ExactLogRational

namespace Thesis.Probability
open Distros

private def binaryGrid : EntropyGrid Bool := ⟨[false, true], by decide⟩
private def remainingMass (p : QProb) : QProb := ⟨p.den - p.num, p.den, p.den_pos⟩
private def binaryLaw (p : QProb) (bounded : p.num ≤ p.den) : Distro Bool :=
  ⟨⟨[(false, p.num), (true, p.den - p.num)], p.den, p.den_pos, by
    change p.num + (p.den - p.num + 0) = p.den
    omega⟩⟩
private theorem binary_false (p : QProb) (bounded : p.num ≤ p.den) : (binaryLaw p bounded).pmf false = p := by
  cases p
  simp [binaryLaw, Distro.pmf, FiniteProbRecord.probVal, FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
private theorem binary_true (p : QProb) (bounded : p.num ≤ p.den) : (binaryLaw p bounded).pmf true = remainingMass p := by
  simp [binaryLaw, remainingMass, Distro.pmf, FiniteProbRecord.probVal, FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
private theorem binary_support (p : QProb) (bounded : p.num ≤ p.den) :
    (binaryLaw p bounded).AlmostSurely (fun value => value ∈ binaryGrid.cells) := by
  intro atom _ _
  cases atom.1 <;> decide

/-- A scalar entropy contribution is bounded by a two-state cross entropy.
The observed mass can be zero or one; only the auxiliary reference is interior. -/
theorem entropyTerm_le_reference (p : QProb) (bounded : p.num ≤ p.den) (r : QProb)
    (positive : 0 < r.num) (interior : r.num < r.den) :
    ExactLog.LE (entropyTerm p)
      (ExactLog.add (ExactLog.scaleRatio p (ExactLog.log ⟨r.den, r.num, r.den_pos, positive⟩))
        (ExactLog.scaleRatio (remainingMass p) (ExactLog.log ⟨r.den, r.den - r.num, r.den_pos, Nat.sub_pos_of_lt interior⟩))) := by
  have referencePositive : (binaryLaw r (Nat.le_of_lt interior)).GridPositive binaryGrid := by
    intro value _
    cases value
    · rw [binary_false]; exact positive
    · rw [binary_true]; exact Nat.sub_pos_of_lt interior
  have variational := (binaryLaw p bounded).entropy_le_crossEntropy (binaryLaw r (Nat.le_of_lt interior)) binaryGrid
    (binary_support p bounded) (binary_support r (Nat.le_of_lt interior)) referencePositive
  have entropy : (binaryLaw p bounded).entropy binaryGrid (binary_support p bounded) =
      ExactLog.add (entropyTerm p) (entropyTerm (remainingMass p)) := by
    simp only [Distro.entropy, binaryGrid, List.map_cons, List.map_nil, ExactLog.listSum,
      ExactLog.add_zero, binary_false, binary_true]
  have cross : (binaryLaw p bounded).crossEntropy (binaryLaw r (Nat.le_of_lt interior)) binaryGrid
      (binary_support p bounded) (binary_support r (Nat.le_of_lt interior)) referencePositive =
      ExactLog.add (ExactLog.scaleRatio p (ExactLog.log ⟨r.den, r.num, r.den_pos, positive⟩))
        (ExactLog.scaleRatio (remainingMass p) (ExactLog.log ⟨r.den, r.den - r.num, r.den_pos, Nat.sub_pos_of_lt interior⟩)) := by
    simp only [Distro.crossEntropy, binaryGrid, List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
      ExactLog.listSum, ExactLog.add_zero, crossEntropyTerm, binary_false, binary_true]
    rfl
  rw [entropy, cross] at variational
  have rest := entropyTerm_nonnegative (remainingMass p) (by
    change (p.den - p.num) * 1 ≤ 1 * p.den
    simpa only [Nat.mul_one, Nat.one_mul] using Nat.sub_le p.den p.num)
  have lower := (ExactLog.add_le_add_left_iff ExactLog.zero (entropyTerm (remainingMass p)) (entropyTerm p)).mpr rest
  rw [ExactLog.add_zero] at lower
  exact ExactLog.le_trans lower variational

/-- For an observed mass at most `1/den`, a fully algebraic upper bound
valid at zero. The remaining logarithm is bounded by the finite Bernoulli
estimate, supplying the boundary ingredient for uniform continuity. -/
theorem entropyTerm_le_small_mass (p : QProb) (bounded : p.num ≤ p.den) (den : Nat) (large : 1 < den)
    (small : QProb.LE p ⟨1, den, Nat.lt_trans Nat.zero_lt_one large⟩) :
    ExactLog.LE (entropyTerm p)
      (ExactLog.add (ExactLog.scaleRatio ⟨1, den, Nat.lt_trans Nat.zero_lt_one large⟩
        (ExactLog.log (PositiveRatio.ofNat den (Nat.lt_trans Nat.zero_lt_one large))))
        (ExactLog.log ⟨den, den - 1, Nat.lt_trans Nat.zero_lt_one large, Nat.sub_pos_of_lt large⟩)) := by
  have bound := entropyTerm_le_reference p bounded ⟨1, den, Nat.lt_trans Nat.zero_lt_one large⟩ Nat.zero_lt_one large
  have firstNonnegative : ExactLog.LE ExactLog.zero (ExactLog.log (PositiveRatio.ofNat den (Nat.lt_trans Nat.zero_lt_one large))) := by
    apply (ExactLog.log_le_log_iff PositiveRatio.one _).mpr
    change 1 * 1 ≤ den * 1
    omega
  have secondNonnegative : ExactLog.LE ExactLog.zero
      (ExactLog.log ⟨den, den - 1, Nat.lt_trans Nat.zero_lt_one large, Nat.sub_pos_of_lt large⟩) := by
    apply (ExactLog.log_le_log_iff PositiveRatio.one _).mpr
    change 1 * (den - 1) ≤ den * 1
    omega
  have first := ExactLog.scaleRatio_weight_mono small _ firstNonnegative
  have second := ExactLog.scaleRatio_weight_mono (p := remainingMass p) (q := QProb.one) (by
    change (p.den - p.num) * 1 ≤ 1 * p.den
    simpa only [Nat.mul_one, Nat.one_mul] using Nat.sub_le p.den p.num) _ secondNonnegative
  rw [ExactLog.scaleRatio_one] at second
  exact ExactLog.le_trans bound (ExactLog.add_le_add first second)

/-- Explicit dyadic boundary estimate: if `p ≤ 2^(-(k+1))`, then
`-p log₂ p ≤ (k+3)/2^(k+1)`, including `p = 0`. -/
theorem entropyTerm_dyadic_bound (p : QProb) (bounded : p.num ≤ p.den) (k : Nat)
    (small : QProb.LE p ⟨1, 2 ^ (k + 1), Nat.pow_pos (by decide)⟩) :
    ExactLog.LE (entropyTerm p) (ExactLog.ofSignedRatio ⟨((k + 3 : Nat) : Int), 2 ^ (k + 1), Nat.pow_pos (by decide)⟩) := by
  have large : 1 < 2 ^ (k + 1) := by
    have positive : 0 < 2 ^ k := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega
  have first := entropyTerm_le_small_mass p bounded (2 ^ (k + 1)) large small
  have complementBound := log_inverse_complement_bound (2 ^ (k + 1)) (2 ^ k) large (Nat.pow_pos (by decide))
    (by rw [Nat.pow_succ]; omega)
  have lifted := (ExactLog.add_le_add_left_iff _ _
    (ExactLog.scaleRatio ⟨1, 2 ^ (k + 1), Nat.pow_pos (by decide)⟩
      (ExactLog.log (PositiveRatio.ofNat (2 ^ (k + 1)) (Nat.pow_pos (by decide)))))).mpr complementBound
  have presentation : ExactLog.add
      (ExactLog.scaleRatio ⟨1, 2 ^ (k + 1), Nat.pow_pos (by decide)⟩
        (ExactLog.log (PositiveRatio.ofNat (2 ^ (k + 1)) (Nat.pow_pos (by decide)))))
      (ExactLog.divideNat (ExactLog.log (PositiveRatio.ofNat 2 (by decide))) (2 ^ k) (Nat.pow_pos (by decide))) =
      ExactLog.rescale (ExactLog.ofSignedRatio ⟨((k + 3 : Nat) : Int), 2 ^ (k + 1), Nat.pow_pos (by decide)⟩)
        (2 ^ k) (Nat.pow_pos (by decide)) := by
    apply ExactLog.ext
    · apply PositiveRatio.ext <;>
        simp only [ExactLog.add, ExactLog.scaleRatio, ExactLog.log, ExactLog.divideNat, ExactLog.rescale,
          ExactLog.ofSignedRatio, PositiveRatio.ofNat, PositiveRatio.pow, PositiveRatio.mul,
          Int.toNat_natCast, Int.toNat_neg_natCast, Nat.pow_zero, Nat.one_pow, Nat.one_mul, Nat.mul_one,
          Nat.pow_one, ← Nat.pow_mul, ← Nat.pow_add]
      congr 1
      rw [Nat.pow_succ]
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [ExactLog.add, ExactLog.scaleRatio, ExactLog.log, ExactLog.divideNat, ExactLog.rescale,
        ExactLog.ofSignedRatio, Nat.one_mul]
  rw [presentation] at lifted
  exact (ExactLog.le_congr (ExactLog.equiv_refl _) (ExactLog.rescale_equiv _ _ _)).mp (ExactLog.le_trans first lifted)

private theorem boundary_coefficient (n : Nat) : 2 * n + 6 ≤ 2 ^ (n + 4) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have scaled := Nat.mul_le_mul_left 2 ih
      have next : 2 ^ (n + 1 + 4) = 2 * 2 ^ (n + 4) := by
        rw [show n + 1 + 4 = n + 4 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      rw [next]
      omega

/-- A power-of-two precision parameter gives a uniform scalar bound at
zero, without a positive lower bound on the observed probability. -/
theorem entropyTerm_boundary_precision (p : QProb) (bounded : p.num ≤ p.den) (n : Nat)
    (small : QProb.LE p ⟨1, 2 ^ (2 * n + 4), Nat.pow_pos (by decide)⟩) :
    ExactLog.LE (entropyTerm p) (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩) := by
  have initial := entropyTerm_dyadic_bound p bounded (2 * n + 3) small
  have rational : ExactLog.LE (ExactLog.ofSignedRatio ⟨((2 * n + 3 + 3 : Nat) : Int), 2 ^ (2 * n + 3 + 1), Nat.pow_pos (by decide)⟩)
      (ExactLog.ofSignedRatio ⟨1, 2 ^ n, Nat.pow_pos (by decide)⟩) := by
    apply (ExactLog.ofSignedRatio_le_iff _ _).mpr
    have scaled := Nat.mul_le_mul_right (2 ^ n) (boundary_coefficient n)
    have exponents : 2 ^ (n + 4) * 2 ^ n = 2 ^ (2 * n + 4) := by rw [← Nat.pow_add]; congr 1; omega
    rw [exponents] at scaled
    simpa only [Int.one_mul, ← Int.natCast_mul, Int.ofNat_le, show 2 * n + 3 + 3 = 2 * n + 6 by omega,
      show 2 * n + 3 + 1 = 2 * n + 4 by omega] using scaled
  exact ExactLog.le_trans initial rational

/-- An explicit rational threshold for any requested positive entropy error.
This is the boundary part of the later two-point continuity modulus. -/
def entropyBoundaryThreshold (tolerance : QProb) : QProb :=
  ⟨1, 2 ^ (2 * (tolerance.den.log2 + 1) + 4), Nat.pow_pos (by decide)⟩

theorem entropyTerm_near_zero (tolerance : QProb) (positive : 0 < tolerance.num)
    (p : QProb) (bounded : p.num ≤ p.den) (small : QProb.LE p (entropyBoundaryThreshold tolerance)) :
    ExactLog.LE (entropyTerm p) (ExactLog.ofSignedRatio tolerance.toSignedRatio) := by
  have initial := entropyTerm_boundary_precision p bounded (tolerance.den.log2 + 1) small
  have rational : ExactLog.LE (ExactLog.ofSignedRatio ⟨1, 2 ^ (tolerance.den.log2 + 1), Nat.pow_pos (by decide)⟩)
      (ExactLog.ofSignedRatio tolerance.toSignedRatio) := by
    apply (ExactLog.ofSignedRatio_le_iff _ _).mpr
    have power : tolerance.den ≤ 2 ^ (tolerance.den.log2 + 1) := Nat.le_of_lt Nat.lt_log2_self
    have scaled : 2 ^ (tolerance.den.log2 + 1) ≤ tolerance.num * 2 ^ (tolerance.den.log2 + 1) :=
      Nat.le_mul_of_pos_left _ positive
    have compared := Nat.le_trans power scaled
    simpa only [QProb.toSignedRatio, Int.one_mul, ← Int.natCast_mul, Int.ofNat_le] using compared
  exact ExactLog.le_trans initial rational

end Thesis.Probability
