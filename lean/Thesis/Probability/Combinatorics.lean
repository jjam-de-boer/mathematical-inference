import Std
import Thesis.Probability.Core

namespace Thesis
namespace Probability
namespace Combinatorics

/-!
Finite natural-number combinatorics for constructive distros.

This module supplies the Nat-level identities used to present named
probability distros as `FiniteProbRecord` values.  Binomial coefficients are
defined by Pascal's recurrence, so every value is produced by addition rather
than by a division of factorials.  The binomial theorem, Vandermonde
convolution, geometric sums, and weighted Cauchy--Schwarz are proved by
induction on `Nat`.  There are no generating-function limits, no real
analysis, and no appeals to choice or excluded middle on undecidable
propositions.
-/

/-- Recursive finite sum `f 0 + ... + f (n-1)`. -/
def natSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => natSum n f + f n

@[simp] theorem natSum_zero (f : Nat → Nat) :
    natSum 0 f = 0 :=
  rfl

theorem natSum_succ (n : Nat) (f : Nat → Nat) :
    natSum (n + 1) f = natSum n f + f n :=
  rfl

/-- Peel the first summand from a nonempty finite sum. -/
theorem natSum_head (n : Nat) (f : Nat → Nat) :
    natSum (n + 1) f = f 0 + natSum n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [natSum]
  | succ n ih =>
      rw [natSum_succ, ih, natSum_succ]
      ac_rfl

/-- Peel both endpoints from a sum of length at least two. -/
theorem natSum_head_last (n : Nat) (f : Nat → Nat) :
    natSum (n + 2) f =
      f 0 + natSum n (fun i => f (i + 1)) + f (n + 1) := by
  rw [natSum_succ, natSum_head, Nat.add_assoc]

theorem natSum_congr {n : Nat} {f g : Nat → Nat}
    (h : forall i, i < n → f i = g i) :
    natSum n f = natSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [natSum_succ, natSum_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        h n (Nat.lt_succ_self n)]

theorem natSum_add (n : Nat) (f g : Nat → Nat) :
    natSum n (fun i => f i + g i) = natSum n f + natSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [natSum, ih, Nat.add_assoc, Nat.add_left_comm]

theorem natSum_mul_left (n c : Nat) (f : Nat → Nat) :
    natSum n (fun i => c * f i) = c * natSum n f := by
  induction n with
  | zero => simp [natSum]
  | succ n ih =>
      simp [natSum, ih, Nat.mul_add]

theorem natSum_zero_fun (n : Nat) :
    natSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natSum, ih]

/-- A finite sum is positive as soon as any one summand is. -/
theorem natSum_pos_of_term {n : Nat} {f : Nat → Nat} {i : Nat}
    (hi : i < n) (hpos : 0 < f i) :
    0 < natSum n f := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
      rw [natSum_succ]
      by_cases hlt : i < n
      · exact Nat.lt_of_lt_of_le (ih hlt) (Nat.le_add_right _ _)
      · have heq : i = n := Nat.eq_of_lt_succ_of_not_lt hi hlt
        rw [heq] at hpos
        exact Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)

/-- Pascal-recurrence binomial coefficient.  `binom n 0 = 1` and
`binom 0 (k + 1) = 0`, with the successor clause the usual addition of the
two smaller coefficients. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

@[simp] theorem binom_zero_right (n : Nat) :
    binom n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem binom_zero_succ (k : Nat) :
    binom 0 (k + 1) = 0 :=
  rfl

theorem binom_succ_succ (n k : Nat) :
    binom (n + 1) (k + 1) = binom n k + binom n (k + 1) :=
  rfl

theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) :
    binom n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => exact False.elim (Nat.lt_irrefl 0 h)
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => exact False.elim ((Nat.not_lt_zero _) (Nat.lt_of_succ_lt h))
      | succ k =>
          have hk : n < k := Nat.succ_lt_succ_iff.mp h
          have hk' : n < k + 1 := Nat.lt_succ_of_lt hk
          simp [binom_succ_succ, ih hk, ih hk']

theorem binom_self (n : Nat) :
    binom n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [binom_succ_succ, ih, binom_eq_zero_of_lt (Nat.lt_succ_self n)]

/-- There is a unique way to choose one element from `n`, so `C(n, 1) = n`. -/
theorem binom_one (n : Nat) :
    binom n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [binom_succ_succ, binom_zero_right, ih]
      exact Nat.add_comm 1 n

/-- The Pascal absorption identity `(k + 1) C(n + 1, k + 1) = (n + 1) C(n, k)`.
This is the Nat form of `k C(n, k) = n C(n - 1, k - 1)`, indexed to avoid
subtracting from zero. -/
theorem binom_succ_mul (n k : Nat) :
    (k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => simp [binom_one]
      | succ k =>
          have hlt : 1 < k + 2 := Nat.succ_lt_succ (Nat.succ_pos k)
          simp [binom_eq_zero_of_lt hlt]
  | succ n ih =>
      rw [binom_succ_succ, Nat.mul_add]
      cases k with
      | zero =>
          simp [binom_zero_right, binom_one]
          omega
      | succ k =>
          have htail := ih (k + 1)
          have hhead := ih k
          rw [htail]
          have hexpand :
              (k + 2) * binom (n + 1) (k + 1) =
                (n + 1) * binom n k + binom (n + 1) (k + 1) := by
            have hsplit :
                (k + 2) * binom (n + 1) (k + 1) =
                  (k + 1) * binom (n + 1) (k + 1) +
                    binom (n + 1) (k + 1) :=
              Nat.succ_mul (k + 1) _
            rw [hsplit, hhead]
          rw [hexpand]
          have hpascal :
              binom (n + 1) (k + 1) = binom n k + binom n (k + 1) :=
            binom_succ_succ n k
          rw [hpascal]
          simp [Nat.succ_mul, Nat.mul_add]
          ac_rfl

/-- The usual binomial term `C(n, k) a^k b^{n-k}`. -/
def binomTerm (n a b k : Nat) : Nat :=
  binom n k * a ^ k * b ^ (n - k)

theorem binomTerm_zero (n a b : Nat) :
    binomTerm n a b 0 = b ^ n := by
  simp [binomTerm]

theorem binomTerm_self (n a b : Nat) :
    binomTerm n a b n = a ^ n := by
  simp [binomTerm, binom_self]

/-- The zero-success successor term factors out one more `b`. -/
theorem binomTerm_succ_zero (n a b : Nat) :
    binomTerm (n + 1) a b 0 = b * binomTerm n a b 0 := by
  simp [binomTerm, Nat.pow_succ, Nat.mul_comm b]

/-- Pascal's recurrence at the level of binomial terms: a success-or-failure
split of `n + 1` trials. -/
theorem binomTerm_succ_succ (n a b k : Nat) :
    binomTerm (n + 1) a b (k + 1) =
      a * binomTerm n a b k + b * binomTerm n a b (k + 1) := by
  have hsub : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ n k
  simp only [binomTerm, binom_succ_succ, hsub]
  rw [Nat.add_mul, Nat.add_mul]
  have hleft :
      binom n k * a ^ (k + 1) * b ^ (n - k) =
        a * (binom n k * a ^ k * b ^ (n - k)) := by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
  have hright :
      binom n (k + 1) * a ^ (k + 1) * b ^ (n - k) =
        b * (binom n (k + 1) * a ^ (k + 1) * b ^ (n - (k + 1))) := by
    by_cases hle : k + 1 ≤ n
    · have hpow : n - k = n - (k + 1) + 1 := by omega
      calc
        binom n (k + 1) * a ^ (k + 1) * b ^ (n - k)
            = binom n (k + 1) * a ^ (k + 1) * b ^ (n - (k + 1) + 1) := by
              rw [hpow]
        _ = binom n (k + 1) * a ^ (k + 1) *
              (b ^ (n - (k + 1)) * b) := by
              rw [Nat.pow_succ b (n - (k + 1))]
        _ = b * (binom n (k + 1) * a ^ (k + 1) *
              b ^ (n - (k + 1))) := by
              ac_rfl
    · have hz : binom n (k + 1) = 0 :=
        binom_eq_zero_of_lt (Nat.not_le.mp hle)
      simp [hz]
  rw [hleft, hright]

theorem pow_two (n : Nat) :
    n ^ 2 = n * n := by
  simp [Nat.pow_succ, Nat.pow_zero]

/-- Scaling the binomial expansion by `a` shifts the power of `a` up by one. -/
theorem binomTerm_mul_left (n a b : Nat) :
    a * natSum (n + 1) (fun k => binomTerm n a b k) =
      natSum (n + 1) (fun k => binom n k * a ^ (k + 1) * b ^ (n - k)) := by
  rw [← natSum_mul_left]
  apply natSum_congr
  intro k _
  simp [binomTerm, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]

/-- Scaling the binomial expansion by `b` shifts the remaining power of `b`. -/
theorem binomTerm_mul_right (n a b : Nat) :
    b * natSum (n + 1) (fun k => binomTerm n a b k) =
      natSum (n + 1) (fun k => binom n k * a ^ k * b ^ (n + 1 - k)) := by
  rw [← natSum_mul_left]
  apply natSum_congr
  intro k hk
  have hle : k ≤ n := Nat.lt_succ_iff.mp hk
  have hsub : n + 1 - k = n - k + 1 := Nat.succ_sub hle
  simp [binomTerm, hsub, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm b]

/-- Interior Pascal expansion of the successor binomial terms. -/
theorem binomTerm_succ_interior (n a b : Nat) :
    natSum n (fun t => binomTerm (n + 1) a b (t + 1)) =
      natSum n (fun t =>
        binom n t * a ^ (t + 1) * b ^ (n - t)) +
      natSum n (fun t =>
        binom n (t + 1) * a ^ (t + 1) * b ^ (n - t)) := by
  rw [← natSum_add]
  apply natSum_congr
  intro t _
  have hsub : n + 1 - (t + 1) = n - t := Nat.succ_sub_succ n t
  simp [binomTerm, binom_succ_succ, hsub, Nat.add_mul, Nat.mul_assoc]

/-- The `a`-scaled expansion contributes the top power and the unshifted interior. -/
theorem binom_left_split (n a b : Nat) :
    natSum (n + 1) (fun k => binom n k * a ^ (k + 1) * b ^ (n - k)) =
      natSum n (fun t => binom n t * a ^ (t + 1) * b ^ (n - t)) +
        a ^ (n + 1) := by
  rw [natSum_succ]
  simp [binom_self, Nat.sub_self, Nat.pow_succ]

/-- The `b`-scaled expansion contributes the bottom power and the shifted interior. -/
theorem binom_right_split (n a b : Nat) :
    natSum (n + 1) (fun k => binom n k * a ^ k * b ^ (n + 1 - k)) =
      b ^ (n + 1) +
        natSum n (fun t =>
          binom n (t + 1) * a ^ (t + 1) * b ^ (n - t)) := by
  rw [natSum_head]
  have hb0 : binom n 0 * a ^ 0 * b ^ (n + 1 - 0) = b ^ (n + 1) := by
    simp
  have htail :
      natSum n (fun i =>
        binom n (i + 1) * a ^ (i + 1) * b ^ (n + 1 - (i + 1))) =
        natSum n (fun t =>
          binom n (t + 1) * a ^ (t + 1) * b ^ (n - t)) := by
    apply natSum_congr
    intro t _
    simp [Nat.succ_sub_succ]
  rw [hb0, htail]

/--
The binomial theorem as a finite Nat identity.  Summing `C(n, k) a^k b^{n-k}`
from `k = 0` to `k = n` recovers `(a + b)^n`.  Distro normalisers for the
binomial family are instances of this identity.
-/
theorem binomial_theorem (n a b : Nat) :
    natSum (n + 1) (fun k => binomTerm n a b k) = (a + b) ^ n := by
  induction n with
  | zero =>
      simp [natSum, binomTerm]
  | succ n ih =>
      have hfactor :
          (a + b) ^ (n + 1) =
            a * natSum (n + 1) (fun k => binomTerm n a b k) +
              b * natSum (n + 1) (fun k => binomTerm n a b k) := by
        rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm _ a, Nat.mul_comm _ b, ih]
      have htarget :
          natSum (n + 2) (fun k => binomTerm (n + 1) a b k) =
            b ^ (n + 1) +
              natSum n (fun t => binomTerm (n + 1) a b (t + 1)) +
              a ^ (n + 1) := by
        rw [natSum_head_last, binomTerm_zero, binomTerm_self]
      rw [htarget, binomTerm_succ_interior, hfactor, binomTerm_mul_left,
        binomTerm_mul_right, binom_left_split, binom_right_split]
      ac_rfl

/-- Vandermonde convolution of binomial coefficients. -/
theorem vandermonde (left right k : Nat) :
    natSum (k + 1) (fun i => binom left i * binom right (k - i)) =
      binom (left + right) k := by
  induction left generalizing k with
  | zero =>
      rw [natSum_head]
      simp [natSum_zero_fun]
  | succ left ih =>
      cases k with
      | zero =>
          simp [natSum]
      | succ k =>
          have hdecomp :
              natSum (k + 2) (fun i =>
                binom (left + 1) i * binom right (k + 1 - i)) =
                (binom right (k + 1) +
                  natSum (k + 1) (fun i =>
                    binom left (i + 1) * binom right (k - i))) +
                  natSum (k + 1) (fun i =>
                    binom left i * binom right (k - i)) := by
            rw [natSum_head]
            have h0 :
                binom (left + 1) 0 * binom right (k + 1 - 0) =
                  binom right (k + 1) := by
              simp
            have htail :
                natSum (k + 1) (fun i =>
                  binom (left + 1) (i + 1) * binom right (k + 1 - (i + 1))) =
                  natSum (k + 1) (fun i =>
                    binom left (i + 1) * binom right (k - i)) +
                  natSum (k + 1) (fun i =>
                    binom left i * binom right (k - i)) := by
              rw [← natSum_add]
              apply natSum_congr
              intro i _
              simp [binom_succ_succ, Nat.succ_sub_succ, Nat.add_mul]
              ac_rfl
            rw [h0, htail]
            ac_rfl
          have hfirst :
              binom right (k + 1) +
                natSum (k + 1) (fun i =>
                  binom left (i + 1) * binom right (k - i)) =
                natSum (k + 2) (fun i =>
                  binom left i * binom right (k + 1 - i)) := by
            have htail :
                natSum (k + 1) (fun i =>
                  binom left (i + 1) * binom right (k - i)) =
                  natSum (k + 1) (fun i =>
                    binom left (i + 1) * binom right (k + 1 - (i + 1))) := by
              apply natSum_congr
              intro i _
              simp [Nat.succ_sub_succ]
            calc
              binom right (k + 1) +
                  natSum (k + 1) (fun i =>
                    binom left (i + 1) * binom right (k - i))
                  = binom left 0 * binom right (k + 1 - 0) +
                      natSum (k + 1) (fun i =>
                        binom left (i + 1) *
                          binom right (k + 1 - (i + 1))) := by
                    simp [htail]
              _ = natSum (k + 2) (fun i =>
                    binom left i * binom right (k + 1 - i)) :=
                (natSum_head (k + 1)
                  (fun i => binom left i * binom right (k + 1 - i))).symm
          have hleft := ih (k + 1)
          have hshift := ih k
          have hpascal :
              binom (left + 1 + right) (k + 1) =
                binom (left + right) (k + 1) + binom (left + right) k := by
            have hidx : left + 1 + right = left + right + 1 := by ac_rfl
            rw [hidx, binom_succ_succ, Nat.add_comm]
          rw [hdecomp, hfirst, hleft, hshift]
          exact hpascal.symm

/-- Scaling the success parameter of a binomial term by `s` is the same as
multiplying the term by `s^k`.  This is the Nat generating function of the
binomial family, before it is packaged as a `QProb` PGF. -/
theorem binomTerm_mul_pow (n a b s k : Nat) :
    binomTerm n a b k * s ^ k = binomTerm n (a * s) b k := by
  simp [binomTerm, Nat.mul_pow]
  ac_rfl

/-- Evaluating the binomial generating function at a natural argument `s`
recovers the binomial theorem with success weight `a * s`. -/
theorem binomTerm_generating (n a b s : Nat) :
    natSum (n + 1) (fun k => binomTerm n a b k * s ^ k) = (a * s + b) ^ n := by
  have hcongr :
      natSum (n + 1) (fun k => binomTerm n a b k * s ^ k) =
        natSum (n + 1) (fun k => binomTerm n (a * s) b k) := by
    apply natSum_congr
    intro k _
    exact binomTerm_mul_pow n a b s k
  rw [hcongr, binomial_theorem]

/-- Absorption at the level of binomial terms: the `(k + 1)`-st term of
`n + 1` trials factors as a success times the `k`-th term of `n` trials. -/
theorem binomTerm_succ_mul (n a b k : Nat) :
    (k + 1) * binomTerm (n + 1) a b (k + 1) =
      (n + 1) * a * binomTerm n a b k := by
  have hsub : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ n k
  simp only [binomTerm, hsub]
  have hpow : a ^ (k + 1) = a * a ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hbinom := binom_succ_mul n k
  calc
    (k + 1) * (binom (n + 1) (k + 1) * a ^ (k + 1) * b ^ (n - k))
        = (k + 1) * binom (n + 1) (k + 1) * a ^ (k + 1) * b ^ (n - k) := by
          ac_rfl
    _ = (n + 1) * binom n k * (a * a ^ k) * b ^ (n - k) := by
          rw [hbinom, hpow]
    _ = (n + 1) * a * (binom n k * a ^ k * b ^ (n - k)) := by
          ac_rfl

/-- The first factorial moment of binomial terms: `∑ k C(n,k) a^k b^{n-k} =
n a (a + b)^{n-1}`.  On `Nat`, the `n = 0` case is `0` because the exponent
`n - 1` underflows to `0` and the front factor `n` vanishes. -/
theorem binomTerm_weighted_sum (n a b : Nat) :
    natSum (n + 1) (fun k => k * binomTerm n a b k) =
      n * a * (a + b) ^ (n - 1) := by
  cases n with
  | zero =>
      simp [natSum, binomTerm]
  | succ n =>
      rw [natSum_head]
      have hzero : 0 * binomTerm (n + 1) a b 0 = 0 := Nat.zero_mul _
      have htail :
          natSum (n + 1) (fun i =>
              (i + 1) * binomTerm (n + 1) a b (i + 1)) =
            (n + 1) * a * (a + b) ^ n := by
        have hcongr :
            natSum (n + 1) (fun i =>
                (i + 1) * binomTerm (n + 1) a b (i + 1)) =
              natSum (n + 1) (fun i =>
                (n + 1) * a * binomTerm n a b i) := by
          apply natSum_congr
          intro i _
          exact binomTerm_succ_mul n a b i
        rw [hcongr, natSum_mul_left, binomial_theorem]
      simp [hzero, htail]

/-- Rising factorial `a (a + 1) ... (a + k - 1)`, with `a↑0 = 1`. -/
def risingFactorial (a k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k + 1 => (a + k) * risingFactorial a k

@[simp] theorem risingFactorial_zero (a : Nat) :
    risingFactorial a 0 = 1 :=
  rfl

theorem risingFactorial_succ (a k : Nat) :
    risingFactorial a (k + 1) = (a + k) * risingFactorial a k :=
  rfl

/-- Geometric partial sum `1 + r + ... + r^{n-1}`. -/
def geomSum (r n : Nat) : Nat :=
  natSum n (fun k => r ^ k)

theorem geomSum_succ (r n : Nat) :
    geomSum r (n + 1) = geomSum r n + r ^ n :=
  rfl

/-- Multiplying a geometric sum by `r` and adding the missing unit term
recovers the next partial sum. -/
theorem geomSum_mul_succ (r n : Nat) :
    r * geomSum r n + 1 = geomSum r (n + 1) := by
  induction n with
  | zero => simp [geomSum, natSum]
  | succ n ih =>
      calc
        r * geomSum r (n + 1) + 1
            = r * (geomSum r n + r ^ n) + 1 := by rw [geomSum_succ]
        _ = r * geomSum r n + 1 + r * r ^ n := by
          simp [Nat.mul_add]
          ac_rfl
        _ = geomSum r (n + 1) + r ^ (n + 1) := by
          rw [ih, Nat.pow_succ, Nat.mul_comm r]
        _ = geomSum r (n + 2) := (geomSum_succ r (n + 1)).symm

/-- A nonempty geometric sum is positive, because it always contains the
unit term `r^0 = 1`. -/
theorem geomSum_pos (r n : Nat) (hn : 0 < n) :
    0 < geomSum r n := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
  | succ n =>
      unfold geomSum
      rw [natSum_head]
      simp [Nat.pow_zero]
      exact Nat.add_pos_left (Nat.succ_pos 0) _

/-- Truncated negative-binomial generating sum
`∑_{k < n} C(k + r - 1, k) x^k`.  Callers take `0 < r` so the
`r - 1` shift does not wrap. -/
def nbSum (r x n : Nat) : Nat :=
  natSum n (fun k => binom (k + r - 1) k * x ^ k)

/-- Under `0 < r`, the index `k + r - 1` is `k` plus the predecessor of
`r`, so the generating sum does not rely on wrapping subtraction. -/
theorem nbSum_pred (r x n : Nat) (hr : 0 < r) :
    nbSum r x n =
      natSum n (fun k => binom (k + (r - 1)) k * x ^ k) := by
  apply natSum_congr
  intro k _
  have hshift : k + r - 1 = k + (r - 1) :=
    Nat.add_sub_assoc (Nat.succ_le_of_lt hr) k
  rw [hshift]

theorem nbSum_pos (r x n : Nat) (hr : 0 < r) (hn : 0 < n) :
    0 < nbSum r x n := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
  | succ n =>
      rw [nbSum_pred r x (n + 1) hr]
      rw [natSum_head]
      simp [binom_zero_right, Nat.pow_zero]
      exact Nat.add_pos_left (Nat.succ_pos 0) _

/-- Cauchy product of binomial terms with a common success/failure weight.
Out-of-range indices are zero by `binom_eq_zero_of_lt`. -/
theorem binomTerm_cauchy (n m a b k i : Nat) (hi : i ≤ k) :
    (if i < n + 1 then binomTerm n a b i else 0) *
      (if k - i < m + 1 then binomTerm m a b (k - i) else 0) =
      binom n i * binom m (k - i) * a ^ k * b ^ (n + m - k) := by
  by_cases hin : i < n + 1
  · by_cases hkm : k - i < m + 1
    · have ha : a ^ i * a ^ (k - i) = a ^ k := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hi]
      have hb : b ^ (n - i) * b ^ (m - (k - i)) = b ^ (n + m - k) := by
        have hile : i ≤ n := Nat.le_of_lt_succ hin
        have hkile : k - i ≤ m := Nat.le_of_lt_succ hkm
        rw [← Nat.pow_add]
        have hsum : n - i + (m - (k - i)) = n + m - k := by
          omega
        rw [hsum]
      simp only [hin, hkm, ↓reduceIte, binomTerm]
      calc
        binom n i * a ^ i * b ^ (n - i) *
            (binom m (k - i) * a ^ (k - i) * b ^ (m - (k - i)))
            =
          binom n i * binom m (k - i) *
            (a ^ i * a ^ (k - i)) *
            (b ^ (n - i) * b ^ (m - (k - i))) := by
          ac_rfl
        _ = binom n i * binom m (k - i) * a ^ k * b ^ (n + m - k) := by
          rw [ha, hb]
    · have hm : m < k - i :=
        Nat.lt_of_succ_le (Nat.not_lt.mp hkm)
      simp [hin, hkm, binom_eq_zero_of_lt hm]
  · have hn : n < i := Nat.lt_of_succ_le (Nat.not_lt.mp hin)
    simp [hin, binom_eq_zero_of_lt hn]

/-- Convolution of binomial terms is the binomial term of the summed trial
count, which is Vandermonde after factoring out the common powers. -/
theorem binomTerm_convolution (n m a b k : Nat) :
    natSum (k + 1) (fun i =>
      (if i < n + 1 then binomTerm n a b i else 0) *
        (if k - i < m + 1 then binomTerm m a b (k - i) else 0)) =
      binomTerm (n + m) a b k := by
  have hcongr :
      natSum (k + 1) (fun i =>
          (if i < n + 1 then binomTerm n a b i else 0) *
            (if k - i < m + 1 then binomTerm m a b (k - i) else 0)) =
        natSum (k + 1) (fun i =>
          binom n i * binom m (k - i) * a ^ k * b ^ (n + m - k)) := by
    apply natSum_congr
    intro i hi
    exact binomTerm_cauchy n m a b k i (Nat.le_of_lt_succ hi)
  rw [hcongr]
  have hfactor :
      natSum (k + 1) (fun i =>
          binom n i * binom m (k - i) * a ^ k * b ^ (n + m - k)) =
        a ^ k * b ^ (n + m - k) *
          natSum (k + 1) (fun i => binom n i * binom m (k - i)) := by
    have hswap :
        natSum (k + 1) (fun i =>
            binom n i * binom m (k - i) * a ^ k * b ^ (n + m - k)) =
          natSum (k + 1) (fun i =>
            a ^ k * b ^ (n + m - k) * (binom n i * binom m (k - i))) := by
      apply natSum_congr
      intro i _
      ac_rfl
    rw [hswap, natSum_mul_left]
  rw [hfactor, vandermonde]
  simp [binomTerm]
  ac_rfl

/-- Occupancy lists of length `categories` summing to `trials`. -/
def compositions : Nat → Nat → List (List Nat)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | categories + 1, trials =>
      (List.range (trials + 1)).flatMap fun used =>
        (compositions categories (trials - used)).map (fun rest => used :: rest)

/-- Multinomial coefficient built from successive binomial coefficients. -/
def multiCoeff : List Nat → Nat
  | [] => 1
  | used :: rest => binom (used + rest.sum) used * multiCoeff rest

/-- `2ab ≤ a² + b²` when `a ≤ b`, by completing the square on `b - a`. -/
theorem two_mul_le_sq_add_of_le (a b : Nat) (h : a ≤ b) :
    2 * a * b ≤ a * a + b * b := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  rw [hb]
  have hexpand :
      (a + (b - a)) * (a + (b - a)) =
        a * a + a * (b - a) + (b - a) * a + (b - a) * (b - a) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    ac_rfl
  have hdouble : 2 * a * (b - a) = a * (b - a) + (b - a) * a := by
    rw [Nat.two_mul, Nat.add_mul]
    exact congrArg (HAdd.hAdd (a * (b - a))) (Nat.mul_comm a (b - a))
  have htwo : 2 * a * a = a * a + a * a := by
    rw [Nat.two_mul, Nat.add_mul]
  calc
    2 * a * (a + (b - a))
        = 2 * a * a + 2 * a * (b - a) := by rw [Nat.mul_add]
    _ ≤ 2 * a * a + 2 * a * (b - a) + (b - a) * (b - a) :=
      Nat.le_add_right _ _
    _ = a * a + (a * a + a * (b - a) + (b - a) * a + (b - a) * (b - a)) := by
      rw [htwo, hdouble]
      ac_rfl
    _ = a * a + (a + (b - a)) * (a + (b - a)) := by
      rw [hexpand]

/-- `2ab ≤ a² + b²`, the elementary quadratic inequality on `Nat`. -/
theorem two_mul_le_sq_add (a b : Nat) :
    2 * a * b ≤ a * a + b * b := by
  rcases Nat.le_total a b with h | h
  · exact two_mul_le_sq_add_of_le a b h
  · calc
      2 * a * b = 2 * b * a := by ac_rfl
      _ ≤ b * b + a * a := two_mul_le_sq_add_of_le b a h
      _ = a * a + b * b := Nat.add_comm _ _

/-- Weighted value `∑ wᵢ xᵢ` for pairs `(x, w)`. -/
def weightedSum : List (Nat × Nat) → Nat
  | [] => 0
  | (x, w) :: rest => w * x + weightedSum rest

/-- Weighted square sum `∑ wᵢ xᵢ²`. -/
def weightedSqSum : List (Nat × Nat) → Nat
  | [] => 0
  | (x, w) :: rest => w * x * x + weightedSqSum rest

/-- Total weight `∑ wᵢ`. -/
def weightTotal : List (Nat × Nat) → Nat
  | [] => 0
  | (_, w) :: rest => w + weightTotal rest

/-- Concatenation is additive for the first weighted moment. -/
theorem weightedSum_append (left right : List (Nat × Nat)) :
    weightedSum (left ++ right) = weightedSum left + weightedSum right := by
  induction left with
  | nil => simp [weightedSum]
  | cons item rest ih =>
      rcases item with ⟨x, w⟩
      simp [weightedSum, ih, Nat.add_assoc]

/-- Cross term for the Cauchy inductive step: each existing atom is compared
with a new value `x` by `2xy ≤ x² + y²`. -/
theorem cauchy_cross (x : Nat) (items : List (Nat × Nat)) :
    2 * x * weightedSum items ≤
      weightedSqSum items + weightTotal items * x * x := by
  induction items with
  | nil => simp [weightedSum, weightedSqSum, weightTotal]
  | cons item rest ih =>
      rcases item with ⟨y, v⟩
      have hpair : 2 * x * (v * y) ≤ v * y * y + v * x * x := by
        have hscaled : v * (2 * x * y) ≤ v * (x * x + y * y) :=
          Nat.mul_le_mul_left v (two_mul_le_sq_add x y)
        calc
          2 * x * (v * y) = v * (2 * x * y) := by ac_rfl
          _ ≤ v * (x * x + y * y) := hscaled
          _ = v * x * x + v * y * y := by
            simp [Nat.mul_add, Nat.mul_assoc]
          _ = v * y * y + v * x * x := Nat.add_comm _ _
      calc
        2 * x * (v * y + weightedSum rest)
            = 2 * x * (v * y) + 2 * x * weightedSum rest := by
          simp [Nat.mul_add]
        _ ≤ (v * y * y + v * x * x) +
              (weightedSqSum rest + weightTotal rest * x * x) :=
          Nat.add_le_add hpair ih
        _ = (v * y * y + weightedSqSum rest) +
              (v * x * x + weightTotal rest * x * x) := by ac_rfl
        _ = (v * y * y + weightedSqSum rest) +
              (v + weightTotal rest) * x * x := by
          simp [Nat.add_mul, Nat.mul_assoc]

/--
Weighted Cauchy--Schwarz / Titu form: `(∑ w x)² ≤ (∑ w) (∑ w x²)`.
This is the Nat identity behind nonnegativity of variance for a finite
Nat-valued distro.
-/
theorem cauchy_schwarz_weights (items : List (Nat × Nat)) :
    weightedSum items * weightedSum items ≤
      weightTotal items * weightedSqSum items := by
  induction items with
  | nil => simp [weightedSum, weightTotal, weightedSqSum]
  | cons item rest ih =>
      rcases item with ⟨x, w⟩
      have hcross : 2 * (w * x) * weightedSum rest ≤
          w * weightedSqSum rest + weightTotal rest * (w * x * x) := by
        have hscaled :
            w * (2 * x * weightedSum rest) ≤
              w * (weightedSqSum rest + weightTotal rest * x * x) :=
          Nat.mul_le_mul_left w (cauchy_cross x rest)
        calc
          2 * (w * x) * weightedSum rest
              = w * (2 * x * weightedSum rest) := by ac_rfl
          _ ≤ w * (weightedSqSum rest + weightTotal rest * x * x) := hscaled
          _ = w * weightedSqSum rest + w * (weightTotal rest * x * x) := by
            simp [Nat.mul_add]
          _ = w * weightedSqSum rest + weightTotal rest * (w * x * x) := by
            ac_rfl
      have hexpand :
          (w * x + weightedSum rest) * (w * x + weightedSum rest) =
            w * x * (w * x) + 2 * (w * x) * weightedSum rest +
              weightedSum rest * weightedSum rest := by
        simp [Nat.add_mul, Nat.mul_add, Nat.two_mul, Nat.mul_assoc]
        ac_rfl
      have hright :
          (w + weightTotal rest) * (w * x * x + weightedSqSum rest) =
            w * (w * x * x) + w * weightedSqSum rest +
              weightTotal rest * (w * x * x) +
              weightTotal rest * weightedSqSum rest := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
        ac_rfl
      have hsq : w * x * (w * x) = w * (w * x * x) := by ac_rfl
      calc
        (w * x + weightedSum rest) * (w * x + weightedSum rest)
            = w * x * (w * x) + 2 * (w * x) * weightedSum rest +
                weightedSum rest * weightedSum rest := hexpand
        _ ≤ w * (w * x * x) +
              (w * weightedSqSum rest + weightTotal rest * (w * x * x)) +
              weightTotal rest * weightedSqSum rest :=
          Nat.add_le_add (Nat.add_le_add (Nat.le_of_eq hsq) hcross) ih
        _ = (w + weightTotal rest) * (w * x * x + weightedSqSum rest) := by
          rw [hright]
          ac_rfl

/-- Markov's inequality on weighted Nat atoms: `t` times the selected weight
is at most the weighted value sum. -/
theorem markov_weights (items : List (Nat × Nat)) (t : Nat) :
    t * weightTotal (items.filter (fun pair => decide (t ≤ pair.1))) ≤
      weightedSum items := by
  induction items with
  | nil => simp [weightTotal, weightedSum]
  | cons item rest ih =>
      rcases item with ⟨x, w⟩
      cases hdec : decide (t ≤ x) with
      | false =>
          simp [List.filter, hdec, weightedSum]
          exact Nat.le_trans ih (Nat.le_add_left _ _)
      | true =>
          have hx : t ≤ x := of_decide_eq_true hdec
          simp [List.filter, hdec, weightedSum, weightTotal, Nat.mul_add]
          have hterm : t * w ≤ w * x := by
            rw [Nat.mul_comm t w]
            exact Nat.mul_le_mul_left w hx
          exact Nat.add_le_add hterm ih

/-- Weighted power sum `∑ wᵢ xᵢ^p`. -/
def weightedPowSum (power : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (x, w) :: rest => w * x ^ power + weightedPowSum power rest

theorem weightedPowSum_one (items : List (Nat × Nat)) :
    weightedPowSum 1 items = weightedSum items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rcases item with ⟨x, w⟩
      simp [weightedPowSum, weightedSum, ih]

theorem weightedPowSum_two (items : List (Nat × Nat)) :
    weightedPowSum 2 items = weightedSqSum items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rcases item with ⟨x, w⟩
      simp [weightedPowSum, weightedSqSum, ih, pow_two, Nat.mul_assoc]

/-- Squared distance between two naturals.  The difference is taken in the
order that stays inside `Nat`, so this is the lattice counterpart of
`(x - y)²` without introducing integers. -/
def natSqDiff (left right : Nat) : Nat :=
  let delta := if left ≤ right then right - left else left - right
  delta * delta

theorem natSqDiff_self (n : Nat) :
    natSqDiff n n = 0 := by
  simp [natSqDiff]

theorem natSqDiff_comm (left right : Nat) :
    natSqDiff left right = natSqDiff right left := by
  simp [natSqDiff]
  by_cases hle : left ≤ right
  · by_cases hge : right ≤ left
    · have heq : left = right := Nat.le_antisymm hle hge
      simp [heq]
    · simp [hle, hge]
  · have hge : right ≤ left := Nat.le_of_not_le hle
    simp [hle, hge]

/-- On the centred window `{0, ..., 2r}`, the squared displacement from `r`
cannot exceed `r²`. -/
theorem natSqDiff_window (radius k : Nat) (hk : k < 2 * radius + 1) :
    natSqDiff k radius ≤ radius * radius := by
  have hk' : k ≤ 2 * radius := Nat.le_of_lt_succ hk
  by_cases hle : k ≤ radius
  · have hdelta : radius - k ≤ radius := Nat.sub_le radius k
    simp [natSqDiff, hle]
    exact Nat.mul_le_mul hdelta hdelta
  · have hge : radius ≤ k := Nat.le_of_not_le hle
    have htwo : k ≤ radius + radius := by
      simpa [Nat.two_mul] using hk'
    have hdelta : k - radius ≤ radius :=
      (Nat.sub_le_iff_le_add).mpr htwo
    simp [natSqDiff, hle]
    exact Nat.mul_le_mul hdelta hdelta

/-- Reflecting a window index through the centre does not change the squared
displacement: `(2r - k) - r` and `k - r` have the same absolute value. -/
theorem natSqDiff_reflect (radius k : Nat) (hk : k ≤ 2 * radius) :
    natSqDiff (2 * radius - k) radius = natSqDiff k radius := by
  by_cases hle : k ≤ radius
  · have hrep : 2 * radius - k = radius + (radius - k) := by
      simpa [Nat.two_mul] using Nat.add_sub_assoc hle radius
    rw [hrep]
    unfold natSqDiff
    by_cases hzero : radius + (radius - k) ≤ radius
    · have hz : radius - k = 0 := by omega
      simp [hzero, hle]
      simp [hz]
    · have hdelta :
          radius + (radius - k) - radius = radius - k := by
        rw [Nat.add_comm, Nat.add_sub_cancel]
      simp [hzero, hle, hdelta]
  · have hge : radius ≤ k := Nat.le_of_not_le hle
    have hd : k - radius ≤ radius := by
      have : k ≤ radius + radius := by simpa [Nat.two_mul] using hk
      exact (Nat.sub_le_iff_le_add).mpr this
    have hrep : 2 * radius - k = radius - (k - radius) := by
      have hk' : k = radius + (k - radius) :=
        (Nat.add_sub_of_le hge).symm
      have htwo : 2 * radius - radius = radius := by
        rw [Nat.two_mul, Nat.add_sub_cancel]
      conv => lhs; rw [hk']
      rw [Nat.sub_add_eq, htwo]
    rw [hrep]
    unfold natSqDiff
    have hleft : radius - (k - radius) ≤ radius := Nat.sub_le _ _
    have hdelta :
        radius - (radius - (k - radius)) = k - radius := by
      conv =>
        lhs
        lhs
        rw [← Nat.sub_add_cancel hd]
      rw [Nat.add_comm]
      exact Nat.add_sub_cancel (k - radius) (radius - (k - radius))
    simp [hleft, hle, hdelta]

/-- A spike of mass `w` at index `a` contributes only at that slot. -/
theorem natSum_spike (bound a w : Nat) (g : Nat → Nat) :
    natSum bound (fun i => (if i = a then w else 0) * g i) =
      if a < bound then w * g a else 0 := by
  induction bound with
  | zero =>
      simp [natSum]
  | succ n ih =>
      rw [natSum_succ, ih]
      cases Nat.decEq n a with
      | isTrue heq =>
          rw [heq]
          simp
      | isFalse hne =>
          have hlast : (if n = a then w else 0) * g n = 0 := by
            simp [hne]
          rw [hlast, Nat.add_zero]
          by_cases hlt : a < n
          · have hsucc : a < n + 1 := Nat.lt_succ_of_lt hlt
            simp [hlt, hsucc]
          · have hsucc : ¬ a < n + 1 :=
              fun h => hlt (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h)
                (Ne.symm hne))
            simp [hlt, hsucc]

/-- Reindexing a finite sum from the far end does not change its value.
The identity is stated on length `n + 1` so that `n - i` stays a natural
number for every summand index `i ≤ n`. -/
theorem natSum_reverse (n : Nat) (f : Nat → Nat) :
    natSum (n + 1) (fun i => f (n - i)) = natSum (n + 1) f := by
  induction n generalizing f with
  | zero =>
      simp [natSum]
  | succ n ih =>
      have hrev :
          natSum (n + 2) (fun i => f (n + 1 - i)) =
            natSum (n + 1) (fun i => f (n + 1 - i)) + f 0 := by
        rw [natSum_succ]
        simp [Nat.sub_self]
      have hidx :
          natSum (n + 1) (fun i => f (n + 1 - i)) =
            natSum (n + 1) (fun i => f (n - i + 1)) := by
        apply natSum_congr
        intro i hi
        have hle : i ≤ n := Nat.le_of_lt_succ hi
        rw [Nat.succ_sub hle]
      have hshift :
          natSum (n + 1) (fun i => f (n - i + 1)) =
            natSum (n + 1) (fun j => f (j + 1)) :=
        ih (fun j => f (j + 1))
      rw [hrev, hidx, hshift]
      rw [Nat.add_comm]
      exact (natSum_head (n + 1) f).symm

/-- Pairing a centred window against its reflection: if weights are symmetric
about `radius`, then `∑ k w(k) = radius * ∑ w(k)`.  This is the Nat identity
behind the lattice-Gaussian mean. -/
theorem natSum_symm_center (radius : Nat) (w : Nat → Nat)
    (hsym : forall k, k ≤ 2 * radius → w (2 * radius - k) = w k) :
    natSum (2 * radius + 1) (fun k => k * w k) =
      radius * natSum (2 * radius + 1) w := by
  have hrev :=
    natSum_reverse (2 * radius) (fun k => k * w k)
  have hsym' :
      natSum (2 * radius + 1) (fun i =>
          (2 * radius - i) * w (2 * radius - i)) =
        natSum (2 * radius + 1) (fun i =>
          (2 * radius - i) * w i) := by
    apply natSum_congr
    intro i hi
    have hle : i ≤ 2 * radius := Nat.le_of_lt_succ hi
    rw [hsym i hle]
  have hS :
      natSum (2 * radius + 1) (fun k => k * w k) =
        natSum (2 * radius + 1) (fun i =>
          (2 * radius - i) * w i) :=
    hrev.symm.trans hsym'
  have hpair :
      natSum (2 * radius + 1) (fun k => k * w k) +
          natSum (2 * radius + 1) (fun i =>
            (2 * radius - i) * w i) =
        natSum (2 * radius + 1) (fun k => (2 * radius) * w k) := by
    rw [← natSum_add]
    apply natSum_congr
    intro k hk
    have hle : k ≤ 2 * radius := Nat.le_of_lt_succ hk
    rw [← Nat.add_mul, Nat.add_sub_of_le hle]
  have hdouble :
      natSum (2 * radius + 1) (fun k => k * w k) +
          natSum (2 * radius + 1) (fun k => k * w k) =
        (2 * radius) * natSum (2 * radius + 1) w := by
    calc
      natSum (2 * radius + 1) (fun k => k * w k) +
            natSum (2 * radius + 1) (fun k => k * w k)
          = natSum (2 * radius + 1) (fun k => k * w k) +
              natSum (2 * radius + 1) (fun i =>
                (2 * radius - i) * w i) :=
        congrArg
          (fun t =>
            natSum (2 * radius + 1) (fun k => k * w k) + t)
          hS
      _ = natSum (2 * radius + 1) (fun k => (2 * radius) * w k) :=
        hpair
      _ = (2 * radius) * natSum (2 * radius + 1) w :=
        natSum_mul_left (2 * radius + 1) (2 * radius) w
  have htwo :
      2 * natSum (2 * radius + 1) (fun k => k * w k) =
        2 * (radius * natSum (2 * radius + 1) w) := by
    calc
      2 * natSum (2 * radius + 1) (fun k => k * w k)
          = natSum (2 * radius + 1) (fun k => k * w k) +
              natSum (2 * radius + 1) (fun k => k * w k) :=
        Nat.two_mul _
      _ = (2 * radius) * natSum (2 * radius + 1) w :=
        hdouble
      _ = 2 * (radius * natSum (2 * radius + 1) w) := by
        rw [Nat.mul_assoc]
  exact Nat.mul_left_cancel (Nat.succ_pos 1) htwo

/-- Double-sum form of a product of finite sums. -/
theorem natSum_mul_natSum (n m : Nat) (a b : Nat → Nat) :
    natSum n (fun i => natSum m (fun j => a i * b j)) =
      natSum n a * natSum m b := by
  have hinner :
      natSum n (fun i => natSum m (fun j => a i * b j)) =
        natSum n (fun i => a i * natSum m b) := by
    apply natSum_congr
    intro i _
    exact natSum_mul_left m (a i) b
  rw [hinner]
  have hswap :
      natSum n (fun i => a i * natSum m b) =
        natSum n (fun i => natSum m b * a i) := by
    apply natSum_congr
    intro i _
    exact Nat.mul_comm _ _
  rw [hswap, natSum_mul_left, Nat.mul_comm]

end Combinatorics
end Probability
end Thesis
