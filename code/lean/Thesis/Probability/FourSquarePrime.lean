import Thesis.Probability.FourSquareDescent

namespace Thesis.Probability.FourSquareNorm

/-!
# A represented multiple of a prime from a finite residue collision

For odd p both x ↦ x² and y ↦ −1−y² are injective modulo p on
0,…,(p−1)/2. The two lists have more entries in total than there are
residue classes. A collision between the lists gives a positive multiple
of p of the form 1+x²+y². The interval bounds make the multiplier less
than p. This finite pigeonhole argument supplies exactly the starting
witness required by the descent.
-/

/-- All nontrivial divisors of this positive integer are the integer itself.
The global proof later separates this case by finite divisibility checks. -/
def HasOnlyPrimeDivisors (p : Nat) : Prop :=
  ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

private theorem list_length_bound [BEq A] [LawfulBEq A] (source target : List A)
    (nodup : source.Nodup) (subset : ∀ a ∈ source, a ∈ target) : source.length ≤ target.length := by
  induction source generalizing target with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    have unique := List.nodup_cons.mp nodup
    have inTarget : a ∈ target := subset a List.mem_cons_self
    have tailBound := ih (target.erase a) unique.2 (by
      intro x member
      have apart : x ≠ a := fun same => unique.1 (same ▸ member)
      exact (List.mem_erase_of_ne apart).mpr (subset x (List.mem_cons_of_mem _ member)))
    have targetNonempty : 0 < target.length := List.length_pos_of_mem inTarget
    rw [List.length_erase_of_mem inTarget] at tailBound
    simp only [List.length_cons]
    omega

private theorem two_images_collide {m p : Nat} (large : p < m + m)
    (f g : Fin m → Fin p) (injectiveF : Function.Injective f) (injectiveG : Function.Injective g) :
    ∃ x y, f x = g y := by
  if found : ∃ x y, f x = g y then exact found
  else
    exfalso
    have unique : ((List.finRange m).map f ++ (List.finRange m).map g).Nodup := by
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact List.Pairwise.map _ (fun a b apart same => apart (injectiveF same)) (Thesis.Probability.finRange_nodup m)
      · exact List.Pairwise.map _ (fun a b apart same => apart (injectiveG same)) (Thesis.Probability.finRange_nodup m)
      · intro a inFirst b inSecond same
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp inFirst
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp inSecond
        exact found ⟨x, y, same⟩
    have bounds := list_length_bound _ (List.finRange p) unique (fun a _ => List.mem_finRange a)
    simp only [List.length_append, List.length_map, List.length_finRange] at bounds
    omega

private theorem prime_dvd_int_mul (p : Nat) (prime : HasOnlyPrimeDivisors p) (a b : Int)
    (product : (p : Int) ∣ a * b) : (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at product
  by_cases first : p ∣ a.natAbs
  · exact .inl (Int.ofNat_dvd_left.mpr first)
  · have gcdOne : Nat.gcd p a.natAbs = 1 := by
      rcases prime _ (Nat.gcd_dvd_left _ _) with one | full
      · exact one
      · exact (first (full ▸ Nat.gcd_dvd_right p a.natAbs)).elim
    exact .inr (Int.ofNat_dvd_left.mpr (Nat.Coprime.dvd_of_dvd_mul_left gcdOne product))

private theorem dvd_small_eq_zero {p k : Int} (positive : 0 < p) (lower : -p < k) (upper : k < p)
    (divides : p ∣ k) : k = 0 := by
  rcases divides with ⟨q, rfl⟩
  by_cases zero : q = 0
  · simp [zero]
  · by_cases sign : 0 < q
    · have tooLarge := Int.mul_le_mul_of_nonneg_left (show 1 ≤ q by omega) (show 0 ≤ p by omega)
      rw [Int.mul_one] at tooLarge
      omega
    · have tooSmall := Int.mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) (show 0 ≤ p by omega)
      simp only [Int.mul_neg, Int.mul_one] at tooSmall
      omega

private def residue (p : Nat) (positive : 0 < p) (k : Int) : Fin p :=
  ⟨(k % (p : Int)).toNat, by
    have bound := Int.emod_lt_of_pos k (show 0 < (p : Int) by omega)
    omega⟩

private theorem residue_same (p : Nat) (positive : 0 < p) {a b : Int}
    (same : residue p positive a = residue p positive b) : (p : Int) ∣ a - b := by
  have aSign := Int.emod_nonneg a (show (p : Int) ≠ 0 by omega)
  have bSign := Int.emod_nonneg b (show (p : Int) ≠ 0 by omega)
  have residueEq := congrArg Fin.val same
  change (a % (p : Int)).toNat = (b % (p : Int)).toNat at residueEq
  have remainderEq : a % (p : Int) = b % (p : Int) := by omega
  exact Int.dvd_sub (Int.dvd_self_sub_of_emod_eq remainderEq)
    (Int.dvd_self_sub_emod (x := b) (m := (p : Int))) |>.elim fun witness proof => ⟨witness, by omega⟩

private theorem half_square_injective (p : Nat) (positive : 0 < p) (odd : p % 2 = 1)
    (prime : HasOnlyPrimeDivisors p) (x y : Fin (p / 2 + 1))
    (divides : (p : Int) ∣ (x.val : Int) * x.val - (y.val : Int) * y.val) : x = y := by
  let a : Int := x.val
  let b : Int := y.val
  have xBound := x.isLt
  have yBound := y.isLt
  have identity : a * a - b * b = (a - b) * (a + b) := by
    simp only [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg, Int.mul_comm]
    omega
  change (p : Int) ∣ a * a - b * b at divides
  rw [identity] at divides
  rcases prime_dvd_int_mul p prime (a - b) (a + b) divides with difference | sum
  · have zero := dvd_small_eq_zero (show 0 < (p : Int) by omega)
      (k := a - b) (by dsimp [a,b]; omega) (by dsimp [a,b]; omega) difference
    apply Fin.ext
    dsimp [a,b] at zero
    omega
  · have zero := dvd_small_eq_zero (show 0 < (p : Int) by omega)
      (k := a + b) (by dsimp [a,b]; omega) (by dsimp [a,b]; omega) sum
    apply Fin.ext
    dsimp [a,b] at zero
    omega

/-- The initial quadruple before descending on the multiplier. -/
theorem odd_prime_multiple (p : Nat) (greater : 1 < p) (odd : p % 2 = 1)
    (prime : HasOnlyPrimeDivisors p) : ∃ m : Nat, 0 < m ∧ m < p ∧ ∃ q : Quad, q.norm = (m : Int) * p := by
  have positive : 0 < p := by omega
  let f := fun x : Fin (p / 2 + 1) => residue p positive ((x.val : Int) * x.val)
  let g := fun x : Fin (p / 2 + 1) => residue p positive (-1 - (x.val : Int) * x.val)
  have fInj : Function.Injective f := by
    intro x y same
    exact half_square_injective p positive odd prime x y (residue_same p positive same)
  have gInj : Function.Injective g := by
    intro x y same
    obtain ⟨w, equal⟩ := residue_same p positive same
    exact half_square_injective p positive odd prime x y ⟨-w, by rw [Int.mul_neg]; omega⟩
  obtain ⟨x, y, same⟩ := two_images_collide (by omega) f g fInj gInj
  let q : Quad := ⟨x.val, y.val, 1, 0⟩
  have qNorm : q.norm = (x.val : Int) * x.val + (y.val : Int) * y.val + 1 := by simp [q, Quad.norm]
  obtain ⟨m, factor⟩ := residue_same p positive same
  have represented : q.norm = (p : Int) * m := by rw [qNorm]; omega
  have px := x.isLt
  have py := y.isLt
  have qPositive : 0 < q.norm := by
    rw [qNorm]
    have hx := Int.mul_nonneg (a := (x.val : Int)) (b := (x.val : Int)) (by omega) (by omega)
    have hy := Int.mul_nonneg (a := (y.val : Int)) (b := (y.val : Int)) (by omega) (by omega)
    omega
  have mPositive : 0 < m := by
    apply Int.lt_of_mul_lt_mul_left (a := (p : Int)) _ (by omega)
    rw [Int.mul_zero, ← represented]
    exact qPositive
  have qSmall : q.norm < (p : Int) * p := by
    let a : Int := x.val
    let b : Int := y.val
    have ha : a * a ≤ (p : Int) * a := Int.mul_le_mul_of_nonneg_right (by dsimp [a]; omega) (by dsimp [a]; omega)
    have hb : b * b ≤ (p : Int) * b := Int.mul_le_mul_of_nonneg_right (by dsimp [b]; omega) (by dsimp [b]; omega)
    have bound : a + b ≤ (p : Int) - 1 := by dsimp [a,b]; omega
    have multiplied := Int.mul_le_mul_of_nonneg_left bound (show 0 ≤ (p : Int) by omega)
    rw [Int.mul_add, Int.mul_sub, Int.mul_one] at multiplied
    rw [qNorm]
    change a * a + b * b + 1 < _
    omega
  have mSmall : m < (p : Int) := by
    apply Int.lt_of_mul_lt_mul_left (a := (p : Int)) _ (by omega)
    rw [← represented]
    exact qSmall
  refine ⟨m.toNat, by omega, by omega, q, ?_⟩
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ m), Int.mul_comm m]
  exact represented

end Thesis.Probability.FourSquareNorm
