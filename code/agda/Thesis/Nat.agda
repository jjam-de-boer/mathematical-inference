module Thesis.Nat where

open import Thesis.Equality

-- Natural numbers are the unary inductive type. Arithmetic below is defined
-- by recursion on that structure, so every equation is witnessed by a finite
-- computation or an induction on it. Zero is least, and a positive number
-- carries its predecessor explicitly.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_ _-_
infixl 7 _*_
infix  4 _≤_ _<_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

-- Truncating subtraction. Theorems that recover a summand carry an explicit
-- inequality so the truncated case is never the one in use.
_-_ : ℕ → ℕ → ℕ
m     - zero   = m
zero  - suc n  = zero
suc m - suc n  = m - n

-- The usual inductive order. `m ≤ n` is a chain of successor steps from `m`
-- up to `n`, so the proof records how much larger `n` is.
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- Strict order is one successor step below the weak order. It introduces no
-- separate truncated witness.
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n      _         = z≤n
≤-trans (s≤s p)  (s≤s q)   = s≤s (≤-trans p q)

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n     = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

-- A successor is never at most its own predecessor. This is the only order
-- fact used to refute a strict comparison of a number with itself.
suc-≰ : ∀ {n} → suc n ≤ n → ⊥
suc-≰ {suc n} (s≤s p) = suc-≰ p
suc-≰ {zero}  ()

<-irrefl : ∀ {n} → n < n → ⊥
<-irrefl p = suc-≰ p

-- Strict order composes. The middle value sits strictly below its successor,
-- so the two successor steps join into one.
<-trans : ∀ {m n p} → m < n → n < p → m < p
<-trans {n = n} mn np = ≤-trans mn (≤-trans (≤-step (≤-refl n)) np)

-- Once `n` is known to be at most `m`, a strict descent from `m` to `n` is
-- impossible.
≰-of-≥ : ∀ {m n} → n ≤ m → m < n → ⊥
≰-of-≥ n≤m m<n = suc-≰ (≤-trans m<n n≤m)

≡-≤ : ∀ {m n} → m ≡ n → m ≤ n
≡-≤ refl = ≤-refl _

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero}  {zero}  z≤n     z≤n     = refl
≤-antisym {zero}  {suc _} z≤n     ()
≤-antisym {suc _} {zero}  ()      _
≤-antisym {suc _} {suc _} (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

-- `m < suc n` is exactly the weak comparison `m ≤ n`. The two directions are
-- the successor constructor and its inverse.
≤-<s : ∀ {m n} → m ≤ n → m < suc n
≤-<s p = s≤s p

<s-≤ : ∀ {m n} → m < suc n → m ≤ n
<s-≤ (s≤s p) = p

-- Total comparison of any two numbers, computed by recursion. The result is
-- a proof of one of the two exhaustive alternatives, not a Boolean alone.
compare≤ : ∀ m n → m ≤ n ⊎ n < m
compare≤ zero n          = inl z≤n
compare≤ (suc m) zero    = inr (s≤s z≤n)
compare≤ (suc m) (suc n) with compare≤ m n
... | inl p = inl (s≤s p)
... | inr p = inr (s≤s p)

-- `m < n` or else `n ≤ m`. Used when a cleared strict inequality must be
-- recovered from a product that has been multiplied by a positive factor.
lt-or-ge : ∀ m n → m < n ⊎ n ≤ m
lt-or-ge m n with compare≤ (suc m) n
... | inl p = inl p
... | inr q = inr (<s-≤ q)

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-idʳ : ∀ m → m + zero ≡ m
+-idʳ zero    = refl
+-idʳ (suc m) rewrite +-idʳ m = refl

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero n rewrite +-idʳ n = refl
+-comm (suc m) n rewrite +-comm m n | +-suc n m = refl

+-cancelˡ-≡ : ∀ k {m n} → k + m ≡ k + n → m ≡ n
+-cancelˡ-≡ zero    eq = eq
+-cancelˡ-≡ (suc k) eq = +-cancelˡ-≡ k (suc-injective eq)
  where
  suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-injective refl = refl

+-cancelʳ-≡ : ∀ {m n} k → m + k ≡ n + k → m ≡ n
+-cancelʳ-≡ {m} {n} k eq rewrite +-comm m k | +-comm n k = +-cancelˡ-≡ k eq

+-cancelˡ-≤ : ∀ k {m n} → k + m ≤ k + n → m ≤ n
+-cancelˡ-≤ zero    le        = le
+-cancelˡ-≤ (suc k) (s≤s le) = +-cancelˡ-≤ k le

+-monoʳ : ∀ p {m n} → m ≤ n → p + m ≤ p + n
+-monoʳ zero    le = le
+-monoʳ (suc p) le = s≤s (+-monoʳ p le)

+-monoˡ : ∀ {m n} → m ≤ n → ∀ p → m + p ≤ n + p
+-monoˡ {m} {n} m≤n p rewrite +-comm m p | +-comm n p = +-monoʳ p m≤n

-- Adding on the left cannot make a number smaller.
≤-+ˡ : ∀ n m → m ≤ n + m
≤-+ˡ zero m = ≤-refl m
≤-+ˡ (suc n) m = ≤-trans (≤-+ˡ n m) (≤-step (≤-refl (n + m)))

*-zeroʳ : ∀ m → m * zero ≡ zero
*-zeroʳ zero    = refl
*-zeroʳ (suc m) rewrite *-zeroʳ m = refl

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  begin
    suc m * suc n
  ≡⟨⟩
    suc n + m * suc n
  ≡⟨ cong (suc n +_) (*-suc m n) ⟩
    suc n + (m + m * n)
  ≡⟨ sym (+-assoc (suc n) m (m * n)) ⟩
    (suc n + m) + m * n
  ≡⟨ cong (_+ m * n) (suc-swap n m) ⟩
    (suc m + n) + m * n
  ≡⟨ +-assoc (suc m) n (m * n) ⟩
    suc m + (n + m * n)
  ≡⟨⟩
    suc m + suc m * n
  ∎
  where
  suc-swap : ∀ n m → suc n + m ≡ suc m + n
  suc-swap n m =
    begin
      suc n + m
    ≡⟨⟩
      suc (n + m)
    ≡⟨ cong suc (+-comm n m) ⟩
      suc (m + n)
    ≡⟨⟩
      suc m + n
    ∎

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = sym (*-zeroʳ n)
*-comm (suc m) n =
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m
  ≡⟨ sym (*-suc n m) ⟩
    n * suc m
  ∎

*-distribʳ-+ : ∀ m n p → (m + n) * p ≡ m * p + n * p
*-distribʳ-+ zero n p = refl
*-distribʳ-+ (suc m) n p rewrite *-distribʳ-+ m n p =
  sym (+-assoc p (m * p) (n * p))

*-distribˡ-+ : ∀ m n p → m * (n + p) ≡ m * n + m * p
*-distribˡ-+ m n p rewrite *-comm m (n + p) | *-comm m n | *-comm m p =
  *-distribʳ-+ n p m

*-assoc : ∀ m n p → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distribʳ-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong (n * p +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    suc m * (n * p)
  ∎

*-idʳ : ∀ m → m * suc zero ≡ m
*-idʳ m =
  begin
    m * suc zero
  ≡⟨ *-suc m zero ⟩
    m + m * zero
  ≡⟨ cong (m +_) (*-zeroʳ m) ⟩
    m + zero
  ≡⟨ +-idʳ m ⟩
    m
  ∎

-- Multiplication on the left argument preserves the weak order.
*-monoˡ : ∀ {m n} → m ≤ n → ∀ p → m * p ≤ n * p
*-monoˡ z≤n     p = z≤n
*-monoˡ (s≤s p) q = +-monoʳ q (*-monoˡ p q)

*-monoʳ : ∀ p {m n} → m ≤ n → p * m ≤ p * n
*-monoʳ p {m} {n} m≤n rewrite *-comm p m | *-comm p n = *-monoˡ m≤n p

-- A positive right factor makes multiplication by a successor strictly larger.
-- The predecessor of that factor is what the inductive order step consumes.
*-<-suc : ∀ {m c} → 0 < c → m * c < suc m * c
*-<-suc {m} {suc c} _ = s≤s (≤-+ˡ c (m * suc c))
*-<-suc {m} {zero} ()

-- Strict increase on the left survives multiplication by a positive factor.
*-mono-< : ∀ {a b c} → a < b → 0 < c → a * c < b * c
*-mono-< {a} {b} {c} a<b c>0 = ≤-trans (*-<-suc {a} {c} c>0) (*-monoˡ a<b c)

-- Cancel a positive right factor from a weak product comparison.
≤-cancel-*-right : ∀ {m n c} → 0 < c → m * c ≤ n * c → m ≤ n
≤-cancel-*-right {m} {n} {zero} () _
≤-cancel-*-right {zero} {n} {suc c} _ _ = z≤n
≤-cancel-*-right {suc m} {zero} {suc c} _ ()
≤-cancel-*-right {suc m} {suc n} {suc c} pos (s≤s le) =
  s≤s (≤-cancel-*-right {m} {n} {suc c} pos (+-cancelˡ-≤ c le))

*-cancel-≡-right : ∀ {m n c} → 0 < c → m * c ≡ n * c → m ≡ n
*-cancel-≡-right {m} {n} {c} c>0 eq =
  ≤-antisym (≤-cancel-*-right c>0 (≡-≤ eq))
            (≤-cancel-*-right c>0 (≡-≤ (sym eq)))

-- A product vanishes only when a factor does. With the other factor known
-- positive, the remaining factor is zero.
*-zero-inv : ∀ m n → m * n ≡ 0 → m ≡ 0 ⊎ n ≡ 0
*-zero-inv zero    n       _  = inl refl
*-zero-inv (suc m) zero    _  = inr refl
*-zero-inv (suc m) (suc n) ()

*-zero-left : ∀ {m n} → m * n ≡ 0 → n ≢ 0 → m ≡ 0
*-zero-left {m} {n} eq n≢0 with *-zero-inv m n eq
... | inl m≡0 = m≡0
... | inr n≡0 = ⊥-elim (n≢0 n≡0)

pos-≢0 : ∀ {n} → 0 < n → n ≢ 0
pos-≢0 {suc n} _ ()
pos-≢0 {zero}  ()

eq-zero-or-pos : ∀ n → n ≡ 0 ⊎ 0 < n
eq-zero-or-pos zero    = inl refl
eq-zero-or-pos (suc n) = inr (s≤s z≤n)

-- Positive factors stay positive. Both arguments are inspected only through
-- their positivity proofs, which force successor form.
*-pos : ∀ {m n} → 0 < m → 0 < n → 0 < m * n
*-pos {suc m} {suc n} _ _ = s≤s z≤n
*-pos {zero}  {_}     () _
*-pos {_}     {zero}  _ ()

-- Recover the left summand after a witnessed subtraction.
sub-add : ∀ {m n} → m ≤ n → (n - m) + m ≡ n
sub-add {zero} {n} z≤n rewrite +-idʳ n = refl
sub-add {suc m} {suc n} (s≤s p) rewrite +-suc (n - m) m | sub-add p = refl
sub-add {suc _} {zero} ()

-- From `x + y ≡ z` with `y ≤ z`, `x` is the witnessed difference `z - y`.
cancel-sub : ∀ {x y z} → y ≤ z → x + y ≡ z → x ≡ z - y
cancel-sub {x} {y} {z} y≤z eq =
  +-cancelʳ-≡ y (trans eq (sym (sub-add y≤z)))

-- Subtraction on the left distributes over multiplication on the right,
-- once the subtracted number is known not to exceed the minuend.
*-sub-distribʳ : ∀ {m n} p → n ≤ m → (m - n) * p ≡ m * p - n * p
*-sub-distribʳ {m} {n} p n≤m =
  cancel-sub (*-monoˡ n≤m p)
    (trans (sym (*-distribʳ-+ (m - n) n p))
           (cong (λ k → k * p) (sub-add n≤m)))

-- Reassociate three factors while swapping the last two. This is the
-- rearrangement used when a cross-multiplication is cycled past a third
-- positive denominator.
*-reorder₃ : ∀ a b c → (a * b) * c ≡ (a * c) * b
*-reorder₃ a b c rewrite *-assoc a b c | *-comm b c | sym (*-assoc a c b) = refl

-- Reassociate four factors, exchanging the two middle ones. Both sides are
-- the product of the same four numbers.
*-reorder₄ : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
*-reorder₄ a b c d =
  begin
    (a * b) * (c * d)
  ≡⟨ *-assoc a b (c * d) ⟩
    a * (b * (c * d))
  ≡⟨ cong (a *_) (sym (*-assoc b c d)) ⟩
    a * ((b * c) * d)
  ≡⟨ cong (λ k → a * (k * d)) (*-comm b c) ⟩
    a * ((c * b) * d)
  ≡⟨ cong (a *_) (*-assoc c b d) ⟩
    a * (c * (b * d))
  ≡⟨ sym (*-assoc a c (b * d)) ⟩
    (a * c) * (b * d)
  ∎

-- An inequality has at most one proof. The constructors record the exact
-- chain of successors, so two chains between the same endpoints agree step
-- by step.
≤-unique : ∀ {m n} (p q : m ≤ n) → p ≡ q
≤-unique z≤n     z≤n     = refl
≤-unique (s≤s p) (s≤s q) = cong s≤s (≤-unique p q)

-- Decide equality by recursion on the unary structure. The negative branch
-- is a refutation, so a later use can derive ⊥ from an identification of
-- distinct numbers.
_≟_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
zero  ≟ suc n  = no λ ()
suc m ≟ zero   = no λ ()
suc m ≟ suc n with m ≟ n
... | yes eq = yes (cong suc eq)
... | no  ne = no λ { refl → ne refl }

