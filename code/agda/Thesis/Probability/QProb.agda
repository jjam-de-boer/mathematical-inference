module Thesis.Probability.QProb where

open import Thesis.Equality
open import Thesis.Nat hiding (zero)
open import Thesis.List

-- A nonnegative rational presented as a numerator over a positive
-- denominator. The denominator proof is part of the data, so a presentation
-- never divides by zero. Magnitudes are compared by cross-multiplication:
-- two presentations are equivalent when they determine the same ratio, and
-- no cancelled representative is selected.

record QProb : Set where
  constructor qprob
  field
    num     : ℕ
    den     : ℕ
    den-pos : 0 < den

open QProb public

-- Both directions of a logical equivalence, kept as data so each use names
-- which direction it applies.
record _⇔_ (A B : Set) : Set where
  constructor iff
  field
    to   : A → B
    from : B → A

-- Cross-multiplication of the two presentations.
Equiv : QProb → QProb → Set
Equiv p q = num p * den q ≡ num q * den p

-- Decided by equality of the two natural cross-products.
equiv-dec : ∀ p q → Dec (Equiv p q)
equiv-dec p q = (num p * den q) ≟ (num q * den p)

zero : QProb
zero = qprob 0 1 (s≤s z≤n)

one : QProb
one = qprob 1 1 (s≤s z≤n)

-- The sum of two presentations. Denominators are multiplied, and each
-- numerator is cleared by the other denominator, so the sum does not depend
-- on a common reduced denominator being chosen in advance.
add : QProb → QProb → QProb
add p q = qprob (num p * den q + num q * den p)
                (den p * den q)
                (*-pos (den-pos p) (den-pos q))

-- Multiply the numerator by a natural number. The denominator is unchanged,
-- so its positivity proof is reused.
scale : ℕ → QProb → QProb
scale k p = qprob (k * num p) (den p) (den-pos p)

mul : QProb → QProb → QProb
mul p q = qprob (num p * num q) (den p * den q)
                (*-pos (den-pos p) (den-pos q))

-- Division requires a positive numerator on the divisor. The resulting
-- denominator is that numerator times the dividend's denominator, hence
-- positive. A zero divisor is not completed to a value.
div : (p q : QProb) → 0 < num q → QProb
div p q q>0 = qprob (num p * den q) (den p * num q) (*-pos (den-pos p) q>0)

equiv-refl : ∀ p → Equiv p p
equiv-refl p = refl

equiv-sym : ∀ {p q} → Equiv p q → Equiv q p
equiv-sym h = sym h

-- Equivalence is transitive. The intermediate denominator is positive, so it
-- can be cancelled after the two cross-multiplications have been aligned.
equiv-trans : ∀ {p q r} → Equiv p q → Equiv q r → Equiv p r
equiv-trans {p} {q} {r} hpq hqr =
  *-cancel-≡-right (den-pos q) (aligned hpq hqr)
  where
  zero-prod : ∀ {a b} → a ≡ 0 → a * b ≡ 0
  zero-prod refl = refl

  aligned : Equiv p q → Equiv q r →
            (num p * den r) * den q ≡ (num r * den p) * den q
  aligned hpq' hqr' =
    begin
      (num p * den r) * den q
    ≡⟨ *-reorder₃ (num p) (den r) (den q) ⟩
      (num p * den q) * den r
    ≡⟨ cong (_* den r) hpq' ⟩
      (num q * den p) * den r
    ≡⟨ *-reorder₃ (num q) (den p) (den r) ⟩
      (num q * den r) * den p
    ≡⟨ cong (_* den p) hqr' ⟩
      (num r * den q) * den p
    ≡⟨ *-reorder₃ (num r) (den q) (den p) ⟩
      (num r * den p) * den q
    ∎

-- Multiplying by a zero factor yields zero. Used when a numerator vanishes.
zero-prod : ∀ {a b} → a ≡ 0 → a * b ≡ 0
zero-prod refl = refl

-- Equivalent presentations have zero numerators together. Cancelling the
-- other, positive, denominator leaves the remaining numerator at zero.
equiv-num-zero : ∀ {p q} → Equiv p q → (num p ≡ 0) ⇔ (num q ≡ 0)
equiv-num-zero {p} {q} h = iff
  (λ pz → *-zero-left (trans (sym h) (zero-prod pz)) (pos-≢0 (den-pos p)))
  (λ qz → *-zero-left (trans h (zero-prod qz)) (pos-≢0 (den-pos q)))

-- Strict positivity of the numerator is likewise invariant. A zero on the
-- other side would contradict the zero-numerator equivalence.
equiv-num-pos : ∀ {p q} → Equiv p q → (0 < num p) ⇔ (0 < num q)
equiv-num-pos {p} {q} h = iff
  (λ hp → right-pos hp (eq-zero-or-pos (num q)))
  (λ hq → left-pos hq (eq-zero-or-pos (num p)))
  where
  link = equiv-num-zero {p} {q} h
  right-pos : 0 < num p → num q ≡ 0 ⊎ 0 < num q → 0 < num q
  right-pos hp (inr ok) = ok
  right-pos hp (inl qz) = ⊥-elim (pos-≢0 hp (_⇔_.from link qz))
  left-pos : 0 < num q → num p ≡ 0 ⊎ 0 < num p → 0 < num p
  left-pos hq (inr ok) = ok
  left-pos hq (inl pz) = ⊥-elim (pos-≢0 hq (_⇔_.to link pz))

-- Addition respects cross-multiplication. Each summand is rearranged
-- separately, then the common denominator product is factored back out.
add-cong : ∀ {p p' q q'} → Equiv p p' → Equiv q q' →
           Equiv (add p q) (add p' q')
add-cong {p} {p'} {q} {q'} hp hq =
  begin
    (num p * den q + num q * den p) * (den p' * den q')
  ≡⟨ *-distribʳ-+ (num p * den q) (num q * den p) (den p' * den q') ⟩
    (num p * den q) * (den p' * den q') +
      (num q * den p) * (den p' * den q')
  ≡⟨ cong₂ _+_ (left-summand hp) (right-summand hq) ⟩
    (num p' * den q') * (den p * den q) +
      (num q' * den p') * (den p * den q)
  ≡⟨ sym (*-distribʳ-+ (num p' * den q') (num q' * den p') (den p * den q)) ⟩
    (num p' * den q' + num q' * den p') * (den p * den q)
  ∎
  where
  left-summand : Equiv p p' →
    (num p * den q) * (den p' * den q') ≡
    (num p' * den q') * (den p * den q)
  left-summand hp' =
    begin
      (num p * den q) * (den p' * den q')
    ≡⟨ *-reorder₄ (num p) (den q) (den p') (den q') ⟩
      (num p * den p') * (den q * den q')
    ≡⟨ cong (_* (den q * den q')) hp' ⟩
      (num p' * den p) * (den q * den q')
    ≡⟨ cong ((num p' * den p) *_) (*-comm (den q) (den q')) ⟩
      (num p' * den p) * (den q' * den q)
    ≡⟨ *-reorder₄ (num p') (den p) (den q') (den q) ⟩
      (num p' * den q') * (den p * den q)
    ∎

  right-summand : Equiv q q' →
    (num q * den p) * (den p' * den q') ≡
    (num q' * den p') * (den p * den q)
  right-summand hq' =
    begin
      (num q * den p) * (den p' * den q')
    ≡⟨ cong ((num q * den p) *_) (*-comm (den p') (den q')) ⟩
      (num q * den p) * (den q' * den p')
    ≡⟨ *-reorder₄ (num q) (den p) (den q') (den p') ⟩
      (num q * den q') * (den p * den p')
    ≡⟨ cong (_* (den p * den p')) hq' ⟩
      (num q' * den q) * (den p * den p')
    ≡⟨ cong ((num q' * den q) *_) (*-comm (den p) (den p')) ⟩
      (num q' * den q) * (den p' * den p)
    ≡⟨ *-reorder₄ (num q') (den q) (den p') (den p) ⟩
      (num q' * den p') * (den q * den p)
    ≡⟨ cong ((num q' * den p') *_) (*-comm (den q) (den p)) ⟩
      (num q' * den p') * (den p * den q)
    ∎

-- Addition of presentations commutes up to cross-multiplication. The two
-- cleared numerators trade places, and the two denominators trade places.
add-comm : ∀ p q → Equiv (add p q) (add q p)
add-comm p q rewrite +-comm (num p * den q) (num q * den p)
                   | *-comm (den q) (den p) = refl

-- Adding the zero presentation does not change the magnitude. The new
-- denominator is the old one multiplied by one.
add-zero : ∀ p → Equiv (add p zero) p
add-zero p =
  begin
    (num p * 1 + 0 * den p) * den p
  ≡⟨ cong (_* den p) (+-idʳ (num p * 1)) ⟩
    (num p * 1) * den p
  ≡⟨ cong (_* den p) (*-idʳ (num p)) ⟩
    num p * den p
  ≡⟨ cong (num p *_) (sym (*-idʳ (den p))) ⟩
    num p * (den p * 1)
  ∎

-- Addition of three presentations associates up to cross-multiplication.
-- Clearing the three denominators produces one polynomial either way, and
-- the two products of denominators agree by associativity of multiplication.
add-assoc : ∀ p q r → Equiv (add (add p q) r) (add p (add q r))
add-assoc p q r =
  trans (cong (L *_) (sym dens)) (cong (_* Dl) (trans expandL (sym expandR)))
  where
  A  = num p
  B  = num q
  C  = num r
  Da = den p
  Db = den q
  Dc = den r
  L  = (A * Db + B * Da) * Dc + C * (Da * Db)
  R  = A * (Db * Dc) + (B * Dc + C * Db) * Da
  Dl = (Da * Db) * Dc
  Dr = Da * (Db * Dc)

  dens : Dl ≡ Dr
  dens = *-assoc Da Db Dc

  expandL : L ≡ (A * (Db * Dc) + (B * Dc) * Da) + (C * Db) * Da
  expandL =
    begin
      (A * Db + B * Da) * Dc + C * (Da * Db)
    ≡⟨ cong (_+ C * (Da * Db)) (*-distribʳ-+ (A * Db) (B * Da) Dc) ⟩
      ((A * Db) * Dc + (B * Da) * Dc) + C * (Da * Db)
    ≡⟨ cong₂ _+_ (cong₂ _+_ (*-assoc A Db Dc) (*-reorder₃ B Da Dc))
                 (trans (sym (*-assoc C Da Db)) (*-reorder₃ C Da Db)) ⟩
      (A * (Db * Dc) + (B * Dc) * Da) + (C * Db) * Da
    ∎

  expandR : R ≡ (A * (Db * Dc) + (B * Dc) * Da) + (C * Db) * Da
  expandR =
    begin
      A * (Db * Dc) + (B * Dc + C * Db) * Da
    ≡⟨ cong (A * (Db * Dc) +_) (*-distribʳ-+ (B * Dc) (C * Db) Da) ⟩
      A * (Db * Dc) + ((B * Dc) * Da + (C * Db) * Da)
    ≡⟨ sym (+-assoc (A * (Db * Dc)) ((B * Dc) * Da) ((C * Db) * Da)) ⟩
      (A * (Db * Dc) + (B * Dc) * Da) + (C * Db) * Da
    ∎

-- Order after clearing denominators. A reduced fraction is never required.
LE : QProb → QProb → Set
LE p q = num p * den q ≤ num q * den p

LT : QProb → QProb → Set
LT p q = num p * den q < num q * den p

lt-irrefl : ∀ p → LT p p → ⊥
lt-irrefl p p<p = <-irrefl p<p

le-refl : ∀ p → LE p p
le-refl p = ≤-refl (num p * den p)

-- The zero presentation is a lower bound.
zero-le : ∀ p → LE zero p
zero-le p rewrite *-idʳ (num p) = z≤n

-- With one shared denominator, the order is the order of the numerators.
le-of-same-den : ∀ {p q} → den p ≡ den q → num p ≤ num q → LE p q
le-of-same-den {p} {q} dens nums rewrite dens = *-monoˡ nums (den q)

lt-of-same-den : ∀ {p q} → den p ≡ den q → num p < num q → LT p q
lt-of-same-den {p} {q} dens nums rewrite dens = *-mono-< nums (den-pos q)

-- Move an inequality across a pair of definitional rearrangements.
≤-cong : ∀ {a b c d} → a ≡ c → b ≡ d → a ≤ b → c ≤ d
≤-cong {a} {b} {c} {d} ac bd ab =
  subst (λ x → x ≤ d) ac (subst (λ y → a ≤ y) bd ab)

-- Cross-multiplication order is transitive. The intermediate denominator is
-- positive, so it cancels once both comparisons sit on that common factor.
le-trans : ∀ {p q r} → LE p q → LE q r → LE p r
le-trans {p} {q} {r} pq qr =
  ≤-cancel-*-right (den-pos q) final
  where
  step1 : (num p * den r) * den q ≤ (num q * den p) * den r
  step1 =
    ≤-cong (*-reorder₃ (num p) (den q) (den r)) refl (*-monoˡ pq (den r))

  step2 : (num p * den r) * den q ≤ (num q * den r) * den p
  step2 = ≤-cong refl (*-reorder₃ (num q) (den p) (den r)) step1

  step3 : (num p * den r) * den q ≤ (num r * den q) * den p
  step3 = ≤-trans step2 (*-monoˡ qr (den p))

  final : (num p * den r) * den q ≤ (num r * den p) * den q
  final = ≤-cong refl (*-reorder₃ (num r) (den q) (den p)) step3
