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

-- The same transport for a strict comparison.
<-cong : ∀ {a b c d} → a ≡ c → b ≡ d → a < b → c < d
<-cong {a} {b} {c} {d} ac bd ab =
  subst (λ x → x < d) ac (subst (λ y → a < y) bd ab)

-- Strict cross-multiplication order is transitive. If the cleared comparison
-- were not strict, multiplying by the positive intermediate denominator
-- would contradict the strict chain.
lt-trans : ∀ {p q r} → LT p q → LT q r → LT p r
lt-trans {p} {q} {r} pq qr with lt-or-ge (num p * den r) (num r * den p)
... | inl strict = strict
... | inr ge     = ⊥-elim (≰-of-≥ (*-monoˡ ge (den q)) cleared)
  where
  step1 : (num p * den r) * den q < (num q * den p) * den r
  step1 = <-cong (*-reorder₃ (num p) (den q) (den r)) refl (*-mono-< pq (den-pos r))

  step2 : (num p * den r) * den q < (num q * den r) * den p
  step2 = <-cong refl (*-reorder₃ (num q) (den p) (den r)) step1

  step3 : (num p * den r) * den q < (num r * den q) * den p
  step3 = <-trans step2 (*-mono-< qr (den-pos p))

  cleared : (num p * den r) * den q < (num r * den p) * den q
  cleared = <-cong refl (*-reorder₃ (num r) (den q) (den p)) step3

-- Move a cleared numerator across an equivalent presentation. The four
-- factors are the two numerators and the two denominators; only their order
-- changes.
cross-num : (p p' q q' : QProb) → Equiv p p' →
            (num p * den q) * (den p' * den q') ≡
            (num p' * den q') * (den p * den q)
cross-num p p' q q' hp =
  begin
    (num p * den q) * (den p' * den q')
  ≡⟨ *-reorder₄ (num p) (den q) (den p') (den q') ⟩
    (num p * den p') * (den q * den q')
  ≡⟨ cong (_* (den q * den q')) hp ⟩
    (num p' * den p) * (den q * den q')
  ≡⟨ cong ((num p' * den p) *_) (*-comm (den q) (den q')) ⟩
    (num p' * den p) * (den q' * den q)
  ≡⟨ *-reorder₄ (num p') (den p) (den q') (den q) ⟩
    (num p' * den q') * (den p * den q)
  ∎

cross-den : (p p' q q' : QProb) → Equiv q q' →
            (num q * den p) * (den p' * den q') ≡
            (num q' * den p') * (den p * den q)
cross-den p p' q q' hq =
  begin
    (num q * den p) * (den p' * den q')
  ≡⟨ cong ((num q * den p) *_) (*-comm (den p') (den q')) ⟩
    (num q * den p) * (den q' * den p')
  ≡⟨ *-reorder₄ (num q) (den p) (den q') (den p') ⟩
    (num q * den q') * (den p * den p')
  ≡⟨ cong (_* (den p * den p')) hq ⟩
    (num q' * den q) * (den p * den p')
  ≡⟨ cong ((num q' * den q) *_) (*-comm (den p) (den p')) ⟩
    (num q' * den q) * (den p' * den p)
  ≡⟨ *-reorder₄ (num q') (den q) (den p') (den p) ⟩
    (num q' * den p') * (den q * den p)
  ≡⟨ cong ((num q' * den p') *_) (*-comm (den q) (den p)) ⟩
    (num q' * den p') * (den p * den q)
  ∎

-- A positive factor reflects a strict product comparison. The non-strict
-- alternative would make the multiplied comparison non-strict as well.
<-cancel-*-right : ∀ {a b c} → 0 < c → a * c < b * c → a < b
<-cancel-*-right {a} {b} {c} c>0 ac<bc with lt-or-ge a b
... | inl a<b = a<b
... | inr b≤a = ⊥-elim (≰-of-≥ (*-monoˡ b≤a c) ac<bc)

-- Equivalence of both sides preserves the weak order. Each cross-product is
-- rearranged onto the equivalent presentation, then the positive product of
-- the two original denominators is cancelled.
le-congr : ∀ {p p' q q'} → Equiv p p' → Equiv q q' → LE p q → LE p' q'
le-congr {p} {p'} {q} {q'} hp hq pq =
  ≤-cancel-*-right (*-pos (den-pos p) (den-pos q))
    (≤-cong (cross-num p p' q q' hp) (cross-den p p' q q' hq)
            (*-monoˡ pq (den p' * den q')))

-- The same rearrangement preserves a strict comparison.
lt-congr : ∀ {p p' q q'} → Equiv p p' → Equiv q q' → LT p q → LT p' q'
lt-congr {p} {p'} {q} {q'} hp hq pq =
  <-cancel-*-right (*-pos (den-pos p) (den-pos q))
    (<-cong (cross-num p p' q q' hp) (cross-den p p' q q' hq)
            (*-mono-< pq (*-pos (den-pos p') (den-pos q'))))

-- Multiplication swaps the two presentations up to cross-multiplication.
mul-comm : ∀ p q → Equiv (mul p q) (mul q p)
mul-comm p q rewrite *-comm (num p) (num q) | *-comm (den q) (den p) = refl

-- Three presentations associate under multiplication. Both the numerators
-- and the denominators associate, so the cross-products agree.
mul-assoc : ∀ p q r → Equiv (mul (mul p q) r) (mul p (mul q r))
mul-assoc p q r =
  trans (cong (_* Dr) num-assoc) (cong (numR *_) (sym den-assoc))
  where
  numL = (num p * num q) * num r
  numR = num p * (num q * num r)
  denL = (den p * den q) * den r
  denR = den p * (den q * den r)
  Dr = denR
  num-assoc : numL ≡ numR
  num-assoc = *-assoc (num p) (num q) (num r)
  den-assoc : denL ≡ denR
  den-assoc = *-assoc (den p) (den q) (den r)

-- The unit presentation is a right unit for multiplication.
mul-one : ∀ p → Equiv (mul p one) p
mul-one p =
  begin
    (num p * 1) * den p
  ≡⟨ cong (_* den p) (*-idʳ (num p)) ⟩
    num p * den p
  ≡⟨ cong (num p *_) (sym (*-idʳ (den p))) ⟩
    num p * (den p * 1)
  ∎

-- And a left unit, by commuting past the right-unit fact.
one-mul : ∀ p → Equiv (mul one p) p
one-mul p =
  equiv-trans {p = mul one p} {q = mul p one} {r = p}
    (mul-comm one p) (mul-one p)

-- Scaling by a fixed natural number preserves equivalence.
scale-congr : ∀ w {p q} → Equiv p q → Equiv (scale w p) (scale w q)
scale-congr w {p} {q} pq =
  begin
    (w * num p) * den q
  ≡⟨ *-assoc w (num p) (den q) ⟩
    w * (num p * den q)
  ≡⟨ cong (w *_) pq ⟩
    w * (num q * den p)
  ≡⟨ sym (*-assoc w (num q) (den p)) ⟩
    (w * num q) * den p
  ∎

-- Multiplication respects equivalence on each factor. The four-factor
-- rearrangement is the same one used for addition of cleared numerators.
mul-congr : ∀ {p p' q q'} → Equiv p p' → Equiv q q' →
            Equiv (mul p q) (mul p' q')
mul-congr {p} {p'} {q} {q'} hp hq =
  begin
    (num p * num q) * (den p' * den q')
  ≡⟨ *-reorder₄ (num p) (num q) (den p') (den q') ⟩
    (num p * den p') * (num q * den q')
  ≡⟨ cong₂ _*_ hp hq ⟩
    (num p' * den p) * (num q' * den q)
  ≡⟨ sym (*-reorder₄ (num p') (num q') (den p) (den q)) ⟩
    (num p' * num q') * (den p * den q)
  ∎

-- Scaling preserves the cleared-denominator order. The natural factor is
-- multiplied on the left of both numerators.
scale-le-scale : ∀ k {p q} → LE p q → LE (scale k p) (scale k q)
scale-le-scale k {p} {q} pq =
  ≤-cong (sym (*-assoc k (num p) (den q)))
         (sym (*-assoc k (num q) (den p)))
         (*-monoʳ k pq)

-- A natural number as a presentation with denominator one.
ofNat : ℕ → QProb
ofNat n = qprob n 1 (s≤s z≤n)

ofNat-add : ∀ a b → Equiv (add (ofNat a) (ofNat b)) (ofNat (a + b))
ofNat-add a b =
  begin
    (a * 1 + b * 1) * 1
  ≡⟨ cong (_* 1) (cong₂ _+_ (*-idʳ a) (*-idʳ b)) ⟩
    (a + b) * 1
  ≡⟨ *-idʳ (a + b) ⟩
    a + b
  ≡⟨ sym (*-idʳ (a + b)) ⟩
    (a + b) * 1
  ∎

-- Finite sum of presentations. The empty sum is the zero presentation.
listSum : List QProb → QProb
listSum []       = zero
listSum (v ∷ vs) = add v (listSum vs)

-- The zero presentation matches a zero numerator on any positive denominator.
equiv-zero-mk : ∀ D → (hD : 0 < D) → Equiv zero (qprob 0 D hD)
equiv-zero-mk D hD = refl

-- Adding two presentations that already share a denominator adds the
-- numerators and keeps that denominator, up to equivalence.
add-mk-same-den : ∀ D → (hD : 0 < D) → ∀ a b →
                  Equiv (add (qprob a D hD) (qprob b D hD)) (qprob (a + b) D hD)
add-mk-same-den D hD a b =
  begin
    (a * D + b * D) * D
  ≡⟨ cong (_* D) (cong₂ _+_ (*-comm a D) (*-comm b D)) ⟩
    (D * a + D * b) * D
  ≡⟨ cong (_* D) (sym (*-distribˡ-+ D a b)) ⟩
    (D * (a + b)) * D
  ≡⟨ *-assoc D (a + b) D ⟩
    D * ((a + b) * D)
  ≡⟨ cong (D *_) (*-comm (a + b) D) ⟩
    D * (D * (a + b))
  ≡⟨ sym (*-assoc D D (a + b)) ⟩
    (D * D) * (a + b)
  ≡⟨ *-comm (D * D) (a + b) ⟩
    (a + b) * (D * D)
  ∎

-- Pointwise equivalence is preserved by a finite sum. Each summand is
-- replaced where it stands; the summands are not identified as functions.
listSum-map-congr : {X : Set} (xs : List X) (left right : X → QProb) →
                    (∀ x → Equiv (left x) (right x)) →
                    Equiv (listSum (map left xs)) (listSum (map right xs))
listSum-map-congr []       left right _ = equiv-refl zero
listSum-map-congr (x ∷ xs) left right h =
  add-cong {p = left x} {p' = right x}
           {q = listSum (map left xs)} {q' = listSum (map right xs)}
           (h x) (listSum-map-congr xs left right h)

-- A sum over a concatenation is the sum of the two component sums.
listSum-append : ∀ xs ys →
                 Equiv (listSum (xs ++ ys)) (add (listSum xs) (listSum ys))
listSum-append [] ys =
  equiv-sym {p = add zero (listSum ys)} {q = listSum ys}
    (equiv-trans {p = add zero (listSum ys)} {q = add (listSum ys) zero} {r = listSum ys}
      (add-comm zero (listSum ys)) (add-zero (listSum ys)))
listSum-append (v ∷ xs) ys =
  equiv-trans
    {p = add v (listSum (xs ++ ys))}
    {q = add v (add (listSum xs) (listSum ys))}
    {r = add (add v (listSum xs)) (listSum ys)}
    (add-cong {p = v} {p' = v}
              {q = listSum (xs ++ ys)} {q' = add (listSum xs) (listSum ys)}
              (equiv-refl v) (listSum-append xs ys))
    (equiv-sym {p = add (add v (listSum xs)) (listSum ys)}
               {q = add v (add (listSum xs) (listSum ys))}
               (add-assoc v (listSum xs) (listSum ys)))

-- A finite sum of a common denominator is the sum of the numerators on
-- that denominator.
listSum-mk-same-den : ∀ D → (hD : 0 < D) → ∀ ns →
  Equiv (listSum (map (λ n → qprob n D hD) ns)) (qprob (sum ns) D hD)
listSum-mk-same-den D hD []       = equiv-zero-mk D hD
listSum-mk-same-den D hD (n ∷ ns) =
  equiv-trans
    {p = add (qprob n D hD) (listSum (map (λ k → qprob k D hD) ns))}
    {q = add (qprob n D hD) (qprob (sum ns) D hD)}
    {r = qprob (n + sum ns) D hD}
    (add-cong {p = qprob n D hD} {p' = qprob n D hD}
              {q = listSum (map (λ k → qprob k D hD) ns)} {q' = qprob (sum ns) D hD}
              (equiv-refl (qprob n D hD)) (listSum-mk-same-den D hD ns))
    (add-mk-same-den D hD n (sum ns))

-- Flattening a finite family of lists does not change the iterated sum.
listSum-flatMap : {X : Set} (xs : List X) (family : X → List QProb) →
  Equiv (listSum (flatMap family xs))
        (listSum (map (λ x → listSum (family x)) xs))
listSum-flatMap []       family = equiv-refl zero
listSum-flatMap (x ∷ xs) family =
  equiv-trans
    {p = listSum (family x ++ flatMap family xs)}
    {q = add (listSum (family x)) (listSum (flatMap family xs))}
    {r = add (listSum (family x)) (listSum (map (λ y → listSum (family y)) xs))}
    (listSum-append (family x) (flatMap family xs))
    (add-cong {p = listSum (family x)} {p' = listSum (family x)}
              {q = listSum (flatMap family xs)}
              {q' = listSum (map (λ y → listSum (family y)) xs)}
              (equiv-refl (listSum (family x))) (listSum-flatMap xs family))

-- Multiplying by the divisor after division recovers the dividend. The
-- divisor numerator is positive, so the resulting denominator is legal.
mul-div-cancel : ∀ p q → (q>0 : 0 < num q) → Equiv (mul q (div p q q>0)) p
mul-div-cancel p q q>0 = trans from-left (sym from-right)
  where
  pN = num p
  pD = den p
  qN = num q
  qD = den q
  common = (pN * qN) * (pD * qD)
  from-left : (qN * (pN * qD)) * pD ≡ common
  from-left =
    begin
      (qN * (pN * qD)) * pD
    ≡⟨ *-assoc qN (pN * qD) pD ⟩
      qN * ((pN * qD) * pD)
    ≡⟨ cong (qN *_) (*-assoc pN qD pD) ⟩
      qN * (pN * (qD * pD))
    ≡⟨ sym (*-assoc qN pN (qD * pD)) ⟩
      (qN * pN) * (qD * pD)
    ≡⟨ cong₂ _*_ (*-comm qN pN) (*-comm qD pD) ⟩
      (pN * qN) * (pD * qD)
    ∎
  from-right : pN * (qD * (pD * qN)) ≡ common
  from-right =
    begin
      pN * (qD * (pD * qN))
    ≡⟨ sym (*-assoc pN qD (pD * qN)) ⟩
      (pN * qD) * (pD * qN)
    ≡⟨ cong ((pN * qD) *_) (*-comm pD qN) ⟩
      (pN * qD) * (qN * pD)
    ≡⟨ sym (*-assoc (pN * qD) qN pD) ⟩
      ((pN * qD) * qN) * pD
    ≡⟨ cong (_* pD) (*-assoc pN qD qN) ⟩
      (pN * (qD * qN)) * pD
    ≡⟨ cong (_* pD) (cong (pN *_) (*-comm qD qN)) ⟩
      (pN * (qN * qD)) * pD
    ≡⟨ cong (_* pD) (sym (*-assoc pN qN qD)) ⟩
      ((pN * qN) * qD) * pD
    ≡⟨ *-assoc (pN * qN) qD pD ⟩
      (pN * qN) * (qD * pD)
    ≡⟨ cong ((pN * qN) *_) (*-comm qD pD) ⟩
      (pN * qN) * (pD * qD)
    ∎

-- A positive presentation divided by itself is the unit presentation.
div-self : ∀ q → (q>0 : 0 < num q) → Equiv (div q q q>0) one
div-self q q>0 =
  begin
    (num q * den q) * 1
  ≡⟨ *-idʳ (num q * den q) ⟩
    num q * den q
  ≡⟨ *-comm (num q) (den q) ⟩
    den q * num q
  ≡⟨ sym (*-idʳ (den q * num q)) ⟩
    (den q * num q) * 1
  ≡⟨ *-comm (den q * num q) 1 ⟩
    1 * (den q * num q)
  ∎

-- A ratio of ordered presentations does not exceed the unit. The comparison
-- is the given order after the unit denominator is cleared.
div-le-one : ∀ p q → (q>0 : 0 < num q) → LE p q → LE (div p q q>0) one
div-le-one p q q>0 ordered =
  ≤-cong (sym (*-idʳ (num p * den q)))
         (sym (+-idʳ (den p * num q)))
         (≤-cong refl (*-comm (num q) (den p)) ordered)

-- Division respects equivalence of the dividend and of the positive divisor.
div-congr : ∀ {p p' q q'} → Equiv p p' → Equiv q q' →
            (q>0 : 0 < num q) → (q'>0 : 0 < num q') →
            Equiv (div p q q>0) (div p' q' q'>0)
div-congr {p} {p'} {q} {q'} hp hq q>0 q'>0 =
  begin
    (num p * den q) * (den p' * num q')
  ≡⟨ *-reorder₄ (num p) (den q) (den p') (num q') ⟩
    (num p * den p') * (den q * num q')
  ≡⟨ cong (_* (den q * num q')) hp ⟩
    (num p' * den p) * (den q * num q')
  ≡⟨ cong ((num p' * den p) *_) den-cross ⟩
    (num p' * den p) * (den q' * num q)
  ≡⟨ *-reorder₄ (num p') (den p) (den q') (num q) ⟩
    (num p' * den q') * (den p * num q)
  ∎
  where
  den-cross : den q * num q' ≡ den q' * num q
  den-cross =
    begin
      den q * num q'
    ≡⟨ *-comm (den q) (num q') ⟩
      num q' * den q
    ≡⟨ sym hq ⟩
      num q * den q'
    ≡⟨ *-comm (num q) (den q') ⟩
      den q' * num q
    ∎

-- If the cross product of two numerators with the opposite denominators
-- agrees, the two ratios agree. Both divisors have positive numerators.
div-equiv-of-cross : ∀ ln ld rn rd →
  (ld>0 : 0 < num ld) → (rd>0 : 0 < num rd) →
  Equiv (mul ln rd) (mul rn ld) →
  Equiv (div ln ld ld>0) (div rn rd rd>0)
div-equiv-of-cross ln ld rn rd ld>0 rd>0 cross =
  begin
    (num ln * den ld) * (den rn * num rd)
  ≡⟨ cong ((num ln * den ld) *_) (*-comm (den rn) (num rd)) ⟩
    (num ln * den ld) * (num rd * den rn)
  ≡⟨ *-reorder₄ (num ln) (den ld) (num rd) (den rn) ⟩
    (num ln * num rd) * (den ld * den rn)
  ≡⟨ cong ((num ln * num rd) *_) (*-comm (den ld) (den rn)) ⟩
    (num ln * num rd) * (den rn * den ld)
  ≡⟨ cross ⟩
    (num rn * num ld) * (den ln * den rd)
  ≡⟨ cong ((num rn * num ld) *_) (*-comm (den ln) (den rd)) ⟩
    (num rn * num ld) * (den rd * den ln)
  ≡⟨ *-reorder₄ (num rn) (num ld) (den rd) (den ln) ⟩
    (num rn * den rd) * (num ld * den ln)
  ≡⟨ cong ((num rn * den rd) *_) (*-comm (num ld) (den ln)) ⟩
    (num rn * den rd) * (den ln * num ld)
  ∎

-- Dividing by a presentation equivalent to the unit does not change the
-- dividend. The divisor's numerator and denominator are the same number.
div-by-unit : ∀ n d → (d>0 : 0 < num d) → Equiv d one →
              Equiv (div n d d>0) n
div-by-unit n d d>0 normalized =
  begin
    (num n * den d) * den n
  ≡⟨ cong (λ k → (num n * k) * den n) parts ⟩
    (num n * num d) * den n
  ≡⟨ *-reorder₃ (num n) (num d) (den n) ⟩
    (num n * den n) * num d
  ≡⟨ *-assoc (num n) (den n) (num d) ⟩
    num n * (den n * num d)
  ∎
  where
  parts : den d ≡ num d
  parts =
    begin
      den d
    ≡⟨ sym (*-idʳ (den d)) ⟩
      den d * 1
    ≡⟨ *-comm (den d) 1 ⟩
      1 * den d
    ≡⟨ sym normalized ⟩
      num d * 1
    ≡⟨ *-idʳ (num d) ⟩
      num d
    ∎

-- Scaling a presentation by N yields the unit only when the presentation is
-- the reciprocal of N.
scale-forced-unit : ∀ {N} → (hN : 0 < N) → (cell : QProb) →
                    Equiv (scale N cell) one →
                    Equiv cell (qprob 1 N hN)
scale-forced-unit {N} hN cell hwhole =
  begin
    num cell * N
  ≡⟨ *-comm (num cell) N ⟩
    N * num cell
  ≡⟨ sym (*-idʳ (N * num cell)) ⟩
    (N * num cell) * 1
  ≡⟨ hwhole ⟩
    1 * den cell
  ∎

-- The same unit equation scales to the ratio k / N.
scale-forced-ratio : ∀ {N k} → (hN : 0 < N) → (cell : QProb) →
                     Equiv (scale N cell) one →
                     Equiv (scale k cell) (qprob k N hN)
scale-forced-ratio {N} {k} hN cell hwhole =
  begin
    (k * num cell) * N
  ≡⟨ *-assoc k (num cell) N ⟩
    k * (num cell * N)
  ≡⟨ cong (k *_) (*-comm (num cell) N) ⟩
    k * (N * num cell)
  ≡⟨ cong (k *_) (trans (sym (*-idʳ (N * num cell))) hwhole) ⟩
    k * (1 * den cell)
  ≡⟨ cong (k *_) (+-idʳ (den cell)) ⟩
    k * den cell
  ∎

-- Difference of presentations, defined only when the subtrahend does not
-- exceed the minuend. The numerator is a natural difference of cleared
-- products, so no signed value is introduced. The inequality stays with the
-- caller: this is an inverse of addition only up to equivalence.
sub : (p q : QProb) → LE q p → QProb
sub p q q≤p =
  qprob (num p * den q - num q * den p)
        (den p * den q)
        (*-pos (den-pos p) (den-pos q))

-- Adding back the subtracted presentation recovers the original magnitude.
restore-sub : ∀ p q → (q≤p : LE q p) → Equiv (add (sub p q q≤p) q) p
restore-sub p q q≤p = trans (cong (_* den p) summed) tail
  where
  m = num p * den q
  s = num q * den p
  summed : (m - s) * den q + num q * (den p * den q) ≡ m * den q
  summed =
    begin
      (m - s) * den q + num q * (den p * den q)
    ≡⟨ cong (_+ num q * (den p * den q))
         (*-sub-distribʳ {m = m} {n = s} (den q) q≤p) ⟩
      (m * den q - s * den q) + num q * (den p * den q)
    ≡⟨ cong (λ k → (m * den q - s * den q) + k)
         (sym (*-assoc (num q) (den p) (den q))) ⟩
      (m * den q - s * den q) + s * den q
    ≡⟨ sub-add (*-monoˡ q≤p (den q)) ⟩
      m * den q
    ∎
  tail : (m * den q) * den p ≡ num p * ((den p * den q) * den q)
  tail =
    begin
      (m * den q) * den p
    ≡⟨ cong (_* den p) (*-assoc (num p) (den q) (den q)) ⟩
      (num p * (den q * den q)) * den p
    ≡⟨ *-assoc (num p) (den q * den q) (den p) ⟩
      num p * ((den q * den q) * den p)
    ≡⟨ cong (num p *_) (*-comm (den q * den q) (den p)) ⟩
      num p * (den p * (den q * den q))
    ≡⟨ cong (num p *_) (sym (*-assoc (den p) (den q) (den q))) ⟩
      num p * ((den p * den q) * den q)
    ∎

-- Equivalent minuends and subtrahends give equivalent differences. Both
-- inequalities are required so each natural subtraction is the witnessed one.
sub-congr : ∀ {p p' q q'} → Equiv p p' → Equiv q q' →
            (q≤p : LE q p) → (q'≤p' : LE q' p') →
            Equiv (sub p q q≤p) (sub p' q' q'≤p')
sub-congr {p} {p'} {q} {q'} hp hq q≤p q'≤p' =
  begin
    (num p * den q - num q * den p) * (den p' * den q')
  ≡⟨ *-sub-distribʳ {m = num p * den q} {n = num q * den p}
       (den p' * den q') q≤p ⟩
    num p * den q * (den p' * den q') - num q * den p * (den p' * den q')
  ≡⟨ cong₂ _-_ (cross-num p p' q q' hp) (cross-den p p' q q' hq) ⟩
    num p' * den q' * (den p * den q) - num q' * den p' * (den p * den q)
  ≡⟨ sym (*-sub-distribʳ {m = num p' * den q'} {n = num q' * den p'}
       (den p * den q) q'≤p') ⟩
    (num p' * den q' - num q' * den p') * (den p * den q)
  ∎
