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
