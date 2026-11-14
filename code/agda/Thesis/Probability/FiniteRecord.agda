module Thesis.Probability.FiniteRecord where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
open import Thesis.Probability.Core
open import Thesis.Probability.QProb using (QProb; qprob; one; LE; zero-le; ≤-cong)

-- A finite probability record is a list of weighted outcomes sharing one
-- positive denominator. Labels may repeat, and a weight may be zero: the
-- mass of an event is the sum of the weights whose labels the event accepts.
-- The resulting probability is that mass over the common denominator, so
-- equivalent events are compared by cross-multiplication.

totalMass : {Ω : Set} → List (Ω × ℕ) → ℕ
totalMass []              = 0
totalMass ((_ , w) ∷ xs)  = w + totalMass xs

eventMass : {Ω : Set} → List (Ω × ℕ) → Event Ω → ℕ
eventMass []             _ = 0
eventMass ((ω , w) ∷ xs) E =
  if E ω then w + eventMass xs E else eventMass xs E

-- Events that agree at every label collect the same mass. Only the value at
-- each listed label is used.
eventMass-cong : {Ω : Set} (atoms : List (Ω × ℕ)) (E F : Event Ω) →
                 (∀ value → E value ≡ F value) →
                 eventMass atoms E ≡ eventMass atoms F
eventMass-cong []             E F _ = refl
eventMass-cong ((ω , w) ∷ xs) E F h rewrite h ω | eventMass-cong xs E F h = refl

-- The mass of a two-atom list is the sum of the weights the event accepts.
eventMass-pair : {Ω : Set} (x y : Ω) (wx wy : ℕ) (E : Event Ω) →
  eventMass ((x , wx) ∷ (y , wy) ∷ []) E ≡
  (if E x then wx else 0) + (if E y then wy else 0)
eventMass-pair x y wx wy E with E x | E y
... | true  | true  = cong (wx +_) (+-idʳ wy)
... | true  | false = refl
... | false | true  = trans (+-idʳ wy) (sym (+-idˡ wy))
  where
  +-idˡ : ∀ n → 0 + n ≡ n
  +-idˡ n = refl
... | false | false = refl

-- Accepting more labels cannot decrease the collected mass.
eventMass-mono : {Ω : Set} (atoms : List (Ω × ℕ)) (E F : Event Ω) →
                 (∀ value → E value ≡ true → F value ≡ true) →
                 eventMass atoms E ≤ eventMass atoms F
eventMass-mono []             E F _ = ≤-refl 0
eventMass-mono ((ω , w) ∷ xs) E F h with E ω in eE | F ω in eF
... | false | false = eventMass-mono xs E F h
... | false | true  =
  ≤-trans (eventMass-mono xs E F h) (≤-+ˡ w (eventMass xs F))
... | true  | true  = +-monoʳ w (eventMass-mono xs E F h)
... | true  | false = ⊥-elim (false≢true (trans (sym eF) (h ω eE)))

-- The total event collects every weight.
eventMass-top : {Ω : Set} (atoms : List (Ω × ℕ)) →
                eventMass atoms topEvent ≡ totalMass atoms
eventMass-top []             = refl
eventMass-top ((_ , _) ∷ xs) rewrite eventMass-top xs = refl

-- Move the middle summand to the front.
+-move : ∀ a b c → a + (b + c) ≡ b + (a + c)
+-move a b c =
  begin
    a + (b + c)
  ≡⟨ sym (+-assoc a b c) ⟩
    (a + b) + c
  ≡⟨ cong (_+ c) (+-comm a b) ⟩
    (b + a) + c
  ≡⟨ +-assoc b a c ⟩
    b + (a + c)
  ∎

-- An event and its complement partition the whole mass. Repeated labels and
-- zero weights are allowed.
eventMass-add-complement : {Ω : Set} (atoms : List (Ω × ℕ)) (E : Event Ω) →
  eventMass atoms E + eventMass atoms (λ value → not (E value)) ≡ totalMass atoms
eventMass-add-complement []             E = refl
eventMass-add-complement ((ω , w) ∷ xs) E with E ω
... | true =
  begin
    (w + eventMass xs E) + eventMass xs (λ value → not (E value))
  ≡⟨ +-assoc w (eventMass xs E) (eventMass xs (λ value → not (E value))) ⟩
    w + (eventMass xs E + eventMass xs (λ value → not (E value)))
  ≡⟨ cong (w +_) (eventMass-add-complement xs E) ⟩
    w + totalMass xs
  ∎
... | false =
  begin
    eventMass xs E + (w + eventMass xs (λ value → not (E value)))
  ≡⟨ +-move (eventMass xs E) w (eventMass xs (λ value → not (E value))) ⟩
    w + (eventMass xs E + eventMass xs (λ value → not (E value)))
  ≡⟨ cong (w +_) (eventMass-add-complement xs E) ⟩
    w + totalMass xs
  ∎

-- An event cannot carry more mass than the complete list.
eventMass-≤-total : {Ω : Set} (atoms : List (Ω × ℕ)) (E : Event Ω) →
                    eventMass atoms E ≤ totalMass atoms
eventMass-≤-total []             E = ≤-refl 0
eventMass-≤-total ((ω , w) ∷ xs) E with E ω
... | false = ≤-trans (eventMass-≤-total xs E) (≤-+ˡ w (totalMass xs))
... | true  = +-monoʳ w (eventMass-≤-total xs E)

-- The constantly false event collects no mass.
eventMass-false : {Ω : Set} (atoms : List (Ω × ℕ)) →
                  eventMass atoms (λ _ → false) ≡ 0
eventMass-false []             = refl
eventMass-false ((_ , _) ∷ xs) rewrite eventMass-false xs = refl

-- A finite rational probability record in common-denominator form.
-- The atom list may repeat labels. Its weights sum to the positive
-- denominator, so every event probability lies in the unit interval.
record FiniteProbRecord (Ω : Set) : Set where
  constructor finiteRecord
  field
    atoms   : List (Ω × ℕ)
    den     : ℕ
    den-pos : 0 < den
    total   : totalMass atoms ≡ den

open FiniteProbRecord

-- The probability of an event is its collected mass over the common
-- denominator. No reduced representative is chosen.
probVal : {Ω : Set} → FiniteProbRecord Ω → Event Ω → QProb
probVal R E = qprob (eventMass (atoms R) E) (den R) (den-pos R)

-- Every such probability is at least zero.
probVal-nonneg : {Ω : Set} (R : FiniteProbRecord Ω) (E : Event Ω) →
                 LE Thesis.Probability.QProb.zero (probVal R E)
probVal-nonneg R E = zero-le (probVal R E)

-- And at most one, because the event cannot outweigh the whole record.
probVal-≤-one : {Ω : Set} (R : FiniteProbRecord Ω) (E : Event Ω) →
                LE (probVal R E) one
probVal-≤-one R E =
  ≤-cong (sym (*-idʳ mass)) (sym (+-idʳ (den R))) bounded
  where
  mass = eventMass (atoms R) E
  bounded : mass ≤ den R
  bounded = subst (λ n → mass ≤ n) (total R) (eventMass-≤-total (atoms R) E)

probVal-bounds : {Ω : Set} (R : FiniteProbRecord Ω) (E : Event Ω) →
                 LE Thesis.Probability.QProb.zero (probVal R E) × LE (probVal R E) one
probVal-bounds R E = probVal-nonneg R E , probVal-≤-one R E

-- Events that agree at every outcome have equivalent probabilities.
-- The agreement is pointwise; the two events are not identified.
probVal-cong : {Ω : Set} (R : FiniteProbRecord Ω) (E F : Event Ω) →
               (∀ value → E value ≡ F value) →
               Thesis.Probability.QProb.Equiv (probVal R E) (probVal R F)
probVal-cong R E F h =
  cong (λ m → m * den R) (eventMass-cong (atoms R) E F h)

-- The empty event has probability zero.
-- The empty event has probability zero. Once its mass is zero, both
-- cross-products against the unit-denominator zero presentation vanish.
probVal-false : {Ω : Set} (R : FiniteProbRecord Ω) →
                Thesis.Probability.QProb.Equiv (probVal R (λ _ → false))
                  Thesis.Probability.QProb.zero
probVal-false R rewrite eventMass-false (atoms R) = refl
