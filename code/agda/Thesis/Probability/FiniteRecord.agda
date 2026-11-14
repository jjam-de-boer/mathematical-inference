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

-- Add a weight only when the label is accepted. The Boolean is an argument,
-- so case analysis on it computes.
add-if : Bool → ℕ → ℕ → ℕ
add-if true  w m = w + m
add-if false _ m = m

eventMass : {Ω : Set} → List (Ω × ℕ) → Event Ω → ℕ
eventMass []             _ = 0
eventMass ((ω , w) ∷ xs) E = add-if (E ω) w (eventMass xs E)

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

-- The empty event has probability zero. Once its mass is zero, both
-- cross-products against the unit-denominator zero presentation vanish.
probVal-false : {Ω : Set} (R : FiniteProbRecord Ω) →
                Thesis.Probability.QProb.Equiv (probVal R (λ _ → false))
                  Thesis.Probability.QProb.zero
probVal-false R rewrite eventMass-false (atoms R) = refl

-- On a disjoint pair, the union mass is the sum of the masses. A label
-- cannot contribute its weight to both events.
eventMass-union-disjoint : {Ω : Set} (atoms : List (Ω × ℕ)) (E F : Event Ω) →
  disjoint E F →
  eventMass atoms (union E F) ≡ eventMass atoms E + eventMass atoms F
eventMass-union-disjoint []             E F _ = refl
eventMass-union-disjoint ((ω , w) ∷ xs) E F disj with E ω in eE | F ω in eF
... | false | false rewrite eventMass-union-disjoint xs E F disj = refl
... | false | true  =
  begin
    w + eventMass xs (union E F)
  ≡⟨ cong (w +_) (eventMass-union-disjoint xs E F disj) ⟩
    w + (eventMass xs E + eventMass xs F)
  ≡⟨ sym (+-move (eventMass xs E) w (eventMass xs F)) ⟩
    eventMass xs E + (w + eventMass xs F)
  ∎
... | true  | false =
  begin
    w + eventMass xs (union E F)
  ≡⟨ cong (w +_) (eventMass-union-disjoint xs E F disj) ⟩
    w + (eventMass xs E + eventMass xs F)
  ≡⟨ sym (+-assoc w (eventMass xs E) (eventMass xs F)) ⟩
    (w + eventMass xs E) + eventMass xs F
  ∎
... | true  | true  = ⊥-elim (disj ω eE eF)

-- Disjoint events add as probabilities. The common denominator is squared
-- on both sides of the cross-multiplication, so it cancels in the comparison.
probVal-union-disjoint : {Ω : Set} (R : FiniteProbRecord Ω) (E F : Event Ω) →
  disjoint E F →
  Thesis.Probability.QProb.Equiv (probVal R (union E F))
    (Thesis.Probability.QProb.add (probVal R E) (probVal R F))
probVal-union-disjoint R E F disj =
  begin
    massU * (den R * den R)
  ≡⟨ cong (_* (den R * den R)) massEq ⟩
    (massE + massF) * (den R * den R)
  ≡⟨ sym (*-assoc (massE + massF) (den R) (den R)) ⟩
    ((massE + massF) * den R) * den R
  ≡⟨ cong (_* den R) (*-distribʳ-+ massE massF (den R)) ⟩
    (massE * den R + massF * den R) * den R
  ∎
  where
  massU = eventMass (atoms R) (union E F)
  massE = eventMass (atoms R) E
  massF = eventMass (atoms R) F
  massEq = eventMass-union-disjoint (atoms R) E F disj

-- The total event has probability one, because its mass is the denominator.
normalization : {Ω : Set} (R : FiniteProbRecord Ω) →
                Thesis.Probability.QProb.Equiv (probVal R topEvent) one
normalization R =
  begin
    eventMass (atoms R) topEvent * 1
  ≡⟨ cong (_* 1) (eventMass-top (atoms R)) ⟩
    totalMass (atoms R) * 1
  ≡⟨ cong (_* 1) (total R) ⟩
    den R * 1
  ≡⟨ *-idʳ (den R) ⟩
    den R
  ≡⟨ sym (+-idʳ (den R)) ⟩
    1 * den R
  ∎

-- Keep the atoms whose labels satisfy a test. Their total weight is the
-- event mass of that test.
keeps : {Ω : Set} → Event Ω → Ω × ℕ → Bool
keeps evidence (ω , _) = evidence ω

totalMass-filter : {Ω : Set} (atoms : List (Ω × ℕ)) (evidence : Event Ω) →
  totalMass (filter (keeps evidence) atoms) ≡ eventMass atoms evidence
totalMass-filter []             evidence = refl
totalMass-filter ((ω , w) ∷ xs) evidence with evidence ω
... | true  =
  begin
    w + totalMass (filter (keeps evidence) xs)
  ≡⟨ cong (w +_) (totalMass-filter xs evidence) ⟩
    w + eventMass xs evidence
  ∎
... | false = totalMass-filter xs evidence

-- Filtering by evidence and then by an event is the mass of the conjunction.
eventMass-filter : {Ω : Set} (atoms : List (Ω × ℕ)) (evidence event : Event Ω) →
  eventMass (filter (keeps evidence) atoms) event ≡
  eventMass atoms (λ ω → evidence ω ∧ event ω)
eventMass-filter []             evidence event = refl
eventMass-filter ((ω , w) ∷ xs) evidence event with evidence ω | event ω in eqE
... | true  | true  =
  begin
    add-if (event ω) w (eventMass (filter (keeps evidence) xs) event)
  ≡⟨ cong (λ b → add-if b w (eventMass (filter (keeps evidence) xs) event)) eqE ⟩
    w + eventMass (filter (keeps evidence) xs) event
  ≡⟨ cong (w +_) (eventMass-filter xs evidence event) ⟩
    w + eventMass xs (λ ω₁ → evidence ω₁ ∧ event ω₁)
  ∎
... | true  | false =
  begin
    add-if (event ω) w (eventMass (filter (keeps evidence) xs) event)
  ≡⟨ cong (λ b → add-if b w (eventMass (filter (keeps evidence) xs) event)) eqE ⟩
    eventMass (filter (keeps evidence) xs) event
  ≡⟨ eventMass-filter xs evidence event ⟩
    eventMass xs (λ ω₁ → evidence ω₁ ∧ event ω₁)
  ∎
... | false | true  = eventMass-filter xs evidence event
... | false | false = eventMass-filter xs evidence event

-- An event is positive when its collected mass is a positive natural number.
-- Conditioning is defined only for such events, so the new denominator is
-- never zero.
EventPositive : {Ω : Set} → FiniteProbRecord Ω → Event Ω → Set
EventPositive R event = 0 < eventMass (atoms R) event

-- Restrict the record to the atoms accepted by the evidence. The new
-- denominator is the evidence mass, and the discarded atoms are absent
-- rather than given weight zero.
conditionOn : {Ω : Set} (R : FiniteProbRecord Ω) (evidence : Event Ω) →
              EventPositive R evidence → FiniteProbRecord Ω
conditionOn R evidence positive = finiteRecord
  (filter (keeps evidence) (atoms R))
  (eventMass (atoms R) evidence)
  positive
  (totalMass-filter (atoms R) evidence)

-- The conditional probability of an event is the joint mass divided by the
-- evidence mass. The original denominator cancels.
conditionOn-probVal : {Ω : Set} (R : FiniteProbRecord Ω)
  (evidence event : Event Ω) (positive : EventPositive R evidence) →
  Thesis.Probability.QProb.Equiv
    (probVal (conditionOn R evidence positive) event)
    (Thesis.Probability.QProb.div
      (probVal R (λ ω → evidence ω ∧ event ω))
      (probVal R evidence) positive)
conditionOn-probVal R evidence event positive =
  begin
    eventMass filtered event * (den R * evidenceMass)
  ≡⟨ cong (_* (den R * evidenceMass)) filteredEq ⟩
    jointMass * (den R * evidenceMass)
  ≡⟨ sym (*-assoc jointMass (den R) evidenceMass) ⟩
    (jointMass * den R) * evidenceMass
  ∎
  where
  filtered = filter (keeps evidence) (atoms R)
  evidenceMass = eventMass (atoms R) evidence
  jointMass = eventMass (atoms R) (λ ω → evidence ω ∧ event ω)
  filteredEq = eventMass-filter (atoms R) evidence event

-- Bayes' formula. Both positivity witnesses are kept, because each
-- conditional probability and the final division need a positive mass.
bayes : {Ω : Set} (R : FiniteProbRecord Ω) (E F : Event Ω) →
        (hE : EventPositive R E) (hF : EventPositive R F) →
        Thesis.Probability.QProb.Equiv
          (probVal (conditionOn R F hF) E)
          (Thesis.Probability.QProb.div
            (Thesis.Probability.QProb.mul
              (probVal (conditionOn R E hE) F)
              (probVal R E))
            (probVal R F) hF)
bayes R E F hE hF =
  equiv-trans
    {p = probVal (conditionOn R F hF) E}
    {q = Thesis.Probability.QProb.div (probVal R (λ ω → F ω ∧ E ω)) (probVal R F) hF}
    {r = Thesis.Probability.QProb.div
           (Thesis.Probability.QProb.mul (probVal (conditionOn R E hE) F) (probVal R E))
           (probVal R F) hF}
    (conditionOn-probVal R F E hF)
    (div-congr
      {p = probVal R (λ ω → F ω ∧ E ω)}
      {p' = Thesis.Probability.QProb.mul (probVal (conditionOn R E hE) F) (probVal R E)}
      {q = probVal R F} {q' = probVal R F}
      joint-as-product
      (Thesis.Probability.QProb.equiv-refl (probVal R F))
      hF hF)
  where
  open import Thesis.Probability.QProb using
    (equiv-trans; equiv-sym; div-congr; equiv-refl; mul-comm; mul-div-cancel; mul-congr)
  joint = probVal R (λ ω → E ω ∧ F ω)
  condF = probVal (conditionOn R E hE) F
  joint-as-product :
    Thesis.Probability.QProb.Equiv
      (probVal R (λ ω → F ω ∧ E ω))
      (Thesis.Probability.QProb.mul condF (probVal R E))
  joint-as-product =
    equiv-trans
      {p = probVal R (λ ω → F ω ∧ E ω)}
      {q = joint}
      {r = Thesis.Probability.QProb.mul condF (probVal R E)}
      (probVal-cong R (λ ω → F ω ∧ E ω) (λ ω → E ω ∧ F ω) (λ ω → ∧-comm (F ω) (E ω)))
      (equiv-trans
        {p = joint}
        {q = Thesis.Probability.QProb.mul (probVal R E)
               (Thesis.Probability.QProb.div joint (probVal R E) hE)}
        {r = Thesis.Probability.QProb.mul condF (probVal R E)}
        (equiv-sym
          {p = Thesis.Probability.QProb.mul (probVal R E)
                 (Thesis.Probability.QProb.div joint (probVal R E) hE)}
          {q = joint}
          (mul-div-cancel joint (probVal R E) hE))
        (equiv-trans
          {p = Thesis.Probability.QProb.mul (probVal R E)
                 (Thesis.Probability.QProb.div joint (probVal R E) hE)}
          {q = Thesis.Probability.QProb.mul (probVal R E) condF}
          {r = Thesis.Probability.QProb.mul condF (probVal R E)}
          (mul-congr
            {p = probVal R E} {p' = probVal R E}
            {q = Thesis.Probability.QProb.div joint (probVal R E) hE}
            {q' = condF}
            (equiv-refl (probVal R E))
            (equiv-sym {p = condF}
              {q = Thesis.Probability.QProb.div joint (probVal R E) hE}
              (conditionOn-probVal R E F hE)))
          (mul-comm (probVal R E) condF)))
