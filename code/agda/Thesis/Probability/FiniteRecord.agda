module Thesis.Probability.FiniteRecord where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
open import Thesis.Probability.Core
import Thesis.Probability.Urn as Urn
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

open import Thesis.Probability.QProb using
  (Equiv; equiv-refl; equiv-sym; equiv-trans; mul; mul-congr; one-mul;
   add; add-cong; listSum; listSum-map-congr)

-- Conditioning does not change the certain event. The retained atoms still
-- exhaust the new denominator.
conditionOn-normalization : {Ω : Set} (R : FiniteProbRecord Ω)
  (evidence : Event Ω) (positive : EventPositive R evidence) →
  Equiv (probVal (conditionOn R evidence positive) topEvent) one
conditionOn-normalization R evidence positive =
  normalization (conditionOn R evidence positive)

-- Rename labels. Weights are kept, so the common denominator is unchanged.
relabel : {Ω X : Set} → (Ω → X) → Ω × ℕ → X × ℕ
relabel f (ω , w) = f ω , w

totalMass-map-labels : {Ω X : Set} (atoms : List (Ω × ℕ)) (f : Ω → X) →
  totalMass (map (relabel f) atoms) ≡ totalMass atoms
totalMass-map-labels []             f = refl
totalMass-map-labels ((_ , _) ∷ xs) f rewrite totalMass-map-labels xs f = refl

eventMass-map-labels : {Ω X : Set} (atoms : List (Ω × ℕ))
  (f : Ω → X) (event : Event X) →
  eventMass (map (relabel f) atoms) event ≡
  eventMass atoms (λ ω → event (f ω))
eventMass-map-labels []             f event = refl
eventMass-map-labels ((ω , w) ∷ xs) f event with event (f ω)
... | true  rewrite eventMass-map-labels xs f event = refl
... | false = eventMass-map-labels xs f event

-- Scaling every weight by the same factor scales every event mass by it.
eventMass-scale : {Ω : Set} (atoms : List (Ω × ℕ)) (factor : ℕ)
  (event : Event Ω) →
  eventMass (map (λ (ω , w) → (ω , factor * w)) atoms) event ≡
  factor * eventMass atoms event
eventMass-scale []             factor event = sym (*-zeroʳ factor)
eventMass-scale ((ω , w) ∷ xs) factor event with event ω
... | true =
  begin
    factor * w + eventMass (map (λ (ω₁ , w₁) → (ω₁ , factor * w₁)) xs) event
  ≡⟨ cong (factor * w +_) (eventMass-scale xs factor event) ⟩
    factor * w + factor * eventMass xs event
  ≡⟨ sym (*-distribˡ-+ factor w (eventMass xs event)) ⟩
    factor * (w + eventMass xs event)
  ∎
... | false = eventMass-scale xs factor event

-- The same scaling after a simultaneous relabelling.
totalMass-map-weight : {Ω X : Set} (atoms : List (Ω × ℕ))
  (label : Ω → X) (factor : ℕ) →
  totalMass (map (λ (ω , w) → (label ω , factor * w)) atoms) ≡
  factor * totalMass atoms
totalMass-map-weight []             label factor = sym (*-zeroʳ factor)
totalMass-map-weight ((ω , w) ∷ xs) label factor =
  begin
    factor * w + totalMass (map (λ (ω₁ , w₁) → (label ω₁ , factor * w₁)) xs)
  ≡⟨ cong (factor * w +_) (totalMass-map-weight xs label factor) ⟩
    factor * w + factor * totalMass xs
  ≡⟨ sym (*-distribˡ-+ factor w (totalMass xs)) ⟩
    factor * (w + totalMass xs)
  ∎

eventMass-map-weight : {Ω X : Set} (atoms : List (Ω × ℕ))
  (label : Ω → X) (factor : ℕ) (event : Event X) →
  eventMass (map (λ (ω , w) → (label ω , factor * w)) atoms) event ≡
  factor * eventMass atoms (λ ω → event (label ω))
eventMass-map-weight []             label factor event = sym (*-zeroʳ factor)
eventMass-map-weight ((ω , w) ∷ xs) label factor event with event (label ω)
... | true =
  begin
    factor * w +
      eventMass (map (λ (ω₁ , w₁) → (label ω₁ , factor * w₁)) xs) event
  ≡⟨ cong (factor * w +_) (eventMass-map-weight xs label factor event) ⟩
    factor * w + factor * eventMass xs (λ ω₁ → event (label ω₁))
  ≡⟨ sym (*-distribˡ-+ factor w (eventMass xs (λ ω₁ → event (label ω₁)))) ⟩
    factor * (w + eventMass xs (λ ω₁ → event (label ω₁)))
  ∎
... | false = eventMass-map-weight xs label factor event

totalMass-append : {Ω : Set} (left right : List (Ω × ℕ)) →
  totalMass (left ++ right) ≡ totalMass left + totalMass right
totalMass-append []             right = refl
totalMass-append ((ω , w) ∷ xs) right =
  begin
    w + totalMass (xs ++ right)
  ≡⟨ cong (w +_) (totalMass-append xs right) ⟩
    w + (totalMass xs + totalMass right)
  ≡⟨ sym (+-assoc w (totalMass xs) (totalMass right)) ⟩
    (w + totalMass xs) + totalMass right
  ∎

eventMass-append : {Ω : Set} (left right : List (Ω × ℕ)) (event : Event Ω) →
  eventMass (left ++ right) event ≡
  eventMass left event + eventMass right event
eventMass-append []             right event = refl
eventMass-append ((ω , w) ∷ xs) right event with event ω
... | true =
  begin
    w + eventMass (xs ++ right) event
  ≡⟨ cong (w +_) (eventMass-append xs right event) ⟩
    w + (eventMass xs event + eventMass right event)
  ≡⟨ sym (+-assoc w (eventMass xs event) (eventMass right event)) ⟩
    (w + eventMass xs event) + eventMass right event
  ∎
... | false = eventMass-append xs right event

-- Independent combination of two weighted lists. Each pair of atoms is kept,
-- and its weight is the product of the two weights, so the masses multiply.
weightedCartesian : {Ω X : Set} → List (Ω × ℕ) → List (X × ℕ) →
                    List ((Ω × X) × ℕ)
weightedCartesian left right =
  flatMap (λ (ω , w) → map (λ (x , v) → ((ω , x) , w * v)) right) left

totalMass-weightedCartesian : {Ω X : Set}
  (left : List (Ω × ℕ)) (right : List (X × ℕ)) →
  totalMass (weightedCartesian left right) ≡ totalMass left * totalMass right
totalMass-weightedCartesian []             right = refl
totalMass-weightedCartesian ((ω , w) ∷ xs) right =
  begin
    totalMass (row ++ weightedCartesian xs right)
  ≡⟨ totalMass-append row (weightedCartesian xs right) ⟩
    totalMass row + totalMass (weightedCartesian xs right)
  ≡⟨ cong₂ _+_ (totalMass-map-weight right (λ x → (ω , x)) w)
               (totalMass-weightedCartesian xs right) ⟩
    w * totalMass right + totalMass xs * totalMass right
  ≡⟨ sym (*-distribʳ-+ w (totalMass xs) (totalMass right)) ⟩
    (w + totalMass xs) * totalMass right
  ∎
  where
  row = map (λ (x , v) → ((ω , x) , w * v)) right

eventMass-weightedCartesian : {Ω X : Set}
  (left : List (Ω × ℕ)) (right : List (X × ℕ))
  (leftEvent : Event Ω) (rightEvent : Event X) →
  eventMass (weightedCartesian left right)
    (λ pair → leftEvent (fst pair) ∧ rightEvent (snd pair)) ≡
  eventMass left leftEvent * eventMass right rightEvent
eventMass-weightedCartesian []             right leftEvent rightEvent = refl
eventMass-weightedCartesian ((ω , w) ∷ xs) right leftEvent rightEvent
  with leftEvent ω in eq
... | true =
  begin
    eventMass (row ++ rest) rectangle
  ≡⟨ eventMass-append row rest rectangle ⟩
    eventMass row rectangle + eventMass rest rectangle
  ≡⟨ cong₂ _+_
       (eventMass-map-weight right (λ x → (ω , x)) w rectangle)
       (eventMass-weightedCartesian xs right leftEvent rightEvent) ⟩
    w * eventMass right (λ x → leftEvent ω ∧ rightEvent x) +
      eventMass xs leftEvent * eventMass right rightEvent
  ≡⟨ cong (_+ eventMass xs leftEvent * eventMass right rightEvent)
       (cong (w *_)
         (eventMass-cong right _ rightEvent
           (λ x → cong (λ b → b ∧ rightEvent x) eq))) ⟩
    w * eventMass right rightEvent +
      eventMass xs leftEvent * eventMass right rightEvent
  ≡⟨ sym (*-distribʳ-+ w (eventMass xs leftEvent) (eventMass right rightEvent)) ⟩
    (w + eventMass xs leftEvent) * eventMass right rightEvent
  ∎
  where
  row = map (λ (x , v) → ((ω , x) , w * v)) right
  rest = weightedCartesian xs right
  rectangle = λ pair → leftEvent (fst pair) ∧ rightEvent (snd pair)
... | false =
  begin
    eventMass (row ++ rest) rectangle
  ≡⟨ eventMass-append row rest rectangle ⟩
    eventMass row rectangle + eventMass rest rectangle
  ≡⟨ cong₂ _+_
       (eventMass-map-weight right (λ x → (ω , x)) w rectangle)
       (eventMass-weightedCartesian xs right leftEvent rightEvent) ⟩
    w * eventMass right (λ x → leftEvent ω ∧ rightEvent x) +
      eventMass xs leftEvent * eventMass right rightEvent
  ≡⟨ cong (λ m → w * m + eventMass xs leftEvent * eventMass right rightEvent)
       (trans (eventMass-cong right _ (λ _ → false)
                 (λ x → cong (λ b → b ∧ rightEvent x) eq))
              (eventMass-false right)) ⟩
    w * 0 + eventMass xs leftEvent * eventMass right rightEvent
  ≡⟨ cong (_+ eventMass xs leftEvent * eventMass right rightEvent) (*-zeroʳ w) ⟩
    eventMass xs leftEvent * eventMass right rightEvent
  ∎
  where
  row = map (λ (x , v) → ((ω , x) , w * v)) right
  rest = weightedCartesian xs right
  rectangle = λ pair → leftEvent (fst pair) ∧ rightEvent (snd pair)

-- Expand a joint event along the left factor. Each left atom contributes its
-- weight times the mass of the right-hand slice it determines.
eventMass-weightedCartesian-bind : {Ω X : Set}
  (left : List (Ω × ℕ)) (right : List (X × ℕ)) (event : Event (Ω × X)) →
  eventMass (weightedCartesian left right) event ≡
  sum (map (λ (ω , w) → w * eventMass right (λ x → event (ω , x))) left)
eventMass-weightedCartesian-bind []             right event = refl
eventMass-weightedCartesian-bind ((ω , w) ∷ xs) right event =
  begin
    eventMass (row ++ rest) event
  ≡⟨ eventMass-append row rest event ⟩
    eventMass row event + eventMass rest event
  ≡⟨ cong₂ _+_
       (eventMass-map-weight right (λ x → (ω , x)) w event)
       (eventMass-weightedCartesian-bind xs right event) ⟩
    w * eventMass right (λ x → event (ω , x)) +
      sum (map (λ (ω₁ , w₁) → w₁ * eventMass right (λ x → event (ω₁ , x))) xs)
  ∎
  where
  row = map (λ (x , v) → ((ω , x) , w * v)) right
  rest = weightedCartesian xs right

-- Two records that list the same atoms and use the same denominator are the
-- same record. The positivity witness and the mass equation each have only
-- one proof, so they do not distinguish presentations.
same-record : {Ω : Set} {a a' : List (Ω × ℕ)} {d d' : ℕ}
  {p : 0 < d} {p' : 0 < d'}
  {t : totalMass a ≡ d} {t' : totalMass a' ≡ d'} →
  a ≡ a' → d ≡ d' →
  finiteRecord a d p t ≡ finiteRecord a' d' p' t'
same-record refl refl = cong₂ (finiteRecord _ _) (≤-unique _ _) (uip _≟_ _ _)

-- Push a function through every label. Zero weights stay zero, and repeated
-- labels stay repeated; only the names change.
pushforward : {Ω X : Set} → FiniteProbRecord Ω → (Ω → X) → FiniteProbRecord X
pushforward R f = finiteRecord
  (map (relabel f) (atoms R))
  (den R)
  (den-pos R)
  (trans (totalMass-map-labels (atoms R) f) (total R))

pushforward-probVal : {Ω X : Set} (R : FiniteProbRecord Ω) (f : Ω → X)
  (event : Event X) →
  Equiv (probVal (pushforward R f) event)
        (probVal R (λ ω → event (f ω)))
pushforward-probVal R f event =
  cong (_* den R) (eventMass-map-labels (atoms R) f event)

map-relabel-comp : {Ω X Y : Set} (f : Ω → X) (g : X → Y)
  (atoms : List (Ω × ℕ)) →
  map (relabel g) (map (relabel f) atoms) ≡
  map (relabel (λ ω → g (f ω))) atoms
map-relabel-comp f g []             = refl
map-relabel-comp f g ((_ , _) ∷ xs) rewrite map-relabel-comp f g xs = refl

map-relabel-id : {Ω : Set} (atoms : List (Ω × ℕ)) →
  map (relabel (λ ω → ω)) atoms ≡ atoms
map-relabel-id []             = refl
map-relabel-id ((_ , _) ∷ xs) rewrite map-relabel-id xs = refl

-- Relabelling twice is relabelling by the composite, including the
-- denominator witness.
pushforward-comp : {Ω X Y : Set} (R : FiniteProbRecord Ω)
  (f : Ω → X) (g : X → Y) →
  pushforward (pushforward R f) g ≡ pushforward R (λ ω → g (f ω))
pushforward-comp R f g =
  same-record (map-relabel-comp f g (atoms R)) refl

-- The identity relabelling leaves atoms, weights, and the denominator as
-- they stand.
pushforward-id : {Ω : Set} (R : FiniteProbRecord Ω) →
  pushforward R (λ ω → ω) ≡ R
pushforward-id R = same-record (map-relabel-id (atoms R)) refl

-- The independent product uses the product of the denominators. Its atoms
-- are the weighted cartesian product, so a missing factor still yields no
-- pairs.
product : {Ω X : Set} → FiniteProbRecord Ω → FiniteProbRecord X →
          FiniteProbRecord (Ω × X)
product left right = finiteRecord
  (weightedCartesian (atoms left) (atoms right))
  (den left * den right)
  (*-pos (den-pos left) (den-pos right))
  (trans (totalMass-weightedCartesian (atoms left) (atoms right))
         (cong₂ _*_ (total left) (total right)))

-- A rectangle factors as the product of its side probabilities.
product-probVal : {Ω X : Set} (left : FiniteProbRecord Ω)
  (right : FiniteProbRecord X) (leftEvent : Event Ω) (rightEvent : Event X) →
  Equiv (probVal (product left right)
          (λ pair → leftEvent (fst pair) ∧ rightEvent (snd pair)))
        (mul (probVal left leftEvent) (probVal right rightEvent))
product-probVal left right leftEvent rightEvent
  rewrite eventMass-weightedCartesian (atoms left) (atoms right)
            leftEvent rightEvent = refl

-- An event that ignores the left coordinate has the right-hand probability.
-- The left factor is the certain event, and that factor is one.
product-probVal-right : {Ω X : Set} (left : FiniteProbRecord Ω)
  (right : FiniteProbRecord X) (event : Event X) →
  Equiv (probVal (product left right) (λ pair → event (snd pair)))
        (probVal right event)
product-probVal-right left right event =
  equiv-trans
    {p = probVal (product left right) (λ pair → event (snd pair))}
    {q = mul (probVal left topEvent) (probVal right event)}
    {r = probVal right event}
    (product-probVal left right topEvent event)
    (equiv-trans
      {p = mul (probVal left topEvent) (probVal right event)}
      {q = mul one (probVal right event)}
      {r = probVal right event}
      (mul-congr
        {p = probVal left topEvent} {p' = one}
        {q = probVal right event} {q' = probVal right event}
        (normalization left) (equiv-refl (probVal right event)))
      (one-mul (probVal right event)))

-- Slicewise agreement of the varying factor is enough for a joint event.
-- The common factor stays independent, and no support is chosen from it.
product-probVal-slices : {Ω X Y : Set}
  (common : FiniteProbRecord Ω) (left : FiniteProbRecord X)
  (right : FiniteProbRecord Y)
  (leftEvent : Event (Ω × X)) (rightEvent : Event (Ω × Y)) →
  (∀ value → Equiv (probVal left (λ sample → leftEvent (value , sample)))
                   (probVal right (λ sample → rightEvent (value , sample)))) →
  Equiv (probVal (product common left) leftEvent)
        (probVal (product common right) rightEvent)
product-probVal-slices {Ω} common left right leftEvent rightEvent slices =
  begin
    massL * (den common * den right)
  ≡⟨ cong (_* (den common * den right))
       (eventMass-weightedCartesian-bind (atoms common) (atoms left) leftEvent) ⟩
    sumL * (den common * den right)
  ≡⟨ cong (sumL *_) (*-comm (den common) (den right)) ⟩
    sumL * (den right * den common)
  ≡⟨ sym (*-assoc sumL (den right) (den common)) ⟩
    (sumL * den right) * den common
  ≡⟨ cong (_* den common) (scaled (atoms common)) ⟩
    (sumR * den left) * den common
  ≡⟨ *-assoc sumR (den left) (den common) ⟩
    sumR * (den left * den common)
  ≡⟨ cong (sumR *_) (*-comm (den left) (den common)) ⟩
    sumR * (den common * den left)
  ≡⟨ cong (_* (den common * den left))
       (sym (eventMass-weightedCartesian-bind (atoms common) (atoms right)
              rightEvent)) ⟩
    massR * (den common * den left)
  ∎
  where
  massL = eventMass (weightedCartesian (atoms common) (atoms left)) leftEvent
  massR = eventMass (weightedCartesian (atoms common) (atoms right)) rightEvent
  sumL = sum (map (λ (ω , w) →
           w * eventMass (atoms left) (λ sample → leftEvent (ω , sample)))
           (atoms common))
  sumR = sum (map (λ (ω , w) →
           w * eventMass (atoms right) (λ sample → rightEvent (ω , sample)))
           (atoms common))
  scaled : (support : List (Ω × ℕ)) →
    sum (map (λ (ω , w) →
          w * eventMass (atoms left) (λ sample → leftEvent (ω , sample)))
         support) * den right ≡
    sum (map (λ (ω , w) →
          w * eventMass (atoms right) (λ sample → rightEvent (ω , sample)))
         support) * den left
  scaled [] = refl
  scaled ((ω , w) ∷ xs) =
    begin
      (w * mL + restL) * den right
    ≡⟨ *-distribʳ-+ (w * mL) restL (den right) ⟩
      (w * mL) * den right + restL * den right
    ≡⟨ cong₂ _+_ (*-assoc w mL (den right)) (scaled xs) ⟩
      w * (mL * den right) + restR * den left
    ≡⟨ cong (λ z → w * z + restR * den left) (slices ω) ⟩
      w * (mR * den left) + restR * den left
    ≡⟨ cong (_+ restR * den left) (sym (*-assoc w mR (den left))) ⟩
      (w * mR) * den left + restR * den left
    ≡⟨ sym (*-distribʳ-+ (w * mR) restR (den left)) ⟩
      (w * mR + restR) * den left
    ∎
    where
    mL = eventMass (atoms left) (λ sample → leftEvent (ω , sample))
    mR = eventMass (atoms right) (λ sample → rightEvent (ω , sample))
    restL = sum (map (λ (ω₁ , w₁) →
              w₁ * eventMass (atoms left) (λ sample → leftEvent (ω₁ , sample)))
             xs)
    restR = sum (map (λ (ω₁ , w₁) →
              w₁ * eventMass (atoms right)
                (λ sample → rightEvent (ω₁ , sample)))
             xs)

-- A relabelling of the right factor can be read on the event instead.
product-map-right-probVal : {Ω X Y : Set} (left : FiniteProbRecord Ω)
  (right : FiniteProbRecord X) (encode : X → Y) (event : Event (Ω × Y)) →
  Equiv (probVal (product left (pushforward right encode)) event)
        (probVal (product left right)
          (λ pair → event (fst pair , encode (snd pair))))
product-map-right-probVal {Ω} left right encode event =
  cong (_* (den left * den right))
    (trans (eventMass-weightedCartesian-bind (atoms left)
              (map (relabel encode) (atoms right)) event)
      (trans (slice-sum (atoms left))
        (sym (eventMass-weightedCartesian-bind (atoms left) (atoms right)
               (λ pair → event (fst pair , encode (snd pair)))))))
  where
  slice-sum : (support : List (Ω × ℕ)) →
    sum (map (λ (ω , w) →
          w * eventMass (map (relabel encode) (atoms right))
               (λ y → event (ω , y))) support) ≡
    sum (map (λ (ω , w) →
          w * eventMass (atoms right)
               (λ x → event (ω , encode x))) support)
  slice-sum [] = refl
  slice-sum ((ω , w) ∷ xs)
    rewrite eventMass-map-labels (atoms right) encode (λ y → event (ω , y))
          | slice-sum xs = refl

-- A relabelling of the left factor can likewise be read on the event.
product-map-left-probVal : {Ω X Y : Set} (left : FiniteProbRecord Ω)
  (right : FiniteProbRecord X) (encode : Ω → Y) (event : Event (Y × X)) →
  Equiv (probVal (product (pushforward left encode) right) event)
        (probVal (product left right)
          (λ pair → event (encode (fst pair) , snd pair)))
product-map-left-probVal {Ω} left right encode event =
  cong (_* (den left * den right))
    (trans (eventMass-weightedCartesian-bind
              (map (relabel encode) (atoms left)) (atoms right) event)
      (trans (slice-sum (atoms left))
        (sym (eventMass-weightedCartesian-bind (atoms left) (atoms right)
               (λ pair → event (encode (fst pair) , snd pair))))))
  where
  slice-sum : (support : List (Ω × ℕ)) →
    sum (map (λ (y , w) → w * eventMass (atoms right) (λ x → event (y , x)))
             (map (relabel encode) support)) ≡
    sum (map (λ (ω , w) →
          w * eventMass (atoms right) (λ x → event (encode ω , x))) support)
  slice-sum [] = refl
  slice-sum ((ω , w) ∷ xs) rewrite slice-sum xs = refl

-- `if b then w else 0` adds the same weight as `add-if`. The Boolean is an
-- argument, so the two forms agree before it is inspected.
add-if-shift : (b : Bool) (w m : ℕ) → (if b then w else 0) + m ≡ add-if b w m
add-if-shift true  w m = refl
add-if-shift false w m = refl

-- Replace each weight by that many copies of its label. The listing has one
-- cell per unit of mass, and a zero weight contributes no cell.
expand : {Ω : Set} → List (Ω × ℕ) → List Ω
expand []             = []
expand ((ω , w) ∷ xs) = replicate w ω ++ expand xs

length-expand : {Ω : Set} (atoms : List (Ω × ℕ)) →
  length (expand atoms) ≡ totalMass atoms
length-expand []             = refl
length-expand ((ω , w) ∷ xs) =
  begin
    length (replicate w ω ++ expand xs)
  ≡⟨ length-++ (replicate w ω) (expand xs) ⟩
    length (replicate w ω) + length (expand xs)
  ≡⟨ cong₂ _+_ (length-replicate w ω) (length-expand xs) ⟩
    w + totalMass xs
  ∎

count-expand : {Ω : Set} (atoms : List (Ω × ℕ)) (E : Event Ω) →
  count (expand atoms) E ≡ eventMass atoms E
count-expand []             E = refl
count-expand ((ω , w) ∷ xs) E =
  begin
    count (replicate w ω ++ expand xs) E
  ≡⟨ countP-++ E (replicate w ω) (expand xs) ⟩
    count (replicate w ω) E + count (expand xs) E
  ≡⟨ cong₂ _+_ (countP-replicate E w ω) (count-expand xs E) ⟩
    (if E ω then w else 0) + eventMass xs E
  ≡⟨ add-if-shift (E ω) w (eventMass xs E) ⟩
    eventMass ((ω , w) ∷ xs) E
  ∎

-- Unit weights make the total mass the length of the label list.
totalMass-unit : {Ω : Set} (xs : List Ω) →
  totalMass (map (λ ω → (ω , 1)) xs) ≡ length xs
totalMass-unit []       = refl
totalMass-unit (_ ∷ xs) rewrite totalMass-unit xs = refl

-- And the event mass is the number of accepted labels.
eventMass-unit : {Ω : Set} (xs : List Ω) (E : Event Ω) →
  eventMass (map (λ ω → (ω , 1)) xs) E ≡ count xs E
eventMass-unit []       E = refl
eventMass-unit (x ∷ xs) E with E x
... | true  rewrite eventMass-unit xs E = refl
... | false rewrite eventMass-unit xs E = refl

-- A singleton event accepts exactly the sample identified with `value`.
-- The decision procedure is part of the data: the sample type need not
-- carry a canonical equality of its own.
singletonEvent : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y)) → Ω → Event Ω
singletonEvent eq value candidate = fromDec (eq candidate value)

-- Membership accepts a sample when the procedure finds it in the list.
membershipEvent : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y)) →
                  List Ω → Event Ω
membershipEvent eq values candidate = fromDec (∈-dec eq candidate values)

singleton-holds : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (value candidate : Ω) →
  singletonEvent eq value candidate ≡ true → candidate ≡ value
singleton-holds eq value candidate h = fromDec-yes (eq candidate value) h

membership-holds : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (values : List Ω) (candidate : Ω) →
  membershipEvent eq values candidate ≡ true → candidate ∈ values
membership-holds eq values candidate h =
  fromDec-yes (∈-dec eq candidate values) h

-- Extending the list by one head is the union of that singleton with
-- membership in the tail, at every candidate.
membership-cons : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (value : Ω) (values : List Ω) (candidate : Ω) →
  membershipEvent eq (value ∷ values) candidate ≡
  union (singletonEvent eq value) (membershipEvent eq values) candidate
membership-cons eq value values candidate
  with eq candidate value | ∈-dec eq candidate values
... | yes _ | _       = refl
... | no  _ | yes _   = refl
... | no  _ | no  _   = refl

-- The finite union of the singletons is membership in the list, at every
-- candidate. No identification of the two events as functions is required.
unionList-singletons : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (values : List Ω) (candidate : Ω) →
  unionList (map (singletonEvent eq) values) candidate ≡
  membershipEvent eq values candidate
unionList-singletons eq []             candidate = refl
unionList-singletons eq (value ∷ values) candidate =
  begin
    singletonEvent eq value candidate ∨
      unionList (map (singletonEvent eq) values) candidate
  ≡⟨ cong (singletonEvent eq value candidate ∨_)
       (unionList-singletons eq values candidate) ⟩
    singletonEvent eq value candidate ∨ membershipEvent eq values candidate
  ≡⟨ sym (membership-cons eq value values candidate) ⟩
    membershipEvent eq (value ∷ values) candidate
  ∎

-- A sample of the head singleton and of a later singleton would identify
-- the head with that later entry.
fresh-disjoint : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (head : Ω) (tail : List Ω) →
  All (head ≢_) tail →
  All (disjoint (singletonEvent eq head)) (map (singletonEvent eq) tail)
fresh-disjoint eq head []             []           = []
fresh-disjoint eq head (y ∷ ys) (y≠ ∷ rest) =
  (λ candidate hHead hY →
     y≠ (trans (sym (singleton-holds eq head candidate hHead))
               (singleton-holds eq y candidate hY)))
  ∷ fresh-disjoint eq head ys rest

-- Distinct entries have pairwise disjoint singletons.
singleton-pairwise : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  {values : List Ω} → Pairwise _≢_ values →
  Pairwise disjoint (map (singletonEvent eq) values)
singleton-pairwise eq []                    = []
singleton-pairwise eq {value ∷ values} (fresh ∷ nodup) =
  fresh-disjoint eq value values fresh ∷ singleton-pairwise eq nodup

-- A value absent from the list has a singleton disjoint from membership.
singleton-membership-disjoint : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  {value : Ω} {values : List Ω} → value ∉ values →
  disjoint (singletonEvent eq value) (membershipEvent eq values)
singleton-membership-disjoint eq {value} {values} absent candidate hValue hMember =
  absent (subst (_∈ values) (singleton-holds eq value candidate hValue)
           (membership-holds eq values candidate hMember))

-- Membership in a repetition-free list is the sum of its singleton
-- probabilities. Each label is counted once.
probVal-membership-sum : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (R : FiniteProbRecord Ω) (values : List Ω) → Pairwise _≢_ values →
  Equiv (probVal R (membershipEvent eq values))
        (listSum (map (λ value → probVal R (singletonEvent eq value)) values))
probVal-membership-sum eq R [] [] =
  equiv-trans
    {p = probVal R (membershipEvent eq [])}
    {q = probVal R (λ _ → false)}
    {r = listSum []}
    (probVal-cong R (membershipEvent eq []) (λ _ → false) (λ _ → refl))
    (probVal-false R)
probVal-membership-sum eq R (value ∷ values) (fresh ∷ nodup) =
  equiv-trans
    {p = probVal R (membershipEvent eq (value ∷ values))}
    {q = probVal R (union (singletonEvent eq value) (membershipEvent eq values))}
    {r = add (probVal R (singletonEvent eq value))
             (listSum (map (λ v → probVal R (singletonEvent eq v)) values))}
    (probVal-cong R _ _
      (membership-cons eq value values))
    (equiv-trans
      {p = probVal R (union (singletonEvent eq value) (membershipEvent eq values))}
      {q = add (probVal R (singletonEvent eq value))
               (probVal R (membershipEvent eq values))}
      {r = add (probVal R (singletonEvent eq value))
               (listSum (map (λ v → probVal R (singletonEvent eq v)) values))}
      (probVal-union-disjoint R _ _
        (singleton-membership-disjoint eq (∉-of-all fresh)))
      (add-cong
        {p = probVal R (singletonEvent eq value)}
        {p' = probVal R (singletonEvent eq value)}
        {q = probVal R (membershipEvent eq values)}
        {q' = listSum (map (λ v → probVal R (singletonEvent eq v)) values)}
        (equiv-refl (probVal R (singletonEvent eq value)))
        (probVal-membership-sum eq R values nodup)))

-- Filtering a complete listing by an event recovers that event at every
-- candidate. A rejected candidate is absent from the filtered list, and an
-- accepted candidate occurs because the listing was complete.
membership-filter : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (values : List Ω) (complete : ∀ value → value ∈ values)
  (event : Event Ω) (candidate : Ω) →
  membershipEvent eq (filter event values) candidate ≡ event candidate
membership-filter eq values complete event candidate =
  step (event candidate) refl
  where
  step : (b : Bool) → event candidate ≡ b →
         membershipEvent eq (filter event values) candidate ≡ b
  step true e =
    fromDec-of-proof (∈-dec eq candidate (filter event values))
      (∈-filter-complete event values e (complete candidate))
  step false e =
    fromDec-false (∈-dec eq candidate (filter event values))
      (λ mem → false≢true (trans (sym e) (∈-filter-sound event values mem)))

-- On a complete repetition-free listing, an event probability is the sum of
-- the singleton probabilities the event accepts.
probVal-filtered-sum : {Ω : Set} (eq : (x y : Ω) → Dec (x ≡ y))
  (R : FiniteProbRecord Ω) (values : List Ω) →
  Pairwise _≢_ values → (∀ value → value ∈ values) → (event : Event Ω) →
  Equiv (probVal R event)
        (listSum (map (λ value → probVal R (singletonEvent eq value))
                      (filter event values)))
probVal-filtered-sum eq R values nodup complete event =
  equiv-trans
    {p = probVal R event}
    {q = probVal R (membershipEvent eq (filter event values))}
    {r = listSum (map (λ value → probVal R (singletonEvent eq value))
                      (filter event values))}
    (probVal-cong R event (membershipEvent eq (filter event values))
      (λ candidate → sym (membership-filter eq values complete event candidate)))
    (probVal-membership-sum eq R (filter event values)
      (pairwise-filter event nodup))

-- Singleton probabilities determine every event probability. The two records
-- may use different atoms; only the singleton masses are compared.
probVal-determined-by-singletons : {Ω : Set}
  (eq : (x y : Ω) → Dec (x ≡ y))
  (left right : FiniteProbRecord Ω) (values : List Ω) →
  Pairwise _≢_ values → (∀ value → value ∈ values) →
  (∀ value → Equiv (probVal left (singletonEvent eq value))
                   (probVal right (singletonEvent eq value))) →
  (event : Event Ω) →
  Equiv (probVal left event) (probVal right event)
probVal-determined-by-singletons eq left right values nodup complete singletons event =
  equiv-trans
    {p = probVal left event}
    {q = listSum (map (λ value → probVal left (singletonEvent eq value))
                      (filter event values))}
    {r = probVal right event}
    (probVal-filtered-sum eq left values nodup complete event)
    (equiv-trans
      {p = listSum (map (λ value → probVal left (singletonEvent eq value))
                        (filter event values))}
      {q = listSum (map (λ value → probVal right (singletonEvent eq value))
                        (filter event values))}
      {r = probVal right event}
      (listSum-map-congr (filter event values)
        (λ value → probVal left (singletonEvent eq value))
        (λ value → probVal right (singletonEvent eq value))
        singletons)
      (equiv-sym
        {p = probVal right event}
        {q = listSum (map (λ value → probVal right (singletonEvent eq value))
                          (filter event values))}
        (probVal-filtered-sum eq right values nodup complete event)))

-- Expand each weight into that many unit cells. A zero weight contributes
-- no cell, and the resulting urn is occupied because the record denominator
-- is positive.
toUrn : {Ω : Set} → FiniteProbRecord Ω → Urn.Urn Ω
toUrn R = Urn.ofList (expand (atoms R))
  (subst (0 <_) (sym (length-expand (atoms R)))
    (subst (0 <_) (sym (total R)) (den-pos R)))

-- A record and its unit-cell urn assign the same probability to every event.
-- The cell count is the event mass, and the number of cells is the denominator.
toUrn-agrees : {Ω : Set} (R : FiniteProbRecord Ω) (E : Event Ω) →
  Equiv (probVal R E) (Urn.probVal (toUrn R) E)
toUrn-agrees R E =
  begin
    eventMass (atoms R) E * length (expand (atoms R))
  ≡⟨ cong (_* length (expand (atoms R))) (sym (count-expand (atoms R) E)) ⟩
    count (expand (atoms R)) E * length (expand (atoms R))
  ≡⟨ cong (count (expand (atoms R)) E *_)
       (trans (length-expand (atoms R)) (total R)) ⟩
    count (expand (atoms R)) E * den R
  ∎

-- The unit-weight record of an urn. Each cell becomes an atom of weight one,
-- so the denominator is the number of cells.
ofUrn : {Ω : Set} → Urn.Urn Ω → FiniteProbRecord Ω
ofUrn μ = finiteRecord (map (λ ω → (ω , 1)) (Urn.cells μ))
  (Urn.size μ) (Urn.occupied μ) (totalMass-unit (Urn.cells μ))

ofUrn-agrees : {Ω : Set} (μ : Urn.Urn Ω) (E : Event Ω) →
  Equiv (probVal (ofUrn μ) E) (Urn.probVal μ E)
ofUrn-agrees μ E =
  cong (_* Urn.size μ) (eventMass-unit (Urn.cells μ) E)

-- A pairwise disjoint family adds in the record because it adds in the
-- unit-cell urn, and the two presentations agree on every event.
record-additive-family : {Ω : Set} (R : FiniteProbRecord Ω)
  (events : List (Event Ω)) → Pairwise disjoint events →
  Equiv (probVal R (unionList events))
        (listSum (map (probVal R) events))
record-additive-family R events pw =
  equiv-trans
    {p = probVal R (unionList events)}
    {q = Urn.probVal (toUrn R) (unionList events)}
    {r = listSum (map (probVal R) events)}
    (toUrn-agrees R (unionList events))
    (equiv-trans
      {p = Urn.probVal (toUrn R) (unionList events)}
      {q = listSum (map (Urn.probVal (toUrn R)) events)}
      {r = listSum (map (probVal R) events)}
      (Urn.additive-family (toUrn R) events pw)
      (listSum-map-congr events
        (Urn.probVal (toUrn R)) (probVal R)
        (λ event → equiv-sym {p = probVal R event}
          {q = Urn.probVal (toUrn R) event} (toUrn-agrees R event))))
