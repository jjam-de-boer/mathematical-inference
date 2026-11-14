module Thesis.Probability.Urn where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
open import Thesis.Probability.Core
open import Thesis.Probability.ConstructivePermutation using (pairList; pairList-length)
open import Thesis.Probability.QProb using
  (QProb; qprob; Equiv; LE; zero-le; ≤-cong; add; mul; div; listSum; one;
   add-cong; equiv-refl; equiv-sym; equiv-trans; num; den)

-- A finite urn is a nonempty list of equally weighted cells. Cells may share
-- a label: repeated labels are repeated cells, not a set. The probability of
-- an event is the number of cells it accepts divided by the number of cells.

record Urn (X : Set) : Set where
  constructor urn
  field
    cells    : List X
    occupied : 0 < length cells

open Urn public

-- The number of cells. It is positive by the occupancy witness.
size : {X : Set} → Urn X → ℕ
size μ = length (cells μ)

-- Build an urn from a nonempty list of labels. The list is the cell sequence.
ofList : {X : Set} (xs : List X) → 0 < length xs → Urn X
ofList = urn

-- How many cells the event accepts.
probNum : {X : Set} → Urn X → Event X → ℕ
probNum μ E = count (cells μ) E

-- The accepted-cell count as a rational presentation with the urn size as
-- denominator. No reduced representative is chosen.
probVal : {X : Set} → Urn X → Event X → QProb
probVal μ E = qprob (probNum μ E) (size μ) (occupied μ)

-- Relabel every cell. The number of cells is unchanged, and a repeated label
-- stays repeated.
relabel : {X Y : Set} → Urn X → (X → Y) → Urn Y
relabel μ f = urn (map f (cells μ))
  (subst (0 <_) (sym (length-map f (cells μ))) (occupied μ))

relabel-num : {X Y : Set} (μ : Urn X) (f : X → Y) (E : Event Y) →
  probNum (relabel μ f) E ≡ probNum μ (λ x → E (f x))
relabel-num μ f E = count-map f E (cells μ)
  where
  count-map : {A B : Set} (g : A → B) (Ev : Event B) (xs : List A) →
    count (map g xs) Ev ≡ count xs (λ x → Ev (g x))
  count-map g Ev [] = refl
  count-map g Ev (x ∷ xs) rewrite count-map g Ev xs = refl

relabel-prob : {X Y : Set} (μ : Urn X) (f : X → Y) (E : Event Y) →
  Equiv (probVal (relabel μ f) E) (probVal μ (λ x → E (f x)))
relabel-prob μ f E =
  begin
    probNum (relabel μ f) E * size μ
  ≡⟨ cong (_* size μ) (relabel-num μ f E) ⟩
    probNum μ (λ x → E (f x)) * size μ
  ≡⟨ cong (probNum μ (λ x → E (f x)) *_) (sym (length-map f (cells μ))) ⟩
    probNum μ (λ x → E (f x)) * size (relabel μ f)
  ∎

-- One row contributes the right-hand count when the left test accepts it.
row-step : (e f : Bool) (n : ℕ) →
  extra (e ∧ f) + (if e then n else 0) ≡ (if e then extra f + n else 0)
row-step true  true  n = refl
row-step true  false n = refl
row-step false true  n = refl
row-step false false n = refl

nil-row : (e : Bool) → zero ≡ (if e then zero else zero)
nil-row true  = refl
nil-row false = refl

count-row : {A B : Set} (a : A) (ys : List B) (E : Event A) (F : Event B) →
  count (map (λ b → (a , b)) ys) (λ p → E (fst p) ∧ F (snd p)) ≡
  (if E a then count ys F else 0)
count-row a [] E F = nil-row (E a)
count-row a (b ∷ ys) E F =
  begin
    extra (E a ∧ F b) + count (map (λ c → (a , c)) ys) (λ p → E (fst p) ∧ F (snd p))
  ≡⟨ cong (extra (E a ∧ F b) +_) (count-row a ys E F) ⟩
    extra (E a ∧ F b) + (if E a then count ys F else 0)
  ≡⟨ row-step (E a) (F b) (count ys F) ⟩
    if E a then extra (F b) + count ys F else 0
  ∎

row-distrib : (e : Bool) (c n : ℕ) →
  (if e then c else 0) + n * c ≡ (extra e + n) * c
row-distrib true  c n = refl
row-distrib false c n = refl

count-pairs : {A B : Set} (xs : List A) (ys : List B)
  (E : Event A) (F : Event B) →
  count (pairList xs ys) (λ p → E (fst p) ∧ F (snd p)) ≡
  count xs E * count ys F
count-pairs [] ys E F = refl
count-pairs (x ∷ xs) ys E F =
  begin
    count (map (λ b → (x , b)) ys ++ pairList xs ys)
      (λ p → E (fst p) ∧ F (snd p))
  ≡⟨ countP-++ (λ p → E (fst p) ∧ F (snd p))
       (map (λ b → (x , b)) ys) (pairList xs ys) ⟩
    count (map (λ b → (x , b)) ys) (λ p → E (fst p) ∧ F (snd p)) +
      count (pairList xs ys) (λ p → E (fst p) ∧ F (snd p))
  ≡⟨ cong₂ _+_ (count-row x ys E F) (count-pairs xs ys E F) ⟩
    (if E x then count ys F else 0) + count xs E * count ys F
  ≡⟨ row-distrib (E x) (count ys F) (count xs E) ⟩
    count (x ∷ xs) E * count ys F
  ∎

-- The independent product urn. Its cells are the pairs of cells, with the
-- right factor varying fastest, and each pair is one cell.
product : {X Y : Set} → Urn X → Urn Y → Urn (X × Y)
product μ ν = urn (pairList (cells μ) (cells ν))
  (subst (0 <_) (sym (pairList-length (cells μ) (cells ν)))
    (*-pos (occupied μ) (occupied ν)))

product-num : {X Y : Set} (μ : Urn X) (ν : Urn Y) (E : Event X) (F : Event Y) →
  probNum (product μ ν) (λ p → E (fst p) ∧ F (snd p)) ≡
  probNum μ E * probNum ν F
product-num μ ν E F = count-pairs (cells μ) (cells ν) E F

product-prob : {X Y : Set} (μ : Urn X) (ν : Urn Y) (E : Event X) (F : Event Y) →
  Equiv (probVal (product μ ν) (λ p → E (fst p) ∧ F (snd p)))
        (mul (probVal μ E) (probVal ν F))
product-prob μ ν E F
  rewrite product-num μ ν E F
        | pairList-length (cells μ) (cells ν) = refl

-- Conditioning keeps the cells the evidence accepts. The new urn is defined
-- only when at least one cell is kept, so the posterior denominator is positive.
condition : {X : Set} (μ : Urn X) (E : Event X) → 0 < probNum μ E → Urn X
condition μ E positive = urn (filter E (cells μ))
  (subst (0 <_) (sym (length-filter E (cells μ))) positive)

condition-num : {X : Set} (μ : Urn X) (E F : Event X) (hE : 0 < probNum μ E) →
  probNum (condition μ E hE) F ≡ probNum μ (inter E F)
condition-num μ E F hE = count-filter E F (cells μ)

-- The conditional value is the joint count over the conditioning count.
condVal : {X : Set} (μ : Urn X) (E F : Event X) → 0 < probNum μ F → QProb
condVal μ E F hF = qprob (probNum μ (inter E F)) (probNum μ F) hF

condition-prob : {X : Set} (μ : Urn X) (E F : Event X) (hE : 0 < probNum μ E) →
  Equiv (probVal (condition μ E hE) F) (condVal μ F E hE)
condition-prob μ E F hE =
  begin
    probNum (condition μ E hE) F * probNum μ E
  ≡⟨ cong (_* probNum μ E) (condition-num μ E F hE) ⟩
    probNum μ (inter E F) * probNum μ E
  ≡⟨ cong (λ n → n * probNum μ E) (count-inter-comm (cells μ) E F) ⟩
    probNum μ (inter F E) * probNum μ E
  ≡⟨ cong (probNum μ (inter F E) *_) (sym (length-filter E (cells μ))) ⟩
    probNum μ (inter F E) * length (filter E (cells μ))
  ∎

-- Every cell count is at most the urn size.
probNum-≤-size : {X : Set} (μ : Urn X) (E : Event X) → probNum μ E ≤ size μ
probNum-≤-size μ E = count-≤-length (cells μ) E

prob-nonneg : {X : Set} (μ : Urn X) (E : Event X) →
  LE Thesis.Probability.QProb.zero (probVal μ E)
prob-nonneg μ E = zero-le (probVal μ E)

prob-≤-one : {X : Set} (μ : Urn X) (E : Event X) → LE (probVal μ E) one
prob-≤-one μ E =
  ≤-cong (sym (*-idʳ (probNum μ E))) (sym (+-idʳ (size μ))) (probNum-≤-size μ E)

prob-bounds : {X : Set} (μ : Urn X) (E : Event X) →
  LE Thesis.Probability.QProb.zero (probVal μ E) × LE (probVal μ E) one
prob-bounds μ E = prob-nonneg μ E , prob-≤-one μ E

probNum-top : {X : Set} (μ : Urn X) → probNum μ topEvent ≡ size μ
probNum-top μ = count-top (cells μ)

normalization : {X : Set} (μ : Urn X) → Equiv (probVal μ topEvent) one
normalization μ =
  begin
    probNum μ topEvent * 1
  ≡⟨ cong (_* 1) (probNum-top μ) ⟩
    size μ * 1
  ≡⟨ *-idʳ (size μ) ⟩
    size μ
  ≡⟨ sym (+-idʳ (size μ)) ⟩
    1 * size μ
  ∎

prob-bottom : {X : Set} (μ : Urn X) →
  Equiv (probVal μ bottomEvent) Thesis.Probability.QProb.zero
prob-bottom μ rewrite count-bottom (cells μ) = refl

-- An event and its complement use every cell exactly once, so their
-- probabilities sum to one.
complement-rule : {X : Set} (μ : Urn X) (E : Event X) →
  Equiv (add (probVal μ E) (probVal μ (complement E))) one
complement-rule μ E =
  begin
    (probNum μ E * size μ + probNum μ (complement E) * size μ) * 1
  ≡⟨ cong (_* 1) (sym (*-distribʳ-+ (probNum μ E) (probNum μ (complement E)) (size μ))) ⟩
    (probNum μ E + probNum μ (complement E)) * size μ * 1
  ≡⟨ cong (λ n → n * size μ * 1) (count-add-count-complement (cells μ) E) ⟩
    size μ * size μ * 1
  ≡⟨ *-idʳ (size μ * size μ) ⟩
    size μ * size μ
  ≡⟨ sym (+-idʳ (size μ * size μ)) ⟩
    1 * (size μ * size μ)
  ∎

condition-normalization : {X : Set} (μ : Urn X) (E : Event X) (hE : 0 < probNum μ E) →
  Equiv (probVal (condition μ E hE) topEvent) one
condition-normalization μ E hE = normalization (condition μ E hE)

additive-num : {X : Set} (μ : Urn X) (E F : Event X) → disjoint E F →
  probNum μ (union E F) ≡ probNum μ E + probNum μ F
additive-num μ E F disj = count-union-disjoint (cells μ) E F disj

additive : {X : Set} (μ : Urn X) (E F : Event X) → disjoint E F →
  Equiv (probVal μ (union E F)) (add (probVal μ E) (probVal μ F))
additive μ E F disj =
  begin
    probNum μ (union E F) * (size μ * size μ)
  ≡⟨ cong (_* (size μ * size μ)) (additive-num μ E F disj) ⟩
    (probNum μ E + probNum μ F) * (size μ * size μ)
  ≡⟨ sym (*-assoc (probNum μ E + probNum μ F) (size μ) (size μ)) ⟩
    ((probNum μ E + probNum μ F) * size μ) * size μ
  ≡⟨ cong (_* size μ) (*-distribʳ-+ (probNum μ E) (probNum μ F) (size μ)) ⟩
    (probNum μ E * size μ + probNum μ F * size μ) * size μ
  ∎

additive-family-num : {X : Set} (μ : Urn X) (events : List (Event X)) →
  Pairwise disjoint events →
  probNum μ (unionList events) ≡ sum (map (probNum μ) events)
additive-family-num μ events pw = count-unionList-pairwise (cells μ) pw

additive-family : {X : Set} (μ : Urn X) (events : List (Event X)) →
  Pairwise disjoint events →
  Equiv (probVal μ (unionList events)) (listSum (map (probVal μ) events))
additive-family μ [] [] = prob-bottom μ
additive-family μ (E ∷ events) (fresh ∷ pw) =
  equiv-trans
    {p = probVal μ (union E (unionList events))}
    {q = add (probVal μ E) (probVal μ (unionList events))}
    {r = add (probVal μ E) (listSum (map (probVal μ) events))}
    (additive μ E (unionList events) (disjoint-unionList fresh))
    (add-cong
      {p = probVal μ E} {p' = probVal μ E}
      {q = probVal μ (unionList events)}
      {q' = listSum (map (probVal μ) events)}
      (equiv-refl (probVal μ E))
      (additive-family μ events pw))

-- The three inspection statuses partition the cells.
status-num : {S : Set} {A : S → Set} (μ : Urn S) (I : Inspection S A) →
  probNum μ (provedEvent I) + probNum μ (refutedEvent I) +
  probNum μ (unresolvedEvent I) ≡ size μ
status-num μ I = status-count-partition (cells μ) (Inspection.status I)

-- A sub-event accepts no more cells, and therefore has no greater probability.
mono-num : {X : Set} (μ : Urn X) {E F : Event X} →
  (∀ x → E x ≡ true → F x ≡ true) → probNum μ E ≤ probNum μ F
mono-num μ h = count-mono {xs = cells μ} h

mono-prob : {X : Set} (μ : Urn X) {E F : Event X} →
  (∀ x → E x ≡ true → F x ≡ true) → LE (probVal μ E) (probVal μ F)
mono-prob μ {E} {F} h =
  le-of-same-den {p = probVal μ E} {q = probVal μ F} refl (mono-num μ h)

-- Inclusion-exclusion at the level of cells: the union and the intersection
-- together account for each event once.
union-inter-num : {X : Set} (μ : Urn X) (E F : Event X) →
  probNum μ (union E F) + probNum μ (inter E F) ≡ probNum μ E + probNum μ F
union-inter-num μ E F = count-union-inter (cells μ) E F

inclusion-exclusion : {X : Set} (μ : Urn X) (E F : Event X) →
  Equiv (add (probVal μ (union E F)) (probVal μ (inter E F)))
        (add (probVal μ E) (probVal μ F))
inclusion-exclusion μ E F =
  begin
    (nu * n + ni * n) * (n * n)
  ≡⟨ cong (_* (n * n)) (sym (*-distribʳ-+ nu ni n)) ⟩
    (nu + ni) * n * (n * n)
  ≡⟨ cong (λ k → (k * n) * (n * n)) (union-inter-num μ E F) ⟩
    (ne + nf) * n * (n * n)
  ≡⟨ cong (_* (n * n)) (*-distribʳ-+ ne nf n) ⟩
    (ne * n + nf * n) * (n * n)
  ∎
  where
  n = size μ
  nu = probNum μ (union E F)
  ni = probNum μ (inter E F)
  ne = probNum μ E
  nf = probNum μ F

-- Updating by a positive event is the probability in the retained urn.
update : {X : Set} (μ : Urn X) (E F : Event X) → 0 < probNum μ E → QProb
update μ E F hE = probVal (condition μ E hE) F

update-cond : {X : Set} (μ : Urn X) (E F : Event X) (hE : 0 < probNum μ E) →
  Equiv (update μ E F hE) (condVal μ F E hE)
update-cond μ E F hE = condition-prob μ E F hE

update-one : {X : Set} (μ : Urn X) (E : Event X) (hE : 0 < probNum μ E) →
  Equiv (update μ E topEvent hE) one
update-one μ E hE = condition-normalization μ E hE

-- The joint count is the conditional count times the conditioning count.
product-rule : {X : Set} (μ : Urn X) (E F : Event X) (hF : 0 < probNum μ F) →
  Equiv (mul (condVal μ E F hF) (probVal μ F)) (probVal μ (inter E F))
product-rule μ E F hF =
  *-assoc (probNum μ (inter E F)) (probNum μ F) (size μ)

-- Bayes' formula. Both positivity witnesses are kept: each conditional value
-- and the final division need a positive count.
bayes : {X : Set} (μ : Urn X) (E F : Event X)
  (hE : 0 < probNum μ E) (hF : 0 < probNum μ F) →
  Equiv (condVal μ E F hF)
        (div (mul (condVal μ F E hE) (probVal μ E)) (probVal μ F) hF)
bayes μ E F hE hF =
  begin
    cEF * ((cE * n) * cF)
  ≡⟨ cong (λ k → k * ((cE * n) * cF)) (count-inter-comm (cells μ) E F) ⟩
    cFE * ((cE * n) * cF)
  ≡⟨ sym (*-assoc cFE (cE * n) cF) ⟩
    (cFE * (cE * n)) * cF
  ≡⟨ cong (_* cF) (sym (*-assoc cFE cE n)) ⟩
    ((cFE * cE) * n) * cF
  ∎
  where
  cEF = probNum μ (inter E F)
  cFE = probNum μ (inter F E)
  cE = probNum μ E
  cF = probNum μ F
  n = size μ

-- The three status probabilities sum to one, because their cell counts
-- exhaust the urn and use the same denominator.
status-prob : {S : Set} {A : S → Set} (μ : Urn S) (I : Inspection S A) →
  Equiv (add (add (probVal μ (provedEvent I)) (probVal μ (refutedEvent I)))
             (probVal μ (unresolvedEvent I)))
        one
status-prob μ I =
  begin
    ((a * n + b * n) * n + c * (n * n)) * 1
  ≡⟨ *-idʳ ((a * n + b * n) * n + c * (n * n)) ⟩
    (a * n + b * n) * n + c * (n * n)
  ≡⟨ cong (λ k → k * n + c * (n * n)) (sym (*-distribʳ-+ a b n)) ⟩
    ((a + b) * n) * n + c * (n * n)
  ≡⟨ cong (_+ c * (n * n)) (*-assoc (a + b) n n) ⟩
    (a + b) * (n * n) + c * (n * n)
  ≡⟨ sym (*-distribʳ-+ (a + b) c (n * n)) ⟩
    ((a + b) + c) * (n * n)
  ≡⟨ cong (_* (n * n)) (status-num μ I) ⟩
    n * (n * n)
  ≡⟨ *-comm n (n * n) ⟩
    (n * n) * n
  ≡⟨ sym (+-idʳ ((n * n) * n)) ⟩
    1 * ((n * n) * n)
  ∎
  where
  a = probNum μ (provedEvent I)
  b = probNum μ (refutedEvent I)
  c = probNum μ (unresolvedEvent I)
  n = size μ

-- The two ways of factoring the joint count agree.
bayes-swap : {X : Set} (μ : Urn X) (E F : Event X)
  (hE : 0 < probNum μ E) (hF : 0 < probNum μ F) →
  Equiv (mul (condVal μ E F hF) (probVal μ F))
        (mul (condVal μ F E hE) (probVal μ E))
bayes-swap μ E F hE hF =
  begin
    (cEF * cF) * (cE * n)
  ≡⟨ cong (λ k → (k * cF) * (cE * n)) (count-inter-comm (cells μ) E F) ⟩
    (cFE * cF) * (cE * n)
  ≡⟨ sym (*-assoc (cFE * cF) cE n) ⟩
    ((cFE * cF) * cE) * n
  ≡⟨ cong (_* n) (*-comm (cFE * cF) cE) ⟩
    (cE * (cFE * cF)) * n
  ≡⟨ cong (_* n) (sym (*-assoc cE cFE cF)) ⟩
    ((cE * cFE) * cF) * n
  ≡⟨ cong (λ k → (k * cF) * n) (*-comm cE cFE) ⟩
    ((cFE * cE) * cF) * n
  ≡⟨ *-assoc (cFE * cE) cF n ⟩
    (cFE * cE) * (cF * n)
  ∎
  where
  cEF = probNum μ (inter E F)
  cFE = probNum μ (inter F E)
  cE = probNum μ E
  cF = probNum μ F
  n = size μ

-- Positive conditioning makes the product form of independence the same
-- fact as equality of the conditional value with the unconditioned event.
-- Each direction is a function: multiplying by the positive urn size, or
-- cancelling it.
independent-left : {X : Set} (μ : Urn X) (A B : Event X) (hB : 0 < probNum μ B) →
  (Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B)) →
   Equiv (condVal μ A B hB) (probVal μ A))
  ×
  (Equiv (condVal μ A B hB) (probVal μ A) →
   Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B)))
independent-left μ A B hB =
  to-cond , from-cond
  where
  cAB = probNum μ (inter A B)
  cA = probNum μ A
  cB = probNum μ B
  n = size μ
  to-cond : Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B)) →
            Equiv (condVal μ A B hB) (probVal μ A)
  to-cond h =
    *-cancel-≡-right (occupied μ)
      (begin
        (cAB * n) * n
      ≡⟨ *-assoc cAB n n ⟩
        cAB * (n * n)
      ≡⟨ h ⟩
        (cA * cB) * n
      ∎)
  from-cond : Equiv (condVal μ A B hB) (probVal μ A) →
              Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B))
  from-cond h =
    begin
      cAB * (n * n)
    ≡⟨ sym (*-assoc cAB n n) ⟩
      (cAB * n) * n
    ≡⟨ cong (_* n) h ⟩
      (cA * cB) * n
    ∎

-- The same equivalence with the conditional value taken on the other event.
independent-right : {X : Set} (μ : Urn X) (A B : Event X) (hA : 0 < probNum μ A) →
  (Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B)) →
   Equiv (condVal μ B A hA) (probVal μ B))
  ×
  (Equiv (condVal μ B A hA) (probVal μ B) →
   Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B)))
independent-right μ A B hA =
  to-cond , from-cond
  where
  cAB = probNum μ (inter A B)
  cBA = probNum μ (inter B A)
  cA = probNum μ A
  cB = probNum μ B
  n = size μ
  same = count-inter-comm (cells μ) B A
  to-cond : Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B)) →
            Equiv (condVal μ B A hA) (probVal μ B)
  to-cond h =
    begin
      cBA * n
    ≡⟨ cong (_* n) same ⟩
      cAB * n
    ≡⟨ *-cancel-≡-right (occupied μ)
         (begin
           (cAB * n) * n
         ≡⟨ *-assoc cAB n n ⟩
           cAB * (n * n)
         ≡⟨ h ⟩
           (cA * cB) * n
         ∎) ⟩
      cA * cB
    ≡⟨ *-comm cA cB ⟩
      cB * cA
    ∎
  from-cond : Equiv (condVal μ B A hA) (probVal μ B) →
              Equiv (probVal μ (inter A B)) (mul (probVal μ A) (probVal μ B))
  from-cond h =
    begin
      cAB * (n * n)
    ≡⟨ sym (*-assoc cAB n n) ⟩
      (cAB * n) * n
    ≡⟨ cong (λ k → (k * n) * n) (sym same) ⟩
      (cBA * n) * n
    ≡⟨ cong (_* n) h ⟩
      (cB * cA) * n
    ≡⟨ cong (_* n) (*-comm cB cA) ⟩
      (cA * cB) * n
    ∎

-- Conditional independence as a product of conditional values is the same
-- fact as the joint counts satisfying the corresponding product, once the
-- conditioning count is positive. Multiplying or cancelling that count, and
-- the square of the urn size, passes between the two forms.
cond-product : {X : Set} (μ : Urn X) (A B C : Event X) (hC : 0 < probNum μ C) →
  let joint = mul (probVal μ (inter (inter A B) C)) (probVal μ C)
      sides = mul (probVal μ (inter A C)) (probVal μ (inter B C))
      conds = mul (condVal μ A C hC) (condVal μ B C hC)
  in (Equiv joint sides → Equiv (condVal μ (inter A B) C hC) conds)
   × (Equiv (condVal μ (inter A B) C hC) conds → Equiv joint sides)
cond-product μ A B C hC =
  to-cond , from-cond
  where
  cABC = probNum μ (inter (inter A B) C)
  cAC = probNum μ (inter A C)
  cBC = probNum μ (inter B C)
  cC = probNum μ C
  n = size μ
  nn>0 = *-pos (occupied μ) (occupied μ)
  to-cond :
    Equiv (mul (probVal μ (inter (inter A B) C)) (probVal μ C))
          (mul (probVal μ (inter A C)) (probVal μ (inter B C))) →
    Equiv (condVal μ (inter A B) C hC)
          (mul (condVal μ A C hC) (condVal μ B C hC))
  to-cond h =
    begin
      cABC * (cC * cC)
    ≡⟨ sym (*-assoc cABC cC cC) ⟩
      (cABC * cC) * cC
    ≡⟨ cong (_* cC) (*-cancel-≡-right {m = cABC * cC} {n = cAC * cBC} {c = n * n} nn>0
         (begin
           (cABC * cC) * (n * n)
         ≡⟨ h ⟩
           (cAC * cBC) * (n * n)
         ∎)) ⟩
      (cAC * cBC) * cC
    ∎
  from-cond :
    Equiv (condVal μ (inter A B) C hC)
          (mul (condVal μ A C hC) (condVal μ B C hC)) →
    Equiv (mul (probVal μ (inter (inter A B) C)) (probVal μ C))
          (mul (probVal μ (inter A C)) (probVal μ (inter B C)))
  from-cond h =
    begin
      (cABC * cC) * (n * n)
    ≡⟨ cong (_* (n * n))
         (*-cancel-≡-right {m = cABC * cC} {n = cAC * cBC} {c = cC} hC
           (begin
             (cABC * cC) * cC
           ≡⟨ *-assoc cABC cC cC ⟩
             cABC * (cC * cC)
           ≡⟨ h ⟩
             (cAC * cBC) * cC
           ∎)) ⟩
      (cAC * cBC) * (n * n)
    ∎

-- The same product of counts is also the equality of the conditional value
-- given `B` and `C` with the conditional value given only `C`. Conjunction
-- associates, so the triple intersection can be grouped either way.
cond-given : {X : Set} (μ : Urn X) (A B C : Event X)
  (hC : 0 < probNum μ C) (hBC : 0 < probNum μ (inter B C)) →
  let joint = mul (probVal μ (inter (inter A B) C)) (probVal μ C)
      sides = mul (probVal μ (inter A C)) (probVal μ (inter B C))
  in (Equiv joint sides →
      Equiv (condVal μ A (inter B C) hBC) (condVal μ A C hC))
   × (Equiv (condVal μ A (inter B C) hBC) (condVal μ A C hC) →
      Equiv joint sides)
cond-given μ A B C hC hBC =
  to-cond , from-cond
  where
  cABC = probNum μ (inter (inter A B) C)
  cJoin = probNum μ (inter A (inter B C))
  cAC = probNum μ (inter A C)
  cBC = probNum μ (inter B C)
  cC = probNum μ C
  n = size μ
  nn>0 = *-pos (occupied μ) (occupied μ)
  grouped : cJoin ≡ cABC
  grouped = count-cong {xs = cells μ}
    (λ x → sym (∧-assoc (A x) (B x) (C x)))
  to-cond :
    Equiv (mul (probVal μ (inter (inter A B) C)) (probVal μ C))
          (mul (probVal μ (inter A C)) (probVal μ (inter B C))) →
    Equiv (condVal μ A (inter B C) hBC) (condVal μ A C hC)
  to-cond h =
    begin
      cJoin * cC
    ≡⟨ cong (_* cC) grouped ⟩
      cABC * cC
    ≡⟨ *-cancel-≡-right nn>0
         (begin
           (cABC * cC) * (n * n)
         ≡⟨ h ⟩
           (cAC * cBC) * (n * n)
         ∎) ⟩
      cAC * cBC
    ∎
  from-cond :
    Equiv (condVal μ A (inter B C) hBC) (condVal μ A C hC) →
    Equiv (mul (probVal μ (inter (inter A B) C)) (probVal μ C))
          (mul (probVal μ (inter A C)) (probVal μ (inter B C)))
  from-cond h =
    begin
      (cABC * cC) * (n * n)
    ≡⟨ cong (λ k → (k * cC) * (n * n)) (sym grouped) ⟩
      (cJoin * cC) * (n * n)
    ≡⟨ cong (_* (n * n)) h ⟩
      (cAC * cBC) * (n * n)
    ∎
