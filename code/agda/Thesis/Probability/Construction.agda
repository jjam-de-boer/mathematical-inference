module Thesis.Probability.Construction where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
open import Thesis.Fin renaming (zero to fzero; suc to fsuc)
open import Thesis.Probability.Core using (Event; topEvent; false≢true)
import Thesis.Probability.QProb as Q
open Q using (QProb; Equiv; equiv-refl; equiv-sym; equiv-trans; mul;
              mul-congr; mul-one; one-mul; one)
open import Thesis.Probability.FiniteRecord
open FiniteProbRecord

-- A dependent assignment is a telescope of coordinates. The empty telescope
-- is the unit. A longer telescope is the assignment to the earlier
-- coordinates, paired with the value at the last coordinate. The earlier
-- family is named once, so both components of the pair refer to that same
-- family. The telescope inhabits the universe of its coordinate types.

record Unit : Set where
  constructor unit

earlier : {n : ℕ} → (Fin (suc n) → Set) → Fin n → Set
earlier V i = V (castSucc i)

Assign : (n : ℕ) → (Fin n → Set) → Set
Assign zero    _ = Unit
Assign (suc n) V = Assign n (earlier V) × V last

-- Read the value at a coordinate by classifying the coordinate as an earlier
-- place or the last place.
mutual
  lookup : {n : ℕ} {V : Fin n → Set} → Assign n V → (i : Fin n) → V i
  lookup {zero}  unit ()
  lookup {suc n} (front , final) i = read front final i (prefix i)

  read : {n : ℕ} {V : Fin (suc n) → Set} →
    Assign n (earlier V) → V last → (i : Fin (suc n)) → Prefix i → V i
  read front final .(castSucc j) (before j) = lookup front j
  read front final .last          end       = final

prefix-last : ∀ {n} → prefix (last {n}) ≡ end
prefix-last {zero}  = refl
prefix-last {suc n} rewrite prefix-last {n} = refl

prefix-castSucc : ∀ {n} (j : Fin n) → prefix (castSucc j) ≡ before j
prefix-castSucc {zero}  ()
prefix-castSucc {suc n} fzero    = refl
prefix-castSucc {suc n} (fsuc j) rewrite prefix-castSucc j = refl

lookup-last : {n : ℕ} {V : Fin (suc n) → Set}
  (front : Assign n (earlier V)) (final : V last) →
  lookup (front , final) last ≡ final
lookup-last {n} {V} front final =
  cong (read {V = V} front final last) (prefix-last {n})

lookup-castSucc : {n : ℕ} {V : Fin (suc n) → Set}
  (front : Assign n (earlier V)) (final : V last) (j : Fin n) →
  lookup (front , final) (castSucc j) ≡ lookup front j
lookup-castSucc {V = V} front final j =
  cong (read {V = V} front final (castSucc j)) (prefix-castSucc j)

lookup-cong : {n : ℕ} {V : Fin n → Set} {a b : Assign n V} →
  a ≡ b → ∀ i → lookup a i ≡ lookup b i
lookup-cong refl i = refl

-- Agreement at every coordinate is equality of the telescope. The step
-- compares the earlier telescope and the last value, then rebuilds one
-- constructor.
assign-ext : {n : ℕ} {V : Fin n → Set} (a b : Assign n V) →
  (∀ i → lookup a i ≡ lookup b i) → a ≡ b
assign-ext {zero} unit unit _ = refl
assign-ext {suc n} {V} (ae , ah) (be , bh) h =
  trans
    (cong (λ p → (p , ah))
      (assign-ext {n = n} {V = earlier V} ae be (λ j →
        trans (sym (lookup-castSucc {V = V} ae ah j))
          (trans (h (castSucc j)) (lookup-castSucc {V = V} be bh j)))))
    (cong (λ q → (be , q))
      (trans (sym (lookup-last {V = V} ae ah))
        (trans (h last) (lookup-last {V = V} be bh))))

-- Coordinatewise decidable equality decides equality of the telescope.
assign-≟ : {n : ℕ} {V : Fin n → Set} →
  (∀ i → (x y : V i) → Dec (x ≡ y)) →
  (a b : Assign n V) → Dec (a ≡ b)
assign-≟ {zero} _ unit unit = yes refl
assign-≟ {suc n} {V} eq (ae , ah) (be , bh)
  with eq last ah bh | assign-≟ {V = earlier V} (λ i → eq (castSucc i)) ae be
... | yes p | yes q =
  yes (trans (cong (λ r → (r , ah)) q) (cong (λ s → (be , s)) p))
... | yes _ | no nq =
  no (λ e → nq (assign-ext {V = earlier V} ae be (λ j →
    trans (sym (lookup-castSucc {V = V} ae ah j))
      (trans (lookup-cong e (castSucc j)) (lookup-castSucc {V = V} be bh j)))))
... | no np | _ =
  no (λ e → np (trans (sym (lookup-last {V = V} ae ah))
                 (trans (lookup-cong e last) (lookup-last {V = V} be bh))))

-- Membership is preserved by mapping and by concatenating the lists a
-- function returns. Both are the position of the original entry, shifted
-- past the lists that precede it.
∈-map : {A B : Set} {f : A → B} {x : A} {xs : List A} →
  x ∈ xs → f x ∈ map f xs
∈-map here        = here
∈-map (there mem) = there (∈-map mem)

∈-flatMap : {A B : Set} {f : A → List B} {x : A} {y : B} {xs : List A} →
  x ∈ xs → y ∈ f x → y ∈ flatMap f xs
∈-flatMap here        mem = ∈-++ˡ mem
∈-flatMap (there mem) y∈  = ∈-++ʳ _ (∈-flatMap mem y∈)

-- Every way of choosing one listed value at each coordinate. The last
-- coordinate varies in the outer list, and each choice extends an assignment
-- to the earlier coordinates.
enumerate : {n : ℕ} {V : Fin n → Set} →
  (∀ i → List (V i)) → List (Assign n V)
enumerate {zero}  _ = unit ∷ []
enumerate {suc n} {V} values =
  flatMap (λ final →
    map (λ front → (front , final))
      (enumerate {V = earlier V} (λ i → values (castSucc i))))
    (values last)

-- If every coordinate list contains every value of that coordinate, every
-- assignment appears in the enumeration.
enum-complete : {n : ℕ} {V : Fin n → Set}
  (values : ∀ i → List (V i)) →
  (∀ i (x : V i) → x ∈ values i) →
  (a : Assign n V) → a ∈ enumerate values
enum-complete {zero}  _ _ unit = here
enum-complete {suc n} {V} values complete (front , final) =
  ∈-flatMap (complete last final)
    (∈-map
      (enum-complete {V = earlier V} (λ i → values (castSucc i))
        (λ i x → complete (castSucc i) x) front))

-- A rectangular test accepts an assignment when every coordinate test accepts
-- the value stored there. The empty assignment is accepted.
rect : {n : ℕ} {V : Fin n → Set} →
  (∀ i → V i → Bool) → Assign n V → Bool
rect {zero}  _ unit = true
rect {suc n} {V} tests (front , final) =
  tests last final ∧ rect {V = earlier V} (λ i → tests (castSucc i)) front

-- The rectangle holds exactly when every coordinate test holds.
rect-holds : {n : ℕ} {V : Fin n → Set}
  (tests : ∀ i → V i → Bool) (a : Assign n V) →
  (rect tests a ≡ true → ∀ i → tests i (lookup a i) ≡ true)
  × ( (∀ i → tests i (lookup a i) ≡ true) → rect tests a ≡ true )
rect-holds {zero} tests unit =
  (λ _ i → ⊥-elim (no-fin i)) , (λ _ → refl)
rect-holds {suc n} {V} tests (front , final) =
  to-coords , from-coords
  where
  earlier-tests = λ i → tests (castSucc i)
  ∧-left : {b c : Bool} → b ∧ c ≡ true → b ≡ true
  ∧-left {true}  _ = refl
  ∧-left {false} ()
  ∧-right : {b c : Bool} → b ∧ c ≡ true → c ≡ true
  ∧-right {true} {true}  _ = refl
  ∧-right {true} {false} ()
  ∧-right {false}        ()
  ∧-both : {b c : Bool} → b ≡ true → c ≡ true → b ∧ c ≡ true
  ∧-both refl refl = refl
  tail = rect-holds {V = earlier V} earlier-tests front
  to-coords : rect tests (front , final) ≡ true →
              ∀ i → tests i (lookup (front , final) i) ≡ true
  to-coords holds i with prefix i
  ... | end = ∧-left holds
  ... | before j = fst tail (∧-right holds) j
  from-coords : (∀ i → tests i (lookup (front , final) i) ≡ true) →
                rect tests (front , final) ≡ true
  from-coords all =
    ∧-both
      (trans (sym (cong (tests last) (lookup-last {V = V} front final)))
             (all last))
      (snd tail (λ j →
        trans (sym (cong (earlier-tests j) (lookup-castSucc {V = V} front final j)))
              (all (castSucc j))))

-- Pointwise agreement of the stored values is equality of the telescopes, so
-- a rectangular test does not distinguish them.
rect-agree : {n : ℕ} {V : Fin n → Set} (tests : ∀ i → V i → Bool)
  (a b : Assign n V) → (∀ i → lookup a i ≡ lookup b i) →
  rect tests a ≡ rect tests b
rect-agree tests a b h = cong (rect tests) (assign-ext a b h)

-- The rectangle that accepts every value accepts every assignment.
rect-top : {n : ℕ} {V : Fin n → Set} (a : Assign n V) →
  rect (λ _ _ → true) a ≡ true
rect-top {zero} unit = refl
rect-top {suc n} {V} (front , final) =
  cong (true ∧_) (rect-top {V = earlier V} front)

-- Two tests that agree at every coordinate value accept the same assignments.
rect-tests : {n : ℕ} {V : Fin n → Set} {t₁ t₂ : ∀ i → V i → Bool} →
  (∀ i v → t₁ i v ≡ t₂ i v) → (a : Assign n V) → rect t₁ a ≡ rect t₂ a
rect-tests {zero} _ unit = refl
rect-tests {suc n} {V} h (front , final) =
  cong₂ _∧_ (h last final)
    (rect-tests {V = earlier V} (λ i v → h (castSucc i) v) front)

-- The product of natural weights, read from the last coordinate backwards.
-- The empty product is one.
natProduct : {n : ℕ} → (Fin n → ℕ) → ℕ
natProduct {zero}  _ = 1
natProduct {suc n} values =
  values last * natProduct (λ i → values (castSucc i))

-- The same recursion for rational presentations. Equivalence is the
-- cross-multiplication relation, so this product is not a reduced fraction.
qProduct : {n : ℕ} → (Fin n → QProb) → QProb
qProduct {zero}  _ = one
qProduct {suc n} values =
  mul (values last) (qProduct (λ i → values (castSucc i)))

-- Pointwise equivalent factors give equivalent products. The factors are
-- not identified as functions; each coordinate is used once.
qProduct-cong : {n : ℕ} {left right : Fin n → QProb} →
  (∀ i → Equiv (left i) (right i)) →
  Equiv (qProduct left) (qProduct right)
qProduct-cong {zero} _ = equiv-refl one
qProduct-cong {suc n} {left} {right} h =
  mul-congr {p = left last} {p' = right last}
            {q = qProduct (λ i → left (castSucc i))}
            {q' = qProduct (λ i → right (castSucc i))}
    (h last)
    (qProduct-cong {n = n}
      {left = λ i → left (castSucc i)}
      {right = λ i → right (castSucc i)}
      (λ i → h (castSucc i)))

-- A product of unit presentations is the unit presentation.
qProduct-one : ∀ n → Equiv (qProduct {n = n} (λ _ → one)) one
qProduct-one zero = equiv-refl one
qProduct-one (suc n) =
  equiv-trans {p = mul one (qProduct {n = n} (λ _ → one))}
              {q = mul one one}
              {r = one}
    (mul-congr {p = one} {p' = one}
               {q = qProduct {n = n} (λ _ → one)} {q' = one}
       (equiv-refl one) (qProduct-one n))
    (one-mul one)

-- An earlier coordinate is not the last coordinate.
castSucc-≢-last : ∀ {n} (i : Fin n) → castSucc i ≢ last {n}
castSucc-≢-last {zero} ()
castSucc-≢-last {suc n} fzero ()
castSucc-≢-last {suc n} (fsuc i) eq = castSucc-≢-last i (suc-injective eq)

-- The Boolean decided by coordinate identity.
sameCoord : ∀ {n} → Fin n → Fin n → Bool
sameCoord i j = fromDec (fin-≟ i j)

-- Select one rational at a chosen coordinate and place the unit presentation
-- at every other coordinate.
pick : ∀ {n} → Fin n → QProb → Fin n → QProb
pick chosen selected i = if sameCoord i chosen then selected else one

equiv-of-≡ : {p q : QProb} → p ≡ q → Equiv p q
equiv-of-≡ {p} refl = equiv-refl p

-- Comparing a coordinate with itself accepts the selected presentation.
pick-here : ∀ {n} (i : Fin n) (selected : QProb) → pick i selected i ≡ selected
pick-here i selected with fin-≟ i i
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

-- Successor preserves the Boolean of coordinate identity, because the
-- decision procedure steps under one successor on both sides together.
sameCoord-suc : ∀ {n} (i j : Fin n) →
  sameCoord (fsuc i) (fsuc j) ≡ sameCoord i j
sameCoord-suc i j with fin-≟ i j
... | yes _ = refl
... | no _ = refl

-- Embedding both coordinates preserves that Boolean as well.
fromDec-castSucc : ∀ {n} (i j : Fin n) →
  sameCoord (castSucc i) (castSucc j) ≡ sameCoord i j
fromDec-castSucc {zero} () ()
fromDec-castSucc {suc n} fzero fzero = refl
fromDec-castSucc {suc n} fzero (fsuc _) = refl
fromDec-castSucc {suc n} (fsuc _) fzero = refl
fromDec-castSucc {suc n} (fsuc i) (fsuc j) =
  begin
    sameCoord (castSucc (fsuc i)) (castSucc (fsuc j))
  ≡⟨ sameCoord-suc (castSucc i) (castSucc j) ⟩
    sameCoord (castSucc i) (castSucc j)
  ≡⟨ fromDec-castSucc i j ⟩
    sameCoord i j
  ≡⟨ sym (sameCoord-suc i j) ⟩
    sameCoord (fsuc i) (fsuc j)
  ∎

-- An earlier coordinate is never the one selected at the last place, so the
-- last factor of that product is the unit presentation.
pick-off-last : ∀ {n} (i : Fin n) (selected : QProb) →
  pick (last {n}) selected (castSucc i) ≡ one
pick-off-last i selected with fin-≟ (castSucc i) last
... | yes eq = ⊥-elim (castSucc-≢-last i eq)
... | no _ = refl

-- The last coordinate is never an earlier one.
pick-off-cast : ∀ {n} (j : Fin n) (selected : QProb) →
  pick (castSucc j) selected (last {n}) ≡ one
pick-off-cast j selected with fin-≟ last (castSucc j)
... | yes eq = ⊥-elim (castSucc-≢-last j (sym eq))
... | no _ = refl

-- Embedding both sides of a coordinate comparison does not change the
-- selected presentation.
pick-along : ∀ {n} (j i : Fin n) (selected : QProb) →
  pick (castSucc j) selected (castSucc i) ≡ pick j selected i
pick-along j i selected rewrite fromDec-castSucc i j = refl

-- Selection at the last coordinate leaves a unit product on the earlier
-- coordinates, and the unit product cancels.
singleton-last : ∀ {n} (selected : QProb) →
  Equiv (qProduct {n = suc n} (pick (last {n}) selected)) selected
singleton-last {n} selected =
  equiv-trans
    {p = qProduct {n = suc n} (pick (last {n}) selected)}
    {q = mul selected (qProduct {n = n} (λ _ → one))}
    {r = selected}
    (mul-congr
      {p = pick (last {n}) selected (last {n})} {p' = selected}
      {q = qProduct {n = n} (λ i → pick (last {n}) selected (castSucc i))}
      {q' = qProduct {n = n} (λ _ → one)}
      (equiv-of-≡ (pick-here (last {n}) selected))
      (qProduct-cong {n = n}
        {left = λ i → pick (last {n}) selected (castSucc i)}
        {right = λ _ → one}
        (λ i → equiv-of-≡ (pick-off-last i selected))))
    (equiv-trans
      {p = mul selected (qProduct {n = n} (λ _ → one))}
      {q = mul selected one}
      {r = selected}
      (mul-congr {p = selected} {p' = selected}
        {q = qProduct {n = n} (λ _ → one)} {q' = one}
        (equiv-refl selected) (qProduct-one n))
      (mul-one selected))

-- Selection at an earlier coordinate leaves a unit at the last place. The
-- earlier product is the same selection, one coordinate shorter. The two
-- statements call each other: shortening the coordinate bound is the
-- recursive step.
mutual
  singleton-earlier : ∀ {n} (j : Fin n) (selected : QProb) →
    Equiv (qProduct {n = suc n} (pick (castSucc j) selected)) selected
  singleton-earlier {n} j selected =
    equiv-trans
      {p = qProduct {n = suc n} (pick (castSucc j) selected)}
      {q = mul one (qProduct {n = n} (pick j selected))}
      {r = selected}
      (mul-congr
        {p = pick (castSucc j) selected (last {n})} {p' = one}
        {q = qProduct {n = n} (λ i → pick (castSucc j) selected (castSucc i))}
        {q' = qProduct {n = n} (pick j selected)}
        (equiv-of-≡ (pick-off-cast j selected))
        (qProduct-cong {n = n}
          {left = λ i → pick (castSucc j) selected (castSucc i)}
          {right = pick j selected}
          (λ i → equiv-of-≡ (pick-along j i selected))))
      (equiv-trans
        {p = mul one (qProduct {n = n} (pick j selected))}
        {q = qProduct {n = n} (pick j selected)}
        {r = selected}
        (one-mul (qProduct {n = n} (pick j selected)))
        (qProduct-singleton j selected))

-- The product that is selected at one coordinate and unit elsewhere is the
-- selected presentation. The other coordinates contribute the unit, which
-- multiplication cancels. The coordinate is classified by the same recursion
-- that builds the product, so each case is an equality of presentations.
  qProduct-singleton : {n : ℕ} (chosen : Fin n) (selected : QProb) →
    Equiv (qProduct {n = n} (pick chosen selected)) selected
  qProduct-singleton {zero} () _
  qProduct-singleton {suc n} chosen selected = by-prefix (prefix chosen)
    where
    by-prefix : (p : Prefix chosen) →
      Equiv (qProduct {n = suc n} (pick chosen selected)) selected
    by-prefix end = singleton-last {n} selected
    by-prefix (before j) = singleton-earlier {n} j selected

-- The common denominator of a coordinatewise family of records is the
-- product of the denominators. The empty family contributes the unit
-- denominator.
denominator : {n : ℕ} {V : Fin n → Set} →
  (∀ i → FiniteProbRecord (V i)) → ℕ
denominator {zero} _ = 1
denominator {suc n} {V} factors =
  den (factors last) * denominator {V = earlier V} (λ i → factors (castSucc i))

-- Every factor denominator is positive, and a product of positive natural
-- numbers is positive. The unit denominator is positive as well.
denominator-pos : {n : ℕ} {V : Fin n → Set}
  (factors : ∀ i → FiniteProbRecord (V i)) → 0 < denominator factors
denominator-pos {zero} _ = s≤s z≤n
denominator-pos {suc n} {V} factors =
  *-pos (den-pos (factors last))
    (denominator-pos {V = earlier V} (λ i → factors (castSucc i)))

-- Turn a last-coordinate value and an earlier assignment into one telescope.
extend : {n : ℕ} {V : Fin (suc n) → Set} →
  V last × Assign n (earlier V) → Assign (suc n) V
extend (final , front) = front , final

-- Weighted atoms of the independent product. The empty product has one atom,
-- of weight one. A longer product keeps every pair of a last-coordinate atom
-- and an earlier atom, including pairs whose weight is zero, and retags the
-- pair as one telescope.
jointAtoms : {n : ℕ} {V : Fin n → Set} →
  (∀ i → FiniteProbRecord (V i)) → List (Assign n V × ℕ)
jointAtoms {zero} _ = (unit , 1) ∷ []
jointAtoms {suc n} {V = V} factors =
  map (relabel (extend {V = V}))
    (weightedCartesian (atoms (factors (last {n})))
      (jointAtoms {n = n} {V = earlier V} (λ i → factors (castSucc i))))

-- The total weight is the product of the denominators. Zero-weight atoms
-- contribute zero and do not change the product.
joint-total : {n : ℕ} {V : Fin n → Set}
  (factors : ∀ i → FiniteProbRecord (V i)) →
  totalMass (jointAtoms factors) ≡ denominator factors
joint-total {zero} _ = refl
joint-total {suc n} {V = V} factors =
  let prefixFactors = λ i → factors (castSucc i)
      frontAtoms = jointAtoms {n = n} {V = earlier V} prefixFactors
      cart = weightedCartesian (atoms (factors (last {n}))) frontAtoms
  in
  begin
    totalMass (jointAtoms {n = suc n} {V = V} factors)
  ≡⟨ totalMass-map-labels cart (extend {n = n} {V = V}) ⟩
    totalMass cart
  ≡⟨ totalMass-weightedCartesian (atoms (factors (last {n}))) frontAtoms ⟩
    totalMass (atoms (factors (last {n}))) * totalMass frontAtoms
  ≡⟨ cong₂ _*_ (total (factors (last {n})))
       (joint-total {n = n} {V = earlier V} prefixFactors) ⟩
    den (factors (last {n})) * denominator {n = n} {V = earlier V} prefixFactors
  ∎

-- Mass of a rectangle on the product atoms. It is the product of the
-- coordinate masses: each coordinate contributes only through its own test.
joint-split : {n : ℕ} {V : Fin (suc n) → Set}
  (factors : ∀ i → FiniteProbRecord (V i))
  (tests : ∀ i → V i → Bool) →
  eventMass (jointAtoms factors) (rect tests) ≡
  eventMass (atoms (factors last)) (tests last) *
  eventMass (jointAtoms {V = earlier V} (λ i → factors (castSucc i)))
    (rect (λ i → tests (castSucc i)))
joint-split {n} {V = V} factors tests =
  let earlierTests = λ i → tests (castSucc i)
      frontAtoms = jointAtoms {n = n} {V = earlier V} (λ i → factors (castSucc i))
      cart = weightedCartesian (atoms (factors (last {n}))) frontAtoms
  in
  trans (eventMass-map-labels cart (extend {n = n} {V = V}) (rect {n = suc n} {V = V} tests))
        (eventMass-weightedCartesian (atoms (factors (last {n}))) frontAtoms
           (tests (last {n})) (rect {n = n} {V = earlier V} earlierTests))

joint-event : {n : ℕ} {V : Fin n → Set}
  (factors : ∀ i → FiniteProbRecord (V i))
  (tests : ∀ i → V i → Bool) →
  eventMass (jointAtoms factors) (rect tests) ≡
  natProduct (λ i → eventMass (atoms (factors i)) (tests i))
joint-event {zero} _ _ = refl
joint-event {suc n} {V} factors tests =
  trans (joint-split factors tests)
    (cong (eventMass (atoms (factors last)) (tests last) *_)
      (joint-event {V = earlier V} (λ i → factors (castSucc i))
        (λ i → tests (castSucc i))))

-- The independent product record. Its denominator is the product of the
-- factor denominators, and its atoms are the weighted pairs above. A factor
-- that lists no positive mass still yields no positive product mass.
productRecord : {n : ℕ} {V : Fin n → Set} →
  (∀ i → FiniteProbRecord (V i)) → FiniteProbRecord (Assign n V)
productRecord factors =
  finiteRecord (jointAtoms factors) (denominator factors)
    (denominator-pos factors) (joint-total factors)

-- The probability of a rectangle is the product of the coordinate
-- probabilities.
record-rect : {n : ℕ} {V : Fin n → Set}
  (factors : ∀ i → FiniteProbRecord (V i))
  (tests : ∀ i → V i → Bool) →
  Equiv (probVal (productRecord factors) (rect tests))
        (qProduct (λ i → probVal (factors i) (tests i)))
record-rect {zero} factors tests =
  equiv-refl (probVal (productRecord factors) (rect tests))
record-rect {suc n} {V} factors tests =
  equiv-trans {p = probVal (productRecord factors) (rect tests)}
              {q = mul (probVal (factors last) (tests last))
                       (probVal (productRecord prefixFactors) (rect prefixTests))}
              {r = qProduct (λ i → probVal (factors i) (tests i))}
    (cong (_* Q.den coupled) (joint-split factors tests))
    (mul-congr {p = probVal (factors last) (tests last)}
               {p' = probVal (factors last) (tests last)}
               {q = probVal (productRecord prefixFactors) (rect prefixTests)}
               {q' = qProduct (λ i → probVal (prefixFactors i) (prefixTests i))}
       (equiv-refl (probVal (factors last) (tests last)))
       (record-rect prefixFactors prefixTests))
  where
  prefixFactors = λ i → factors (castSucc i)
  prefixTests = λ i → tests (castSucc i)
  coupled = mul (probVal (factors last) (tests last))
                (probVal (productRecord prefixFactors) (rect prefixTests))

-- Apply a coordinate decision. A positive decision transports the value
-- along the coordinate identity and reads the selected test. A negative
-- decision accepts the value. The decision is an argument, so each case
-- computes.
coordTest : {n : ℕ} {V : Fin n → Set} (chosen : Fin n)
  (event : V chosen → Bool) (i : Fin n) →
  Dec (i ≡ chosen) → V i → Bool
coordTest {V = V} chosen event i (yes eq) value = event (subst V eq value)
coordTest chosen event i (no _) _ = true

-- The test that reads one coordinate and accepts every value at the others.
atCoord : {n : ℕ} {V : Fin n → Set} (chosen : Fin n) →
  (V chosen → Bool) → ∀ i → V i → Bool
atCoord chosen event i value = coordTest chosen event i (fin-≟ i chosen) value
