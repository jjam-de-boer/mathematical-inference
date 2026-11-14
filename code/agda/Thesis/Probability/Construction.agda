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
import Thesis.Probability.Urn as Urn

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
-- to the earlier coordinates. The row map is named so membership can be
-- inverted without rebuilding the family.
mutual
  enumerate : {n : ℕ} {V : Fin n → Set} →
    (∀ i → List (V i)) → List (Assign n V)
  enumerate {zero}  _ = unit ∷ []
  enumerate {suc n} {V} values =
    flatMap (enum-row {n = n} {V = V} values) (values last)

  enum-row : {n : ℕ} {V : Fin (suc n) → Set} →
    (∀ i → List (V i)) → V last → List (Assign (suc n) V)
  enum-row {n} {V} values final =
    map (λ front → (front , final))
      (enumerate {n = n} {V = earlier V} (λ i → values (castSucc i)))

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

-- Invert a mapped list: the image came from one listed source, and the
-- mapping equation is data.
record MapHit {A B : Set} (f : A → B) (y : B) (xs : List A) : Set where
  constructor mapped
  field
    source : A
    member : source ∈ xs
    image  : f source ≡ y

∈-map-inv : {A B : Set} (f : A → B) {y : B} {xs : List A} →
  y ∈ map f xs → MapHit f y xs
∈-map-inv f {xs = []} ()
∈-map-inv f {xs = x ∷ _} here = mapped x here refl
∈-map-inv f {xs = _ ∷ xs} (there mem) with ∈-map-inv f mem
... | mapped source member image = mapped source (there member) image

record FlatHit {A B : Set} (f : A → List B) (y : B) (xs : List A) : Set where
  constructor flattened
  field
    source : A
    member : source ∈ xs
    inner  : y ∈ f source

∈-flatMap-inv : {A B : Set} (f : A → List B) {y : B} {xs : List A} →
  y ∈ flatMap f xs → FlatHit f y xs
∈-flatMap-inv f {xs = []} ()
∈-flatMap-inv f {xs = x ∷ xs} mem with ∈-++ (f x) (flatMap f xs) mem
... | inl inHead = flattened x here inHead
... | inr later with ∈-flatMap-inv f later
... | flattened source member inner = flattened source (there member) inner

-- A listed successor assignment is one last-coordinate value from that
-- coordinate's list, paired with a listed earlier assignment. Both positions
-- are data, so a later coordinate is read from those positions rather than
-- from an existence proof.
record EnumParts {n : ℕ} {V : Fin (suc n) → Set}
    (values : ∀ i → List (V i)) (a : Assign (suc n) V) : Set where
  constructor parts
  field
    front  : Assign n (earlier V)
    final  : V last
    path   : a ≡ (front , final)
    front∈ : front ∈ enumerate {n = n} {V = earlier V} (λ i → values (castSucc i))
    final∈ : final ∈ values last

enum-parts : {n : ℕ} {V : Fin (suc n) → Set}
  (values : ∀ i → List (V i)) (a : Assign (suc n) V) →
  a ∈ enumerate values → EnumParts values a
enum-parts {n} {V} values a mem =
  from-flat (∈-flatMap-inv (enum-row {n = n} {V = V} values)
    {xs = values last} mem)
  where
  from-flat : FlatHit (enum-row {n = n} {V = V} values) a (values last) →
              EnumParts values a
  from-flat (flattened final final∈ inRow) =
    from-map (∈-map-inv (λ front → (front , final)) inRow)
    where
    from-map : MapHit (λ front → (front , final)) a
                 (enumerate {n = n} {V = earlier V} (λ i → values (castSucc i))) →
               EnumParts values a
    from-map (mapped front front∈ image) =
      parts front final (sym image) front∈ final∈

-- Every coordinate of a listed assignment comes from that coordinate's list.
enum-coord : {n : ℕ} {V : Fin n → Set}
  (values : ∀ i → List (V i)) (a : Assign n V) →
  a ∈ enumerate values → (i : Fin n) → lookup a i ∈ values i
enum-coord {zero} _ _ _ ()
enum-coord {suc n} {V} values a mem i =
  from-parts (enum-parts {n = n} {V = V} values a mem) i
  where
  from-parts : EnumParts values a → (i : Fin (suc n)) → lookup a i ∈ values i
  from-parts (parts front final path front∈ final∈) i =
    subst (λ a₀ → lookup a₀ i ∈ values i) (sym path) (at (prefix i))
    where
    at : Prefix i → lookup (front , final) i ∈ values i
    at end =
      subst (_∈ values last) (sym (lookup-last {V = V} front final)) final∈
    at (before j) =
      subst (_∈ values (castSucc j))
        (sym (lookup-castSucc {V = V} front final j))
        (enum-coord {n = n} {V = earlier V}
          (λ k → values (castSucc k)) front front∈ j)

-- The Boolean that is true exactly at the last coordinate, or exactly at an
-- earlier coordinate, is computed by classifying both places. No value is
-- transported along a coordinate identity: when both classifications are
-- `end`, the stored value already has the last-coordinate type.
oneCoord : {n : ℕ} {V : Fin n → Set} (chosen : Fin n) →
  (V chosen → Bool) → ∀ i → V i → Bool
oneCoord {zero} chosen event i value = ⊥-elim (no-fin chosen)
oneCoord {suc n} {V} chosen event i value with prefix chosen | prefix i
... | end       | end       = event value
... | end       | before _  = true
... | before _  | end       = true
... | before j  | before k  = oneCoord {V = earlier V} j event k value

∧-true : ∀ b → b ∧ true ≡ b
∧-true true  = refl
∧-true false = refl

-- The last-coordinate classification is `end`, so the one-coordinate test
-- reads the last value there and accepts every earlier value.
one-last-here : {n : ℕ} {V : Fin (suc n) → Set}
  (event : V last → Bool) (value : V last) →
  oneCoord {n = suc n} {V = V} last event last value ≡ event value
one-last-here {n} {V} event value rewrite prefix-last {n} = refl

one-last-else : {n : ℕ} {V : Fin (suc n) → Set}
  (event : V last → Bool) (j : Fin n) (value : V (castSucc j)) →
  oneCoord {n = suc n} {V = V} last event (castSucc j) value ≡ true
one-last-else {n} {V} event j value rewrite prefix-last {n} | prefix-castSucc j = refl

one-cast-last : {n : ℕ} {V : Fin (suc n) → Set} (j : Fin n)
  (event : V (castSucc j) → Bool) (value : V last) →
  oneCoord {n = suc n} {V = V} (castSucc j) event last value ≡ true
one-cast-last {n} {V} j event value rewrite prefix-castSucc j | prefix-last {n} = refl

one-cast-cast : {n : ℕ} {V : Fin (suc n) → Set} (j k : Fin n)
  (event : V (castSucc j) → Bool) (value : V (castSucc k)) →
  oneCoord {n = suc n} {V = V} (castSucc j) event (castSucc k) value ≡
  oneCoord {n = n} {V = earlier V} j event k value
one-cast-cast {n} {V} j k event value
  rewrite prefix-castSucc j | prefix-castSucc k = refl

-- A one-coordinate rectangle is the test at that coordinate of the telescope.
rect-one : {n : ℕ} {V : Fin n → Set} (chosen : Fin n)
  (event : V chosen → Bool) (a : Assign n V) →
  rect (oneCoord chosen event) a ≡ event (lookup a chosen)
rect-one {zero} ()
rect-one {suc n} {V} chosen event (front , final) = step (prefix chosen)
  where
  step : (p : Prefix chosen) →
    rect (oneCoord chosen event) (front , final) ≡
    event (lookup (front , final) chosen)
  step end =
    begin
      oneCoord {n = suc n} {V = V} last event last final ∧
        rect {n = n} {V = earlier V}
          (λ i → oneCoord {n = suc n} {V = V} last event (castSucc i)) front
    ≡⟨ cong₂ _∧_
         (one-last-here {n} {V} event final)
         (trans (rect-tests {n = n} {V = earlier V}
                  (λ i v → one-last-else {n} {V} event i v) front)
                (rect-top {n = n} {V = earlier V} front)) ⟩
      event final ∧ true
    ≡⟨ ∧-true (event final) ⟩
      event final
    ≡⟨ cong event (sym (lookup-last {n} {V} front final)) ⟩
      event (lookup {n = suc n} {V = V} (front , final) (last {n}))
    ∎
  step (before j) =
    begin
      oneCoord {n = suc n} {V = V} (castSucc j) event last final ∧
        rect {n = n} {V = earlier V}
          (λ i → oneCoord {n = suc n} {V = V} (castSucc j) event (castSucc i))
          front
    ≡⟨ cong₂ _∧_
         (one-cast-last {n} {V} j event final)
         (rect-tests {n = n} {V = earlier V}
           (λ i v → one-cast-cast {n} {V} j i event v) front) ⟩
      true ∧ rect {n = n} {V = earlier V}
        (oneCoord {n = n} {V = earlier V} j event) front
    ≡⟨ rect-one {n = n} {V = earlier V} j event front ⟩
      event (lookup front j)
    ≡⟨ cong event (sym (lookup-castSucc {n} {V} front final j)) ⟩
      event (lookup {n = suc n} {V = V} (front , final) (castSucc j))
    ∎

-- The product of coordinate probabilities for a one-coordinate family is the
-- chosen coordinate's probability. Earlier (or later) coordinates contribute
-- the certain event, hence the unit presentation, which multiplication
-- cancels.
qProduct-oneCoord : {n : ℕ} {V : Fin n → Set}
  (factors : ∀ i → FiniteProbRecord (V i))
  (chosen : Fin n) (event : V chosen → Bool) →
  Equiv (qProduct {n = n}
          (λ i → probVal (factors i) (oneCoord {n = n} {V = V} chosen event i)))
        (probVal (factors chosen) event)
qProduct-oneCoord {zero} _ () _
qProduct-oneCoord {suc n} {V} factors chosen event = step (prefix chosen)
  where
  tests = oneCoord {n = suc n} {V = V} chosen event
  step : (p : Prefix chosen) →
    Equiv (qProduct {n = suc n}
            (λ i → probVal (factors i) (tests i)))
          (probVal (factors chosen) event)
  step end =
    equiv-trans
      {p = qProduct {n = suc n}
            (λ i → probVal (factors i)
              (oneCoord {n = suc n} {V = V} last event i))}
      {q = mul (probVal (factors last) event)
               (qProduct {n = n} (λ _ → one))}
      {r = probVal (factors last) event}
      (mul-congr
        {p = probVal (factors last)
              (oneCoord {n = suc n} {V = V} last event last)}
        {p' = probVal (factors last) event}
        {q = qProduct {n = n}
              (λ i → probVal (factors (castSucc i))
                (oneCoord {n = suc n} {V = V} last event (castSucc i)))}
        {q' = qProduct {n = n} (λ _ → one)}
        (probVal-cong (factors last)
          (oneCoord {n = suc n} {V = V} last event last) event
          (λ v → one-last-here {n} {V} event v))
        (qProduct-cong {n = n}
          {left = λ i → probVal (factors (castSucc i))
                          (oneCoord {n = suc n} {V = V} last event (castSucc i))}
          {right = λ _ → one}
          (λ i →
            equiv-trans
              {p = probVal (factors (castSucc i))
                    (oneCoord {n = suc n} {V = V} last event (castSucc i))}
              {q = probVal (factors (castSucc i)) topEvent}
              {r = one}
              (probVal-cong (factors (castSucc i))
                (oneCoord {n = suc n} {V = V} last event (castSucc i))
                topEvent
                (λ v → one-last-else {n} {V} event i v))
              (normalization (factors (castSucc i))))))
      (equiv-trans
        {p = mul (probVal (factors last) event)
                 (qProduct {n = n} (λ _ → one))}
        {q = mul (probVal (factors last) event) one}
        {r = probVal (factors last) event}
        (mul-congr {p = probVal (factors last) event}
                   {p' = probVal (factors last) event}
                   {q = qProduct {n = n} (λ _ → one)} {q' = one}
          (equiv-refl (probVal (factors last) event)) (qProduct-one n))
        (mul-one (probVal (factors last) event)))
  step (before j) =
    equiv-trans
      {p = qProduct {n = suc n}
            (λ i → probVal (factors i)
              (oneCoord {n = suc n} {V = V} (castSucc j) event i))}
      {q = mul one
            (qProduct {n = n}
              (λ i → probVal (factors (castSucc i))
                (oneCoord {n = n} {V = earlier V} j event i)))}
      {r = probVal (factors (castSucc j)) event}
      (mul-congr
        {p = probVal (factors last)
              (oneCoord {n = suc n} {V = V} (castSucc j) event last)}
        {p' = one}
        {q = qProduct {n = n}
              (λ i → probVal (factors (castSucc i))
                (oneCoord {n = suc n} {V = V} (castSucc j) event (castSucc i)))}
        {q' = qProduct {n = n}
              (λ i → probVal (factors (castSucc i))
                (oneCoord {n = n} {V = earlier V} j event i))}
        (equiv-trans
          {p = probVal (factors last)
                (oneCoord {n = suc n} {V = V} (castSucc j) event last)}
          {q = probVal (factors last) topEvent}
          {r = one}
          (probVal-cong (factors last)
            (oneCoord {n = suc n} {V = V} (castSucc j) event last)
            topEvent
            (λ v → one-cast-last {n} {V} j event v))
          (normalization (factors last)))
        (qProduct-cong {n = n}
          {left = λ i → probVal (factors (castSucc i))
                          (oneCoord {n = suc n} {V = V}
                            (castSucc j) event (castSucc i))}
          {right = λ i → probVal (factors (castSucc i))
                           (oneCoord {n = n} {V = earlier V} j event i)}
          (λ i →
            probVal-cong (factors (castSucc i))
              (oneCoord {n = suc n} {V = V} (castSucc j) event (castSucc i))
              (oneCoord {n = n} {V = earlier V} j event i)
              (λ v → one-cast-cast {n} {V} j i event v))))
      (equiv-trans
        {p = mul one
              (qProduct {n = n}
                (λ i → probVal (factors (castSucc i))
                  (oneCoord {n = n} {V = earlier V} j event i)))}
        {q = qProduct {n = n}
              (λ i → probVal (factors (castSucc i))
                (oneCoord {n = n} {V = earlier V} j event i))}
        {r = probVal (factors (castSucc j)) event}
        (one-mul (qProduct {n = n}
                   (λ i → probVal (factors (castSucc i))
                     (oneCoord {n = n} {V = earlier V} j event i))))
        (qProduct-oneCoord {n = n} {V = earlier V}
          (λ i → factors (castSucc i)) j event))

-- A coordinate of the independent product has the marginal law declared by
-- that coordinate's record.
coordinate-prob : {n : ℕ} {V : Fin n → Set}
  (factors : ∀ i → FiniteProbRecord (V i))
  (chosen : Fin n) (event : V chosen → Bool) →
  Equiv (probVal (productRecord factors) (λ a → event (lookup a chosen)))
        (probVal (factors chosen) event)
coordinate-prob {n} {V} factors chosen event =
  equiv-trans
    {p = probVal (productRecord factors) (λ a → event (lookup a chosen))}
    {q = probVal (productRecord factors)
          (rect (oneCoord {n = n} {V = V} chosen event))}
    {r = probVal (factors chosen) event}
    (probVal-cong (productRecord factors)
      (λ a → event (lookup a chosen))
      (rect (oneCoord {n = n} {V = V} chosen event))
      (λ a → sym (rect-one {n = n} {V = V} chosen event a)))
    (equiv-trans
      {p = probVal (productRecord factors)
            (rect (oneCoord {n = n} {V = V} chosen event))}
      {q = qProduct {n = n}
            (λ i → probVal (factors i)
              (oneCoord {n = n} {V = V} chosen event i))}
      {r = probVal (factors chosen) event}
      (record-rect {n = n} {V = V} factors
        (oneCoord {n = n} {V = V} chosen event))
      (qProduct-oneCoord {n = n} {V = V} factors chosen event))

-- The homogeneous specialisation: every coordinate shares one outcome type.
coordinate-prob-const : {n : ℕ} {A : Set}
  (factors : Fin n → FiniteProbRecord A)
  (chosen : Fin n) (event : A → Bool) →
  Equiv (probVal (productRecord {V = λ _ → A} factors)
          (λ a → event (lookup a chosen)))
        (probVal (factors chosen) event)
coordinate-prob-const {A = A} factors chosen event =
  coordinate-prob {V = λ _ → A} factors chosen event

-- Keep the first occurrence of each value. Later copies are dropped, so the
-- resulting list has no duplicates and still contains every original value.
dedup : {A : Set} (eq : (x y : A) → Dec (x ≡ y)) → List A → List A
dedup eq [] = []
dedup eq (x ∷ xs) with ∈-dec eq x (dedup eq xs)
... | yes _ = dedup eq xs
... | no  _ = x ∷ dedup eq xs

mem-dedup-to : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (x : A) (xs : List A) → x ∈ dedup eq xs → x ∈ xs
mem-dedup-to eq x (y ∷ ys) mem with ∈-dec eq y (dedup eq ys)
... | yes _ = there (mem-dedup-to eq x ys mem)
... | no _ = cons-case mem
  where
  cons-case : x ∈ y ∷ dedup eq ys → x ∈ y ∷ ys
  cons-case here        = here
  cons-case (there later) = there (mem-dedup-to eq x ys later)

mem-dedup-from : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (x : A) (xs : List A) → x ∈ xs → x ∈ dedup eq xs
mem-dedup-from eq x (y ∷ ys) mem with ∈-dec eq y (dedup eq ys)
... | yes y∈ = from-tail mem
  where
  from-tail : x ∈ y ∷ ys → x ∈ dedup eq ys
  from-tail here        = y∈
  from-tail (there later) = mem-dedup-from eq x ys later
... | no y∉ = from-cons mem
  where
  from-cons : x ∈ y ∷ ys → x ∈ y ∷ dedup eq ys
  from-cons here        = here
  from-cons (there later) = there (mem-dedup-from eq x ys later)

dedup-nodup : {A : Set} (eq : (x y : A) → Dec (x ≡ y)) (xs : List A) →
  Nodup (dedup eq xs)
dedup-nodup eq [] = Nodup.[]
dedup-nodup eq (x ∷ xs) with ∈-dec eq x (dedup eq xs)
... | yes _ = dedup-nodup eq xs
... | no x∉ = x∉ ∷ dedup-nodup eq xs

-- The first occurrence of a listed value, as a position below the length.
idxOf : {A : Set} (eq : (x y : A) → Dec (x ≡ y)) (x : A) (xs : List A) → ℕ
idxOf eq x [] = 0
idxOf eq x (y ∷ ys) with eq x y
... | yes _ = 0
... | no  _ = suc (idxOf eq x ys)

-- A listed head that differs from the needle is not the occurrence; the
-- search continues in the tail.
drop-here : {A : Set} {x y : A} {ys : List A} → x ≢ y → x ∈ y ∷ ys → x ∈ ys
drop-here ne here        = ⊥-elim (ne refl)
drop-here _  (there later) = later

idxOf-< : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (x : A) (xs : List A) → x ∈ xs → idxOf eq x xs < length xs
idxOf-< eq x (y ∷ ys) mem with eq x y
... | yes _ = s≤s z≤n
... | no ne = s≤s (idxOf-< eq x ys (drop-here ne mem))

get-idxOf : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (x : A) (xs : List A) (mem : x ∈ xs) →
  get xs (fromℕ< (idxOf eq x xs) (idxOf-< eq x xs mem)) ≡ x
get-idxOf eq x (y ∷ ys) mem with eq x y
... | yes p = sym p
... | no ne = get-idxOf eq x ys (drop-here ne mem)

get-∈ : {A : Set} (xs : List A) (i : Fin (length xs)) → get xs i ∈ xs
get-∈ (x ∷ xs) fzero    = here
get-∈ (x ∷ xs) (fsuc i) = there (get-∈ xs i)

-- On a duplicate-free list, the position of the value stored at a coordinate
-- is that coordinate's underlying natural number.
idxOf-get : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (xs : List A) → Nodup xs → (i : Fin (length xs)) →
  idxOf eq (get xs i) xs ≡ toℕ i
idxOf-get eq (x ∷ xs) (x∉ ∷ nd) fzero with eq x x
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)
idxOf-get eq (x ∷ xs) (x∉ ∷ nd) (fsuc i) with eq (get xs i) x
... | yes p = ⊥-elim (x∉ (subst (_∈ xs) p (get-∈ xs i)))
... | no  _ = cong suc (idxOf-get eq xs nd i)

-- An explicit finite presentation: every value has a coordinate code, and
-- every coordinate decodes to a value, as inverse constructions. The
-- membership proof used to build a code is not part of the identity of the
-- value.
record FiniteWitness (X : Set) : Set where
  field
    card          : ℕ
    encode        : X → Fin card
    decode        : Fin card → X
    decode-encode : ∀ x → decode (encode x) ≡ x
    encode-decode : ∀ i → encode (decode i) ≡ i

open FiniteWitness public

-- A duplicate-free exhaustive listing is such a presentation. The encoder
-- stores the first occurrence; the decoder reads that cell.
ofList : {X : Set} (eq : (x y : X) → Dec (x ≡ y))
  (values : List X) → (∀ x → x ∈ values) → Nodup values → FiniteWitness X
ofList eq values complete nodup = record
  { card = length values
  ; encode = λ x → fromℕ< (idxOf eq x values) (idxOf-< eq x values (complete x))
  ; decode = get values
  ; decode-encode = λ x → get-idxOf eq x values (complete x)
  ; encode-decode = λ i →
      toℕ-injective (trans (toℕ-fromℕ< (idxOf eq (get values i) values)
                                      (idxOf-< eq (get values i) values
                                        (complete (get values i))))
                           (idxOf-get eq values nodup i))
  }

-- The dependent assignment type has an explicit finite presentation: list
-- every telescope, drop later copies of the same telescope, and use that
-- duplicate-free listing as the codes.
assign-witness : {n : ℕ} {V : Fin n → Set}
  (values : ∀ i → List (V i)) →
  (∀ i (x : V i) → x ∈ values i) →
  (∀ i (x y : V i) → Dec (x ≡ y)) →
  FiniteWitness (Assign n V)
assign-witness values complete eq =
  ofList (assign-≟ eq)
    (dedup (assign-≟ eq) (enumerate values))
    (λ a → mem-dedup-from (assign-≟ eq) a (enumerate values)
      (enum-complete values complete a))
    (dedup-nodup (assign-≟ eq) (enumerate values))

-- Put every listed rational mass over the product of all listed denominators.
-- A non-selected entry contributes a zero with that entry's own denominator,
-- so the resulting denominator is the product independently of the event.
zero-den : QProb → QProb
zero-den p = Q.qprob 0 (Q.den p) (Q.den-pos p)

commonDen : {Ω : Set} → List Ω → (Ω → QProb) → ℕ
commonDen []       _    = 1
commonDen (ω ∷ ωs) mass = Q.den (mass ω) * commonDen ωs mass

commonDen-pos : {Ω : Set} (values : List Ω) (mass : Ω → QProb) →
  0 < commonDen values mass
commonDen-pos []       _    = s≤s z≤n
commonDen-pos (ω ∷ ωs) mass =
  *-pos (Q.den-pos (mass ω)) (commonDen-pos ωs mass)

massAtoms : {Ω : Set} → List Ω → (Ω → QProb) → List (Ω × ℕ)
massAtoms []       _    = []
massAtoms (ω ∷ ωs) mass =
  (ω , Q.num (mass ω) * commonDen ωs mass) ∷
  map (λ (x , w) → (x , Q.den (mass ω) * w)) (massAtoms ωs mass)

eventSum : {Ω : Set} → List Ω → (Ω → QProb) → Event Ω → QProb
eventSum []       _    _     = Q.zero
eventSum (ω ∷ ωs) mass event =
  Q.add (if event ω then mass ω else zero-den (mass ω))
      (eventSum ωs mass event)

eventSum-den : {Ω : Set} (values : List Ω) (mass : Ω → QProb)
  (event : Event Ω) →
  Q.den (eventSum values mass event) ≡ commonDen values mass
eventSum-den []       _    _     = refl
eventSum-den (ω ∷ ωs) mass event with event ω
... | true  rewrite eventSum-den ωs mass event = refl
... | false rewrite eventSum-den ωs mass event = refl

eventMass-atoms : {Ω : Set} (values : List Ω) (mass : Ω → QProb)
  (event : Event Ω) →
  eventMass (massAtoms values mass) event ≡ Q.num (eventSum values mass event)
eventMass-atoms []       _    _     = refl
eventMass-atoms (ω ∷ ωs) mass event with event ω in eq
... | true =
  begin
    Q.num (mass ω) * commonDen ωs mass +
      eventMass (map (λ (x , w) → (x , Q.den (mass ω) * w)) rest) event
  ≡⟨ cong (Q.num (mass ω) * commonDen ωs mass +_)
       (eventMass-scale rest (Q.den (mass ω)) event) ⟩
    Q.num (mass ω) * commonDen ωs mass +
      Q.den (mass ω) * eventMass rest event
  ≡⟨ cong (Q.num (mass ω) * commonDen ωs mass +_)
       (cong (Q.den (mass ω) *_) (eventMass-atoms ωs mass event)) ⟩
    Q.num (mass ω) * commonDen ωs mass +
      Q.den (mass ω) * Q.num (eventSum ωs mass event)
  ≡⟨ cong (λ d → Q.num (mass ω) * d +
                 Q.den (mass ω) * Q.num (eventSum ωs mass event))
       (sym (eventSum-den ωs mass event)) ⟩
    Q.num (mass ω) * Q.den (eventSum ωs mass event) +
      Q.den (mass ω) * Q.num (eventSum ωs mass event)
  ≡⟨ cong (Q.num (mass ω) * Q.den (eventSum ωs mass event) +_)
       (*-comm (Q.den (mass ω)) (Q.num (eventSum ωs mass event))) ⟩
    Q.num (mass ω) * Q.den (eventSum ωs mass event) +
      Q.num (eventSum ωs mass event) * Q.den (mass ω)
  ∎
  where
  rest = massAtoms ωs mass
... | false =
  begin
    eventMass (map (λ (x , w) → (x , Q.den (mass ω) * w)) rest) event
  ≡⟨ eventMass-scale rest (Q.den (mass ω)) event ⟩
    Q.den (mass ω) * eventMass rest event
  ≡⟨ cong (Q.den (mass ω) *_) (eventMass-atoms ωs mass event) ⟩
    Q.den (mass ω) * Q.num (eventSum ωs mass event)
  ≡⟨ *-comm (Q.den (mass ω)) (Q.num (eventSum ωs mass event)) ⟩
    Q.num (eventSum ωs mass event) * Q.den (mass ω)
  ≡⟨ cong (λ n → n + Q.num (eventSum ωs mass event) * Q.den (mass ω))
       (sym (*-zeroˡ (Q.den (eventSum ωs mass event)))) ⟩
    0 * Q.den (eventSum ωs mass event) +
      Q.num (eventSum ωs mass event) * Q.den (mass ω)
  ∎
  where
  rest = massAtoms ωs mass
  *-zeroˡ : ∀ n → 0 * n ≡ 0
  *-zeroˡ n = refl

-- A finite rational mass table before a common denominator has been chosen.
-- The listing is exhaustive and duplicate-free, and the masses of the total
-- event are equivalent to the unit presentation.
record FiniteQMass (Ω : Set) : Set where
  field
    values     : List Ω
    nodup      : Nodup values
    complete   : ∀ ω → ω ∈ values
    mass       : Ω → QProb
    normalized : Equiv (eventSum values mass topEvent) one

open FiniteQMass public

common-total : {Ω : Set} (M : FiniteQMass Ω) →
  totalMass (massAtoms (values M) (mass M)) ≡ commonDen (values M) (mass M)
common-total M =
  begin
    totalMass (massAtoms (values M) (mass M))
  ≡⟨ sym (eventMass-top (massAtoms (values M) (mass M))) ⟩
    eventMass (massAtoms (values M) (mass M)) topEvent
  ≡⟨ eventMass-atoms (values M) (mass M) topEvent ⟩
    Q.num (eventSum (values M) (mass M) topEvent)
  ≡⟨ trans (sym (*-idʳ (Q.num (eventSum (values M) (mass M) topEvent))))
           (trans (normalized M) (*-idˡ (Q.den (eventSum (values M) (mass M) topEvent)))) ⟩
    Q.den (eventSum (values M) (mass M) topEvent)
  ≡⟨ eventSum-den (values M) (mass M) topEvent ⟩
    commonDen (values M) (mass M)
  ∎
  where
  *-idˡ : ∀ n → 1 * n ≡ n
  *-idˡ n = +-idʳ n

-- Convert to a common-denominator record. Zero masses stay zero, and a
-- missing listed outcome is not invented.
toRecord : {Ω : Set} → FiniteQMass Ω → FiniteProbRecord Ω
toRecord M = finiteRecord
  (massAtoms (values M) (mass M))
  (commonDen (values M) (mass M))
  (commonDen-pos (values M) (mass M))
  (common-total M)

toRecord-preserves : {Ω : Set} (M : FiniteQMass Ω) (event : Event Ω) →
  Equiv (probVal (toRecord M) event) (eventSum (values M) (mass M) event)
toRecord-preserves M event =
  begin
    eventMass (massAtoms (values M) (mass M)) event *
      Q.den (eventSum (values M) (mass M) event)
  ≡⟨ cong (eventMass (massAtoms (values M) (mass M)) event *_)
       (eventSum-den (values M) (mass M) event) ⟩
    eventMass (massAtoms (values M) (mass M)) event *
      commonDen (values M) (mass M)
  ≡⟨ cong (_* commonDen (values M) (mass M))
       (eventMass-atoms (values M) (mass M) event) ⟩
    Q.num (eventSum (values M) (mass M) event) *
      commonDen (values M) (mass M)
  ∎

toUrn-preserves : {Ω : Set} (M : FiniteQMass Ω) (event : Event Ω) →
  Equiv (Urn.probVal (toUrn (toRecord M)) event)
        (eventSum (values M) (mass M) event)
toUrn-preserves M event =
  equiv-trans
    {p = Urn.probVal (toUrn (toRecord M)) event}
    {q = probVal (toRecord M) event}
    {r = eventSum (values M) (mass M) event}
    (equiv-sym {p = probVal (toRecord M) event}
               {q = Urn.probVal (toUrn (toRecord M)) event}
      (toUrn-agrees (toRecord M) event))
    (toRecord-preserves M event)
