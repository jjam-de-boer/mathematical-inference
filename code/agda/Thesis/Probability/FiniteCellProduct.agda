module Thesis.Probability.FiniteCellProduct where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
open import Thesis.Fin hiding (zero; suc)
open import Thesis.Probability.Core
open import Thesis.Probability.ConstructivePermutation using (perm-of-count; pairList)

-- Pairs of finite cells, enumerated in row-major order and identified with
-- the cells of the product bound. A rectangular event, true on a cell when
-- each coordinate satisfies its own test, selects the product of the two
-- component counts.

-- Two types are explicitly equivalent when each direction undoes the other
-- on every element. The witnesses are functions, and the two round trips are
-- proved element by element.
record EquivTypes (A B : Set) : Set where
  constructor equivTypes
  field
    forward          : A → B
    backward         : B → A
    backward-forward : ∀ a → backward (forward a) ≡ a
    forward-backward : ∀ b → forward (backward b) ≡ b

-- A quotient that has reached the left factor no longer fits under the
-- product bound.
quot-< : ∀ q r M d → r < d → q * d + r < M * d → q < M
quot-< q r M d r<d below with lt-or-ge q M
... | inl q<M = q<M
... | inr M≤q =
  ⊥-elim (≰-of-≥ (≤-trans (*-monoˡ M≤q d) (≤-+ʳ (q * d) r)) below)

-- The row-major address of a pair lies strictly below the product bound.
-- The remainder sits below one full row, and the next row still lies at or
-- before the last row of the product.
sum-< : ∀ {a A b B} → a < A → b < B → a * B + b < A * B
sum-< {a} {A} {b} {B} a<A b<B =
  ≤-trans
    (subst (λ n → n ≤ a * B + B) (+-suc (a * B) b) (+-monoʳ (a * B) b<B))
    (≤-trans
      (subst (λ n → a * B + B ≤ n) (+-comm (a * B) B) (≤-refl (a * B + B)))
      (*-monoˡ a<A B))

-- Changing the dividend along an equality does not change the quotient or
-- the remainder. Division is computed from the dividend.
quot-cong : ∀ {a b d} (p : 0 < d) → a ≡ b →
  Division.quot (divide a d p) ≡ Division.quot (divide b d p)
quot-cong _ refl = refl

rem-cong : ∀ {a b d} (p : 0 < d) → a ≡ b →
  Division.rem (divide a d p) ≡ Division.rem (divide b d p)
rem-cong _ refl = refl

-- Row-major address of a pair of coordinates.
encode : {M N : ℕ} → Fin M × Fin N → Fin (M * N)
encode {N = N} (i , j) =
  fromℕ< (toℕ i * N + toℕ j) (sum-< (toℕ-< i) (toℕ-< j))

-- Split a product coordinate into its row and its place in the row.
decode : (M : ℕ) {N : ℕ} → 0 < N → Fin (M * N) → Fin M × Fin N
decode M {N} hN index =
  fromℕ< (Division.quot Δ) q< , fromℕ< (Division.rem Δ) (Division.rem-< Δ)
  where
  Δ = divide (toℕ index) N hN
  q< = quot-< (Division.quot Δ) (Division.rem Δ) M N (Division.rem-< Δ)
         (subst (_< M * N) (Division.path Δ) (toℕ-< index))

toℕ-encode : {M N : ℕ} (i : Fin M) (j : Fin N) →
  toℕ (encode (i , j)) ≡ toℕ i * N + toℕ j
toℕ-encode {N = N} i j = toℕ-fromℕ< (toℕ i * N + toℕ j) (sum-< (toℕ-< i) (toℕ-< j))

toℕ-decode-fst : {M N : ℕ} (hN : 0 < N) (index : Fin (M * N)) →
  toℕ (fst (decode M hN index)) ≡ Division.quot (divide (toℕ index) N hN)
toℕ-decode-fst {M} {N} hN index =
  toℕ-fromℕ< (Division.quot Δ) q<
  where
  Δ = divide (toℕ index) N hN
  q< = quot-< (Division.quot Δ) (Division.rem Δ) M N (Division.rem-< Δ)
         (subst (_< M * N) (Division.path Δ) (toℕ-< index))

toℕ-decode-snd : {M N : ℕ} (hN : 0 < N) (index : Fin (M * N)) →
  toℕ (snd (decode M hN index)) ≡ Division.rem (divide (toℕ index) N hN)
toℕ-decode-snd {M = M} {N = N} hN index =
  toℕ-fromℕ< (Division.rem (divide (toℕ index) N hN))
             (Division.rem-< (divide (toℕ index) N hN))

-- Encoding and then decoding restores the pair. The address is already a
-- quotient times the row length plus a remainder below that length.
decode-encode : {M N : ℕ} (hN : 0 < N) (i : Fin M) (j : Fin N) →
  decode M hN (encode (i , j)) ≡ (i , j)
decode-encode {M = M} {N = N} hN i j = cong₂ _,_ fst≡ snd≡
  where
  s = toℕ i * N + toℕ j
  fst≡ : fst (decode M hN (encode (i , j))) ≡ i
  fst≡ = toℕ-injective
    (begin
      toℕ (fst (decode M hN (encode (i , j))))
    ≡⟨ toℕ-decode-fst {M = M} {N = N} hN (encode (i , j)) ⟩
      Division.quot (divide (toℕ (encode (i , j))) N hN)
    ≡⟨ quot-cong hN (toℕ-encode i j) ⟩
      Division.quot (divide s N hN)
    ≡⟨ fst (divide-scale (toℕ i) (toℕ j) N (toℕ-< j) hN) ⟩
      toℕ i
    ≡⟨ sym (toℕ-fromℕ< (toℕ i) (toℕ-< i)) ⟩
      toℕ (fromℕ< (toℕ i) (toℕ-< i))
    ≡⟨ cong toℕ (fromℕ<-toℕ i) ⟩
      toℕ i
    ∎)
  snd≡ : snd (decode M hN (encode (i , j))) ≡ j
  snd≡ = toℕ-injective
    (begin
      toℕ (snd (decode M hN (encode (i , j))))
    ≡⟨ toℕ-decode-snd {M = M} {N = N} hN (encode (i , j)) ⟩
      Division.rem (divide (toℕ (encode (i , j))) N hN)
    ≡⟨ rem-cong hN (toℕ-encode i j) ⟩
      Division.rem (divide s N hN)
    ≡⟨ snd (divide-scale (toℕ i) (toℕ j) N (toℕ-< j) hN) ⟩
      toℕ j
    ≡⟨ sym (toℕ-fromℕ< (toℕ j) (toℕ-< j)) ⟩
      toℕ (fromℕ< (toℕ j) (toℕ-< j))
    ≡⟨ cong toℕ (fromℕ<-toℕ j) ⟩
      toℕ j
    ∎)

-- Decoding and then encoding restores the product coordinate.
encode-decode : {M N : ℕ} (hN : 0 < N) (index : Fin (M * N)) →
  encode (decode M hN index) ≡ index
encode-decode {M = M} {N = N} hN index = toℕ-injective
  (begin
    toℕ (encode (decode M hN index))
  ≡⟨ toℕ-encode (fst (decode M hN index)) (snd (decode M hN index)) ⟩
    toℕ (fst (decode M hN index)) * N + toℕ (snd (decode M hN index))
  ≡⟨ cong₂ _+_
       (cong (_* N) (toℕ-decode-fst {M = M} {N = N} hN index))
       (toℕ-decode-snd {M = M} {N = N} hN index) ⟩
    Division.quot Δ * N + Division.rem Δ
  ≡⟨ sym (Division.path Δ) ⟩
    toℕ index
  ∎)
  where Δ = divide (toℕ index) N hN

-- The two directions are an equivalence of the pair of coordinate types with
-- the product coordinate type.
cell-equivalence : {M N : ℕ} (hN : 0 < N) →
  EquivTypes (Fin M × Fin N) (Fin (M * N))
cell-equivalence {M} {N} hN =
  equivTypes encode (decode M hN)
    (λ cell → decode-encode {M = M} {N = N} hN (fst cell) (snd cell))
    (encode-decode {M = M} {N = N} hN)

-- Every coordinate, once, in increasing order.
cells : ∀ n → List (Fin n)
cells = finRange

cells-nodup : ∀ n → Nodup (cells n)
cells-nodup = finRange-nodup

-- One selected coordinate contributes one to the count.
count-as-occurrences : ∀ {n} (i : Fin n) (xs : List (Fin n)) →
  count xs (λ j → fromDec (fin-≟ i j)) ≡ occurrences fin-≟ i xs
count-as-occurrences i [] = refl
count-as-occurrences i (j ∷ xs) with fin-≟ i j
... | yes _ = cong suc (count-as-occurrences i xs)
... | no  _ = count-as-occurrences i xs

count-cells-singleton : ∀ {n} (i : Fin n) →
  count (cells n) (λ j → fromDec (fin-≟ i j)) ≡ suc zero
count-cells-singleton {n} i =
  trans (count-as-occurrences i (cells n)) (occurrences-finRange n i)

-- Every pair, with the right coordinate varying fastest.
productCells : ∀ M N → List (Fin M × Fin N)
productCells M N = pairList (cells M) (cells N)

rectangular : ∀ {M N} → Event (Fin M) → Event (Fin N) → Event (Fin M × Fin N)
rectangular E F cell = E (fst cell) ∧ F (snd cell)

-- A contribution of `c` when the left test accepts the row, and nothing
-- otherwise, is the same number as the product increment below.
row-step : (e f : Bool) (n : ℕ) →
  extra (e ∧ f) + (if e then n else 0) ≡ (if e then extra f + n else 0)
row-step true  true  n = refl
row-step true  false n = refl
row-step false true  n = refl
row-step false false n = refl

nil-step : (e : Bool) → zero ≡ (if e then zero else zero)
nil-step true  = refl
nil-step false = refl

-- One row contributes the right-hand count when the left test accepts the
-- row, and contributes nothing otherwise.
count-row : ∀ {M N} (left : Fin M) (ys : List (Fin N))
  (E : Event (Fin M)) (F : Event (Fin N)) →
  count (map (λ r → (left , r)) ys) (rectangular E F) ≡
  (if E left then count ys F else 0)
count-row left [] E F = nil-step (E left)
count-row left (r ∷ ys) E F =
  begin
    extra (E left ∧ F r) + count (map (λ s → (left , s)) ys) (rectangular E F)
  ≡⟨ cong (extra (E left ∧ F r) +_) (count-row left ys E F) ⟩
    extra (E left ∧ F r) + (if E left then count ys F else 0)
  ≡⟨ row-step (E left) (F r) (count ys F) ⟩
    if E left then extra (F r) + count ys F else 0
  ∎

-- The zero contribution and the unit contribution both factor through the
-- right-hand count.
row-distrib : (e : Bool) (c n : ℕ) →
  (if e then c else 0) + n * c ≡ (extra e + n) * c
row-distrib true  c n = refl
row-distrib false c n = refl

count-rows : ∀ {M N} (xs : List (Fin M)) (ys : List (Fin N))
  (E : Event (Fin M)) (F : Event (Fin N)) →
  count (pairList xs ys) (rectangular E F) ≡ count xs E * count ys F
count-rows [] ys E F = refl
count-rows (x ∷ xs) ys E F =
  begin
    count (map (λ r → (x , r)) ys ++ pairList xs ys) (rectangular E F)
  ≡⟨ countP-++ (rectangular E F) (map (λ r → (x , r)) ys) (pairList xs ys) ⟩
    count (map (λ r → (x , r)) ys) (rectangular E F) +
      count (pairList xs ys) (rectangular E F)
  ≡⟨ cong₂ _+_ (count-row x ys E F) (count-rows xs ys E F) ⟩
    (if E x then count ys F else 0) + count xs E * count ys F
  ≡⟨ row-distrib (E x) (count ys F) (count xs E) ⟩
    count (x ∷ xs) E * count ys F
  ∎

-- A rectangle selects the product of the two component counts.
count-rectangular : ∀ {M N} (E : Event (Fin M)) (F : Event (Fin N)) →
  count (productCells M N) (rectangular E F) ≡
  count (cells M) E * count (cells N) F
count-rectangular {M} {N} E F = count-rows (cells M) (cells N) E F

-- The same pairs, named by their row-major addresses.
encodedCells : ∀ M N → List (Fin (M * N))
encodedCells M N = map encode (productCells M N)

encodedRectangular : ∀ {M N} → 0 < N → Event (Fin M) → Event (Fin N) →
  Event (Fin (M * N))
encodedRectangular {M} hN E F index = rectangular E F (decode M hN index)

count-map : {A B : Set} (f : A → B) (E : Event B) (xs : List A) →
  count (map f xs) E ≡ count xs (λ x → E (f x))
count-map f E [] = refl
count-map f E (x ∷ xs) rewrite count-map f E xs = refl

-- Transport along the encoding preserves the rectangular count. Decoding an
-- encoded pair is that pair, so the test is unchanged.
count-encoded : ∀ {M N} (hN : 0 < N) (E : Event (Fin M)) (F : Event (Fin N)) →
  count (encodedCells M N) (encodedRectangular hN E F) ≡
  count (cells M) E * count (cells N) F
count-encoded {M} {N} hN E F =
  begin
    count (map encode (productCells M N)) (encodedRectangular hN E F)
  ≡⟨ count-map encode (encodedRectangular hN E F) (productCells M N) ⟩
    count (productCells M N) (λ cell → rectangular E F (decode M hN (encode cell)))
  ≡⟨ count-cong {xs = productCells M N} (λ { (i , j) →
        cong (rectangular E F) (decode-encode {M = M} {N = N} hN i j) }) ⟩
    count (productCells M N) (rectangular E F)
  ≡⟨ count-rectangular {M = M} {N = N} E F ⟩
    count (cells M) E * count (cells N) F
  ∎

-- A coordinate agrees with a target exactly when both of its decoded
-- components agree with the target's components.
not-true-step : (b c : Bool) → b ≢ true → b ≡ c → c ≡ false
not-true-step _ false _  _  = refl
not-true-step b true  d eq = ⊥-elim (d eq)

not-true : (b : Bool) → b ≢ true → b ≡ false
not-true b d = not-true-step b b d refl

-- The two projections of a true conjunction.
∧-left : ∀ {b c} → b ∧ c ≡ true → b ≡ true
∧-left {true}  _ = refl
∧-left {false} ()

∧-right : ∀ {b c} → b ∧ c ≡ true → c ≡ true
∧-right {true} {true}  _ = refl
∧-right {true} {false} ()
∧-right {false} ()

encoded-hit : ∀ {M N} (hN : 0 < N) (target index : Fin (M * N)) →
  (fromDec (fin-≟ (fst (decode M hN index)) (fst (decode M hN target))) ∧
   fromDec (fin-≟ (snd (decode M hN index)) (snd (decode M hN target)))) ≡
  fromDec (fin-≟ index target)
encoded-hit {M} {N} hN target index with fin-≟ index target
... | yes eq =
  cong₂ _∧_
    (fromDec-of-proof (fin-≟ (fst (decode M hN index)) (fst (decode M hN target)))
      (cong (λ z → fst (decode M hN z)) eq))
    (fromDec-of-proof (fin-≟ (snd (decode M hN index)) (snd (decode M hN target)))
      (cong (λ z → snd (decode M hN z)) eq))
... | no ¬eq = not-true _ refuse
  where
  refuse : fromDec (fin-≟ (fst (decode M hN index)) (fst (decode M hN target))) ∧
           fromDec (fin-≟ (snd (decode M hN index)) (snd (decode M hN target)))
           ≢ true
  refuse isTrue =
    ¬eq (toℕ-injective
      (trans (sym (toℕ-path index))
        (trans (encode-value components) (toℕ-path target))))
    where
    toℕ-path : (k : Fin _) → toℕ (encode (decode M hN k)) ≡ toℕ k
    toℕ-path k = cong toℕ (encode-decode {M = M} {N = N} hN k)
    components : decode M hN index ≡ decode M hN target
    components = cong₂ _,_
      (fromDec-yes (fin-≟ (fst (decode M hN index)) (fst (decode M hN target)))
        (∧-left isTrue))
      (fromDec-yes (fin-≟ (snd (decode M hN index)) (snd (decode M hN target)))
        (∧-right isTrue))
    encode-value : ∀ {p q : Fin _ × Fin _} → p ≡ q → toℕ (encode p) ≡ toℕ (encode q)
    encode-value eq = cong (λ z → toℕ (encode z)) eq

count-encoded-singleton : ∀ {M N} (hN : 0 < N) (index : Fin (M * N)) →
  count (encodedCells M N) (λ j → fromDec (fin-≟ index j)) ≡ suc zero
count-encoded-singleton {M} {N} hN index =
  begin
    count (encodedCells M N) (λ j → fromDec (fin-≟ index j))
  ≡⟨ count-cong {xs = encodedCells M N}
        (λ j → sym (encoded-hit {M = M} {N = N} hN j index)) ⟩
    count (encodedCells M N)
      (encodedRectangular hN
        (λ a → fromDec (fin-≟ (fst (decode M hN index)) a))
        (λ b → fromDec (fin-≟ (snd (decode M hN index)) b)))
  ≡⟨ count-encoded {M = M} {N = N} hN _ _ ⟩
    count (cells M) (λ a → fromDec (fin-≟ (fst (decode M hN index)) a)) *
      count (cells N) (λ b → fromDec (fin-≟ (snd (decode M hN index)) b))
  ≡⟨ cong₂ _*_ (count-cells-singleton {n = M} (fst (decode M hN index)))
               (count-cells-singleton {n = N} (snd (decode M hN index))) ⟩
    suc zero * suc zero
  ≡⟨ +-idʳ (suc zero) ⟩
    suc zero
  ∎

-- Row-major encoding lists each product coordinate once. The order may
-- differ from the increasing enumeration; the permutation records the
-- rearrangement.
pairList-right-empty : {A B : Set} (xs : List A) → pairList xs ([] {A = B}) ≡ []
pairList-right-empty []       = refl
pairList-right-empty (_ ∷ xs) = pairList-right-empty xs

encodedCells-perm : ∀ M N → Perm (encodedCells M N) (cells (M * N))
encodedCells-perm M zero =
  subst (λ ys → Perm ys (cells (M * zero)))
    (sym (cong (map encode) (pairList-right-empty (cells M))))
    (subst (λ n → Perm [] (cells n)) (sym (*-zeroʳ M)) refl)
encodedCells-perm M (suc N) =
  perm-of-count fin-≟ (λ index →
    trans (sym (count-as-occurrences {n = M * suc N} index (encodedCells M (suc N))))
      (trans (count-encoded-singleton {M = M} {N = suc N} (s≤s z≤n) index)
        (trans (sym (count-cells-singleton {n = M * suc N} index))
          (count-as-occurrences {n = M * suc N} index (cells (M * suc N))))))

-- On the increasing enumeration, a rectangle still selects the product count.
count-canonical : ∀ {M N} (hN : 0 < N) (E : Event (Fin M)) (F : Event (Fin N)) →
  count (cells (M * N)) (encodedRectangular hN E F) ≡
  count (cells M) E * count (cells N) F
count-canonical {M} {N} hN E F =
  begin
    count (cells (M * N)) (encodedRectangular hN E F)
  ≡⟨ sym (count-reindex (encodedCells-perm M N) (encodedRectangular hN E F)) ⟩
    count (encodedCells M N) (encodedRectangular hN E F)
  ≡⟨ count-encoded {M = M} {N = N} hN E F ⟩
    count (cells M) E * count (cells N) F
  ∎

-- Specified component counts multiply.
selected-product : ∀ {M N k l} (hN : 0 < N)
  (E : Event (Fin M)) (F : Event (Fin N)) →
  count (cells M) E ≡ k → count (cells N) F ≡ l →
  count (cells (M * N)) (encodedRectangular hN E F) ≡ k * l
selected-product hN E F hE hF =
  trans (count-canonical hN E F) (cong₂ _*_ hE hF)

