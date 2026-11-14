module Thesis.Fin where

open import Thesis.Equality
open import Thesis.Nat renaming (zero to ℕ0; suc to ℕs)
open import Thesis.List

-- `Fin n` is a coordinate strictly below `n`. It is the index type of a
-- finite family: `zero` selects the first place, and `suc` shifts one place
-- further. There is no coordinate below zero.

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (ℕs n)
  suc  : ∀ {n} → Fin n → Fin (ℕs n)

-- There is no coordinate strictly below zero.
no-fin : Fin ℕ0 → ⊥
no-fin ()

-- The underlying natural position of a coordinate, counting from zero.
toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = ℕ0
toℕ (suc i) = ℕs (toℕ i)

-- Every coordinate is strictly below its bound.
toℕ-< : ∀ {n} (i : Fin n) → toℕ i < n
toℕ-< {ℕs n} zero    = s≤s z≤n
toℕ-< {ℕs n} (suc i) = s≤s (toℕ-< i)

-- The coordinate whose position is `m`, using a proof that `m` lies below
-- the bound. The proof is data, so the construction does not search.
fromℕ< : ∀ {n} (m : ℕ) → m < n → Fin n
fromℕ< {ℕ0}   m ()
fromℕ< {ℕs n} ℕ0     _        = zero
fromℕ< {ℕs n} (ℕs m) (s≤s h) = suc (fromℕ< m h)

-- The bound proof is not part of the coordinate. Any two proofs that `m`
-- lies below `n` build the same coordinate.
fromℕ<-cong : ∀ {n m} (h₁ h₂ : m < n) → fromℕ< m h₁ ≡ fromℕ< m h₂
fromℕ<-cong h₁ h₂ rewrite ≤-unique h₁ h₂ = refl

toℕ-fromℕ< : ∀ {n} (m : ℕ) (h : m < n) → toℕ (fromℕ< m h) ≡ m
toℕ-fromℕ< {ℕs n} ℕ0     _        = refl
toℕ-fromℕ< {ℕs n} (ℕs m) (s≤s h) = cong ℕs (toℕ-fromℕ< m h)

fromℕ<-toℕ : ∀ {n} (i : Fin n) → fromℕ< (toℕ i) (toℕ-< i) ≡ i
fromℕ<-toℕ zero    = refl
fromℕ<-toℕ (suc i) = cong suc (fromℕ<-toℕ i)

ℕs-injective : ∀ {m n} → ℕs m ≡ ℕs n → m ≡ n
ℕs-injective refl = refl

-- Positions determine coordinates. Distinct constructions sit at distinct
-- positions, so an equality of positions is an equality of coordinates.
toℕ-injective : ∀ {n} {i j : Fin n} → toℕ i ≡ toℕ j → i ≡ j
toℕ-injective {i = zero}  {j = zero}  _  = refl
toℕ-injective {i = zero}  {j = suc j} ()
toℕ-injective {i = suc i} {j = zero}  ()
toℕ-injective {i = suc i} {j = suc j} eq = cong suc (toℕ-injective (ℕs-injective eq))

-- Embed a coordinate into a one-step larger index by keeping its position.
-- The new last place is not in the image.
castSucc : ∀ {n} → Fin n → Fin (ℕs n)
castSucc zero    = zero
castSucc (suc i) = suc (castSucc i)

-- The greatest coordinate below a successor bound.
last : ∀ {n} → Fin (ℕs n)
last {ℕ0}   = zero
last {ℕs n} = suc last

-- A coordinate below a successor is either an earlier coordinate, embedded
-- by castSucc, or the new last place.
data Prefix {n : ℕ} : Fin (ℕs n) → Set where
  before : (j : Fin n) → Prefix (castSucc j)
  end    : Prefix last

-- Compute that classification. The recursion follows the coordinate, so the
-- result is data, not an appeal to excluded middle.
prefix : ∀ {n} (i : Fin (ℕs n)) → Prefix i
prefix {ℕ0}   zero    = end
prefix {ℕ0}   (suc ())
prefix {ℕs n} zero    = before zero
prefix {ℕs n} (suc i) with prefix i
... | before j = before (suc j)
... | end      = end

-- The canonical listing of every coordinate, in increasing order, with each
-- coordinate once. The successor listing is the old listing shifted by one,
-- placed after the new zero.
finRange : ∀ n → List (Fin n)
finRange ℕ0     = []
finRange (ℕs n) = zero ∷ map suc (finRange n)

-- Build a list by reading a coordinate family once at each position. Two
-- families that agree at every coordinate therefore build the same list:
-- the induction steps through the finitely many coordinates and never equates
-- the families as functions.
ofFn : {n : ℕ} {A : Set} → (Fin n → A) → List A
ofFn {ℕ0}    f = []
ofFn {ℕs n} f = f zero ∷ ofFn (λ i → f (suc i))

ofFn-cong : {n : ℕ} {A : Set} {f g : Fin n → A} →
            (∀ i → f i ≡ g i) → ofFn f ≡ ofFn g
ofFn-cong {ℕ0}    _ = refl
ofFn-cong {ℕs n} h rewrite h zero | ofFn-cong {n} (λ i → h (suc i)) = refl

get : {A : Set} (xs : List A) → Fin (length xs) → A
get (x ∷ xs) zero    = x
get (x ∷ xs) (suc i) = get xs i

-- Reading back the coordinates of a list recovers that list. The coordinate
-- family is the list's own lookup, so this is a round trip from lists to
-- finite families and back.
ofFn-get : {A : Set} (xs : List A) → ofFn (get xs) ≡ xs
ofFn-get []       = refl
ofFn-get (x ∷ xs) rewrite ofFn-get xs = refl

-- A shifted coordinate is never zero, and successor on coordinates is
-- injective. Both are used to keep the canonical listing free of duplicates.
suc-≢-zero : ∀ {n} {i : Fin n} → suc i ≢ zero
suc-≢-zero ()

suc-injective : ∀ {n} {i j : Fin n} → suc i ≡ suc j → i ≡ j
suc-injective refl = refl

-- Coordinate equality is decided by recursion on the two indices. Distinct
-- constructors refute equality; matching successors continue one step down.
fin-≟ : ∀ {n} (i j : Fin n) → Dec (i ≡ j)
fin-≟ zero    zero    = yes refl
fin-≟ zero    (suc j) = no λ ()
fin-≟ (suc i) zero    = no λ ()
fin-≟ (suc i) (suc j) with fin-≟ i j
... | yes eq = yes (cong suc eq)
... | no  ne = no λ eq → ne (suc-injective eq)

-- No coordinate occurs twice. The tail of a cons is duplicate-free, and the
-- head does not occur in that tail.
data Nodup {A : Set} : List A → Set where
  []  : Nodup []
  _∷_ : ∀ {x xs} → (x ∈ xs → ⊥) → Nodup xs → Nodup (x ∷ xs)

map-suc-nodup : ∀ {n} {xs : List (Fin n)} → Nodup xs → Nodup (map suc xs)
map-suc-nodup []       = []
map-suc-nodup (p ∷ ps) = (λ mem → p (suc-mem-inv mem)) ∷ map-suc-nodup ps
  where
  suc-mem-inv : ∀ {n} {i : Fin n} {ys : List (Fin n)} →
                suc i ∈ map suc ys → i ∈ ys
  suc-mem-inv {ys = []}     ()
  suc-mem-inv {ys = y ∷ ys} here        = here
  suc-mem-inv {ys = y ∷ ys} (there mem) = there (suc-mem-inv mem)

zero-∉-map-suc : ∀ {n} (xs : List (Fin n)) → zero ∈ map suc xs → ⊥
zero-∉-map-suc []       ()
zero-∉-map-suc (x ∷ xs) (there mem) = zero-∉-map-suc xs mem

finRange-nodup : ∀ n → Nodup (finRange n)
finRange-nodup ℕ0     = []
finRange-nodup (ℕs n) =
  zero-∉-map-suc (finRange n) ∷ map-suc-nodup (finRange-nodup n)

-- How many times a decidable value occurs.
occurrences : {A : Set} → (∀ (x y : A) → Dec (x ≡ y)) → A → List A → ℕ
occurrences _  _ []       = ℕ0
occurrences eq x (y ∷ ys) with eq x y
... | yes _ = ℕs (occurrences eq x ys)
... | no  _ = occurrences eq x ys

occurrences-zero-empty : {A : Set} (eq : ∀ (x y : A) → Dec (x ≡ y)) (x : A) →
                   occurrences eq x [] ≡ ℕ0
occurrences-zero-empty _ _ = refl

-- An element excluded from a list occurs zero times.
occurrences-absent : {A : Set} (eq : ∀ (x y : A) → Dec (x ≡ y)) {x : A} {xs : List A} →
               (x ∈ xs → ⊥) → occurrences eq x xs ≡ ℕ0
occurrences-absent eq {xs = []}     _ = refl
occurrences-absent eq {x = x} {xs = y ∷ ys} p with eq x y
... | yes refl = ⊥-elim (p here)
... | no  _    = occurrences-absent eq (λ mem → p (there mem))

-- In a duplicate-free list, an entry that occurs does so exactly once.
occurrences-nodup-∈ : {A : Set} (eq : ∀ (x y : A) → Dec (x ≡ y)) {x : A} {xs : List A} →
                Nodup xs → x ∈ xs → occurrences eq x xs ≡ ℕs ℕ0
occurrences-nodup-∈ eq {x} {x ∷ xs} (p ∷ _) here with eq x x
... | yes _ = cong ℕs (occurrences-absent eq p)
... | no ne = ⊥-elim (ne refl)
occurrences-nodup-∈ eq {x} {y ∷ xs} (p ∷ ps) (there mem) with eq x y
... | yes refl = ⊥-elim (p mem)
... | no  _    = occurrences-nodup-∈ eq ps mem

-- Every coordinate occurs in the canonical listing.
finRange-complete : ∀ {n} (i : Fin n) → i ∈ finRange n
finRange-complete zero    = here
finRange-complete (suc i) = there (map-suc-∈ (finRange-complete i))
  where
  map-suc-∈ : ∀ {n} {i : Fin n} {xs : List (Fin n)} →
              i ∈ xs → suc i ∈ map suc xs
  map-suc-∈ here        = here
  map-suc-∈ (there mem) = there (map-suc-∈ mem)

-- Each coordinate occurs exactly once.
occurrences-finRange : ∀ n (i : Fin n) → occurrences fin-≟ i (finRange n) ≡ ℕs ℕ0
occurrences-finRange n i = occurrences-nodup-∈ fin-≟ (finRange-nodup n) (finRange-complete i)
