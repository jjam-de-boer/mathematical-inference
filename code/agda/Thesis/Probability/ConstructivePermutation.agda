module Thesis.Probability.ConstructivePermutation where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
open import Thesis.Fin using (Nodup; occurrences) renaming ([] to nodup[] ; _∷_ to _∷ᵈ_)

-- Explicit permutations of finite lists. An occurrence count, or a
-- duplicate-free listing of the same entries, determines a concrete sequence
-- of swaps. Nothing is chosen: each step moves one exhibited entry.

-- A decision of a reflexive identity is affirmative. The negative branch
-- would be a proof that an entry differs from itself.
fromDec-refl : {A : Set} {x : A} (d : Dec (x ≡ x)) → fromDec d ≡ true
fromDec-refl (yes _) = refl
fromDec-refl (no ¬x) = ⊥-elim (¬x refl)

0≢suc : ∀ {n} → 0 ≢ suc n
0≢suc ()

-- The head contributes one when it is the sought entry, and nothing otherwise.
occurrences-cons : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (other head : A) (xs : List A) →
  occurrences eq other (head ∷ xs) ≡
  extra (fromDec (eq other head)) + occurrences eq other xs
occurrences-cons eq other head xs with eq other head
... | yes _ = refl
... | no  _ = refl

-- An entry occurs once more in its own extension than in the tail.
occurrences-self : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (value : A) (xs : List A) →
  occurrences eq value (value ∷ xs) ≡ suc (occurrences eq value xs)
occurrences-self eq value xs =
  begin
    occurrences eq value (value ∷ xs)
  ≡⟨ occurrences-cons eq value value xs ⟩
    extra (fromDec (eq value value)) + occurrences eq value xs
  ≡⟨ cong (λ b → extra b + occurrences eq value xs) (fromDec-refl (eq value value)) ⟩
    suc (occurrences eq value xs)
  ∎

-- Swapping the first two cells does not change how many times an entry occurs.
occurrences-swap : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (value x y : A) (xs : List A) →
  occurrences eq value (x ∷ y ∷ xs) ≡ occurrences eq value (y ∷ x ∷ xs)
occurrences-swap eq value x y xs =
  begin
    occurrences eq value (x ∷ y ∷ xs)
  ≡⟨ occurrences-cons eq value x (y ∷ xs) ⟩
    extra (fromDec (eq value x)) + occurrences eq value (y ∷ xs)
  ≡⟨ cong (extra (fromDec (eq value x)) +_) (occurrences-cons eq value y xs) ⟩
    extra (fromDec (eq value x)) +
      (extra (fromDec (eq value y)) + occurrences eq value xs)
  ≡⟨ sym (+-assoc (extra (fromDec (eq value x)))
                  (extra (fromDec (eq value y)))
                  (occurrences eq value xs)) ⟩
    (extra (fromDec (eq value x)) + extra (fromDec (eq value y))) +
      occurrences eq value xs
  ≡⟨ cong (_+ occurrences eq value xs)
       (+-comm (extra (fromDec (eq value x))) (extra (fromDec (eq value y)))) ⟩
    (extra (fromDec (eq value y)) + extra (fromDec (eq value x))) +
      occurrences eq value xs
  ≡⟨ +-assoc (extra (fromDec (eq value y)))
             (extra (fromDec (eq value x)))
             (occurrences eq value xs) ⟩
    extra (fromDec (eq value y)) +
      (extra (fromDec (eq value x)) + occurrences eq value xs)
  ≡⟨ cong (extra (fromDec (eq value y)) +_)
       (sym (occurrences-cons eq value x xs)) ⟩
    extra (fromDec (eq value y)) + occurrences eq value (x ∷ xs)
  ≡⟨ sym (occurrences-cons eq value y (x ∷ xs)) ⟩
    occurrences eq value (y ∷ x ∷ xs)
  ∎

-- A permutation preserves occurrence counts. The count is recomputed on the
-- rearranged cells; the two counting functions are not identified.
occurrences-perm : {A : Set} {xs ys : List A} (eq : (x y : A) → Dec (x ≡ y))
  (value : A) → Perm xs ys → occurrences eq value xs ≡ occurrences eq value ys
occurrences-perm eq value refl = refl
occurrences-perm eq value (prep {x} p) with eq value x
... | yes _ = cong suc (occurrences-perm eq value p)
... | no  _ = occurrences-perm eq value p
occurrences-perm eq value (swap {x} {y} {xs}) = occurrences-swap eq value x y xs
occurrences-perm eq value (comp p q) =
  trans (occurrences-perm eq value p) (occurrences-perm eq value q)

-- A positive count exhibits an entry. The successor tells which cell matched.
∈-of-suc : {A : Set} (eq : (x y : A) → Dec (x ≡ y)) {x : A} {xs : List A} {n : ℕ} →
  occurrences eq x xs ≡ suc n → x ∈ xs
∈-of-suc eq {xs = []} ()
∈-of-suc eq {x} {y ∷ ys} h with eq x y
... | yes p = subst (_∈ y ∷ ys) (sym p) here
... | no  _ = there (∈-of-suc eq h)

-- If an entry occurs, moving its first match to the front is a permutation.
perm-cons-erase : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  (x : A) (xs : List A) → x ∈ xs → Perm xs (x ∷ erase eq x xs)
perm-cons-erase eq x (y ∷ ys) mem with eq x y
... | yes p = subst (λ z → Perm (y ∷ ys) (z ∷ ys)) (sym p) refl
... | no ¬p with mem
... | here = ⊥-elim (¬p refl)
... | there mem′ =
  comp (prep (perm-cons-erase eq x ys mem′)) (swap {x = y} {y = x})

-- Matching occurrence counts determine a permutation. The first entry of the
-- left list is moved to the front of the right list, that one occurrence is
-- cancelled, and the construction repeats on the tails.
perm-of-count : {A : Set} (eq : (x y : A) → Dec (x ≡ y))
  {left right : List A} →
  (∀ value → occurrences eq value left ≡ occurrences eq value right) →
  Perm left right
perm-of-count eq {[]} {[]} _ = refl
perm-of-count eq {[]} {value ∷ rest} h =
  ⊥-elim (0≢suc (trans (h value) (occurrences-self eq value rest)))
perm-of-count eq {value ∷ left} {right} h =
  comp (prep (perm-of-count eq {left} {erase eq value right} tail-counts))
       (perm-sym front)
  where
  mem : value ∈ right
  mem = ∈-of-suc eq (trans (sym (h value)) (occurrences-self eq value left))
  front : Perm right (value ∷ erase eq value right)
  front = perm-cons-erase eq value right mem
  tail-counts : ∀ other →
    occurrences eq other left ≡ occurrences eq other (erase eq value right)
  tail-counts other =
    +-cancelˡ-≡ (extra (fromDec (eq other value)))
      (begin
        extra (fromDec (eq other value)) + occurrences eq other left
      ≡⟨ sym (occurrences-cons eq other value left) ⟩
        occurrences eq other (value ∷ left)
      ≡⟨ h other ⟩
        occurrences eq other right
      ≡⟨ occurrences-perm eq other front ⟩
        occurrences eq other (value ∷ erase eq value right)
      ≡⟨ occurrences-cons eq other value (erase eq value right) ⟩
        extra (fromDec (eq other value)) +
          occurrences eq other (erase eq value right)
      ∎)

-- Removing one exhibited occurrence keeps the remaining list duplicate-free,
-- and the removed entry does not occur in what remains.
nodup-remove : {A : Set} {x : A} (before after : List A) →
  Nodup (before ++ x ∷ after) →
  Nodup (before ++ after) × (x ∈ before ++ after → ⊥)
nodup-remove [] after (x∉ ∷ᵈ na) = na , x∉
nodup-remove {x = x} (y ∷ before) after (y∉ ∷ᵈ nrest) =
  (y∉′ ∷ᵈ fst ih) , x∉′
  where
  ih = nodup-remove before after nrest
  y∉′ : y ∈ before ++ after → ⊥
  y∉′ mem = y∉ (∈-insert before after mem)
  x∉′ : x ∈ y ∷ (before ++ after) → ⊥
  x∉′ here        = y∉ (∈-++ʳ before here)
  x∉′ (there mem) = snd ih mem

-- Two duplicate-free lists with the same entries differ by a permutation.
-- The shared head is removed from the right-hand list and the tails are
-- compared. Both directions of membership are kept as functions.
perm-of-same-members : {A : Set} (left right : List A) →
  Nodup left → Nodup right →
  (∀ value → (value ∈ left → value ∈ right) × (value ∈ right → value ∈ left)) →
  Perm left right
perm-of-same-members [] [] _ _ _ = refl
perm-of-same-members [] (y ∷ _) _ _ same with snd (same y) here
... | ()
perm-of-same-members (value ∷ left) right (value∉ ∷ᵈ nleft) nright same
  with split-∈ (fst (same value) here)
... | located before after path rewrite path =
  comp (prep (perm-of-same-members left (before ++ after) nleft
              (fst removed) tail-same))
       (perm-sym (perm-middle before after))
  where
  removed = nodup-remove before after nright
  tail-same : ∀ w → (w ∈ left → w ∈ before ++ after) ×
                     (w ∈ before ++ after → w ∈ left)
  tail-same w =
    (λ mem → forward mem) , (λ mem → backward mem)
    where
    forward : w ∈ left → w ∈ before ++ after
    forward mem with ∈-++ before (value ∷ after) (fst (same w) (there mem))
    ... | inl inBefore = ∈-++ˡ inBefore
    ... | inr here = ⊥-elim (value∉ mem)
    ... | inr (there inAfter) = ∈-++ʳ before inAfter
    backward : w ∈ before ++ after → w ∈ left
    backward mem with snd (same w) (∈-insert before after mem)
    ... | here = ⊥-elim (snd removed mem)
    ... | there inLeft = inLeft

-- The preimage of a mapped entry: a source cell, its position, and the
-- computation that produced the image.
data Fiber {A B : Set} (f : A → B) (y : B) : List A → Set where
  fiber : {xs : List A} (x : A) → x ∈ xs → f x ≡ y → Fiber f y xs

fiber-map : {A B : Set} {f : A → B} {y : B} (xs : List A) →
  y ∈ map f xs → Fiber f y xs
fiber-map (x ∷ xs) here = fiber x here refl
fiber-map (x ∷ xs) (there mem) with fiber-map xs mem
... | fiber z mz eq = fiber z (there mz) eq

-- A map that does not identify entries of a duplicate-free list keeps the
-- image duplicate-free. Injectivity is required only on the listed entries.
nodup-map : {A B : Set} (f : A → B) (xs : List A) →
  (∀ {a b} → a ∈ xs → b ∈ xs → f a ≡ f b → a ≡ b) →
  Nodup xs → Nodup (map f xs)
nodup-map f [] _ nodup[] = nodup[]
nodup-map f (x ∷ xs) inj (x∉ ∷ᵈ nxs) =
  (λ mem → x∉ (source mem)) ∷ᵈ nodup-map f xs inj-tail nxs
  where
  source : f x ∈ map f xs → x ∈ xs
  source mem with fiber-map xs mem
  ... | fiber z mz eq =
    subst (_∈ xs) (sym (inj here (there mz) (sym eq))) mz
  inj-tail : ∀ {a b} → a ∈ xs → b ∈ xs → f a ≡ f b → a ≡ b
  inj-tail ma mb eq = inj (there ma) (there mb) eq

-- A duplicate-free list is no longer than a list that contains each of its
-- entries. One exhibited match is removed at each step.
length-insert : {A : Set} (before after : List A) (x : A) →
  length (before ++ x ∷ after) ≡ suc (length (before ++ after))
length-insert []           after x = refl
length-insert (y ∷ before) after x rewrite length-insert before after x = refl

length-≤-nodup-subset : {A : Set} {left right : List A} →
  Nodup left → (∀ value → value ∈ left → value ∈ right) →
  length left ≤ length right
length-≤-nodup-subset {left = []} _ _ = z≤n
length-≤-nodup-subset {left = value ∷ left} (value∉ ∷ᵈ nleft) subset
  with split-∈ (subset value here)
... | located before after path rewrite path =
  subst (λ n → suc (length left) ≤ n)
    (sym (length-insert before after value))
    (s≤s (length-≤-nodup-subset nleft tail-subset))
  where
  tail-subset : ∀ w → w ∈ left → w ∈ before ++ after
  tail-subset w mem with ∈-++ before (value ∷ after) (subset w (there mem))
  ... | inl inBefore = ∈-++ˡ inBefore
  ... | inr here = ⊥-elim (value∉ mem)
  ... | inr (there inAfter) = ∈-++ʳ before inAfter

-- Cartesian enumeration with the right coordinate varying fastest. Every
-- pair of listed entries appears once for each way of choosing its
-- coordinates from the two lists.
pairList : {A B : Set} → List A → List B → List (A × B)
pairList []       _  = []
pairList (a ∷ as) bs = map (λ b → (a , b)) bs ++ pairList as bs

∈-pairList-forward : {A B : Set} {a : A} {b : B} (xs : List A) (ys : List B) →
  (a , b) ∈ pairList xs ys → (a ∈ xs) × (b ∈ ys)
∈-pairList-forward []       ys ()
∈-pairList-forward (x ∷ xs) ys mem with ∈-++ (map (λ c → (x , c)) ys) (pairList xs ys) mem
∈-pairList-forward (x ∷ xs) ys mem | inl inRow with fiber-map ys inRow
... | fiber c mc refl = here , mc
∈-pairList-forward (x ∷ xs) ys mem | inr inTail with ∈-pairList-forward xs ys inTail
... | a∈ , b∈ = there a∈ , b∈

∈-pairList-backward : {A B : Set} {a : A} {b : B} (xs : List A) (ys : List B) →
  a ∈ xs → b ∈ ys → (a , b) ∈ pairList xs ys
∈-pairList-backward {B = B} (x ∷ xs) ys here b∈ = ∈-++ˡ (pair-row ys b∈)
  where
  pair-row : ∀ {c} (zs : List B) → c ∈ zs → (x , c) ∈ map (λ d → (x , d)) zs
  pair-row (_ ∷ zs) here        = here
  pair-row (_ ∷ zs) (there mem) = there (pair-row zs mem)
∈-pairList-backward (x ∷ xs) ys (there a∈) b∈ =
  ∈-++ʳ (map (λ c → (x , c)) ys) (∈-pairList-backward xs ys a∈ b∈)

pairList-length : {A B : Set} (xs : List A) (ys : List B) →
  length (pairList xs ys) ≡ length xs * length ys
pairList-length []       ys = refl
pairList-length (x ∷ xs) ys =
  begin
    length (map (λ b → (x , b)) ys ++ pairList xs ys)
  ≡⟨ length-++ (map (λ b → (x , b)) ys) (pairList xs ys) ⟩
    length (map (λ b → (x , b)) ys) + length (pairList xs ys)
  ≡⟨ cong₂ _+_ (length-map (λ b → (x , b)) ys) (pairList-length xs ys) ⟩
    length ys + length xs * length ys
  ∎

-- Concatenation stays duplicate-free when the two sides share no entry.
nodup-++ : {A : Set} {xs ys : List A} →
  Nodup xs → Nodup ys → (∀ a → a ∈ xs → a ∈ ys → ⊥) → Nodup (xs ++ ys)
nodup-++ {xs = []} _ nys _ = nys
nodup-++ {xs = x ∷ xs} {ys = ys} (x∉ ∷ᵈ nxs) nys disj =
  clash ∷ᵈ nodup-++ nxs nys (λ a ma my → disj a (there ma) my)
  where
  clash : x ∈ xs ++ ys → ⊥
  clash mem with ∈-++ xs ys mem
  ... | inl inXs = x∉ inXs
  ... | inr inYs = disj x here inYs

-- Two duplicate-free lists have a duplicate-free cartesian enumeration.
-- A row is duplicate-free because the left coordinate is fixed, and distinct
-- rows cannot meet because their left coordinates differ.
pairList-nodup : {A B : Set} (xs : List A) (ys : List B) →
  Nodup xs → Nodup ys → Nodup (pairList xs ys)
pairList-nodup []       ys nodup[] _ = nodup[]
pairList-nodup (x ∷ xs) ys (x∉ ∷ᵈ nxs) nys =
  nodup-++ (nodup-map (λ b → (x , b)) ys row-inj nys)
           (pairList-nodup xs ys nxs nys)
           rows-apart
  where
  row-inj : ∀ {a b} → a ∈ ys → b ∈ ys → (x , a) ≡ (x , b) → a ≡ b
  row-inj _ _ eq = cong snd eq
  rows-apart : ∀ p → p ∈ map (λ b → (x , b)) ys → p ∈ pairList xs ys → ⊥
  rows-apart p inRow inTail with fiber-map ys inRow
  ... | fiber b _ eq =
    x∉ (fst (∈-pairList-forward xs ys
              (subst (_∈ pairList xs ys) (sym eq) inTail)))
