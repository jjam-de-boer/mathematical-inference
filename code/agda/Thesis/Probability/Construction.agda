module Thesis.Probability.Construction where

open import Thesis.Equality
open import Thesis.Nat
open import Thesis.Fin renaming (zero to fzero; suc to fsuc)

-- A dependent assignment is one inductive telescope. The empty telescope
-- applies to a coordinate bound of zero. A longer telescope stores an
-- assignment to the earlier coordinates and one value at the last coordinate.
-- The value family is a parameter of the constructor, so the earlier family
-- is named once and is not rebuilt as a separate function at each use.

earlier : {n : ℕ} → (Fin (suc n) → Set) → Fin n → Set
earlier V i = V (castSucc i)

data Assign : (n : ℕ) → (Fin n → Set) → Set₁ where
  empty : {V : Fin zero → Set} → Assign zero V
  snoc  : {n : ℕ} {V : Fin (suc n) → Set} →
          Assign n (earlier V) → V last → Assign (suc n) V

-- Read the value at a coordinate by classifying the coordinate as an earlier
-- place or the last place.
mutual
  lookup : {n : ℕ} {V : Fin n → Set} → Assign n V → (i : Fin n) → V i
  lookup empty ()
  lookup (snoc front final) i = read front final i (prefix i)

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
  lookup (snoc front final) last ≡ final
lookup-last {n} {V} front final =
  cong (read {V = V} front final last) (prefix-last {n})

lookup-castSucc : {n : ℕ} {V : Fin (suc n) → Set}
  (front : Assign n (earlier V)) (final : V last) (j : Fin n) →
  lookup (snoc front final) (castSucc j) ≡ lookup front j
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
assign-ext empty empty _ = refl
assign-ext {suc n} {V} (snoc ae ah) (snoc be bh) h =
  trans
    (cong (λ p → snoc {n = n} {V = V} p ah)
      (assign-ext {n = n} {V = earlier V} ae be (λ j →
        trans (sym (lookup-castSucc {V = V} ae ah j))
          (trans (h (castSucc j)) (lookup-castSucc {V = V} be bh j)))))
    (cong (snoc {n = n} {V = V} be)
      (trans (sym (lookup-last {V = V} ae ah))
        (trans (h last) (lookup-last {V = V} be bh))))
