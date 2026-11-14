module Thesis.Equality where

-- Propositional identity is the intensional identity type. A proof `refl`
-- witnesses that the two sides are the same construction. Identity is not
-- reflected into definitional equality: a derived equation is used by
-- substitution along this type, one occurrence at a time.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- The empty type. A function into it is a refutation.
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

-- A claim is decided when a proof or a refutation is supplied as data.
-- No general excluded middle is assumed; only the procedures below decide
-- the relations they are written for.
data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

-- Disjoint union of two sets of constructions. Pattern matching on it chooses
-- a concrete side; it is not a proof-irrelevant or.
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 1 _⊎_

infix  4 _≡_ _≢_
infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} (x : A) {y : A} → x ≡ y → x ≡ y
_ ≡⟨⟩ q = q

_∎ : {A : Set} (x : A) → x ≡ x
x ∎ = refl
