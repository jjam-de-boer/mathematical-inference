module Thesis.Equality where

open import Agda.Primitive using (Level)

-- Propositional identity is the intensional identity type. A proof `refl`
-- witnesses that the two sides are the same construction. Identity is not
-- reflected into definitional equality: a derived equation is used by
-- substitution along this type, one occurrence at a time.

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- The empty type. A function into it is a refutation.
data ⊥ : Set where

⊥-elim : {a : Level} {A : Set a} → ⊥ → A
⊥-elim ()

_≢_ : {a : Level} {A : Set a} → A → A → Set a
x ≢ y = x ≡ y → ⊥

sym : {a : Level} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {a : Level} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {a b : Level} {A : Set a} {B : Set b} (f : A → B) {x y : A} →
       x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : {a b : Level} {A : Set a} (P : A → Set b) {x y : A} →
        x ≡ y → P x → P y
subst P refl px = px

-- A pair of independent constructions. Each component is retained.
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

infixr 4 _,_
infixr 2 _×_

open _×_ public

-- A claim is decided when a proof or a refutation is supplied as data.
-- No general excluded middle is assumed; only the procedures below decide
-- the relations they are written for.
data Dec {a : Level} (A : Set a) : Set a where
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

begin_ : {a : Level} {A : Set a} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : {a : Level} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {a : Level} {A : Set a} (x : A) {y : A} → x ≡ y → x ≡ y
_ ≡⟨⟩ q = q

_∎ : {a : Level} {A : Set a} (x : A) → x ≡ x
x ∎ = refl

-- Hedberg's theorem. When identity of a type is decided, any two proofs of
-- the same identity are themselves identical. The decision procedure picks
-- one canonical proof; every other proof is shown equal to that one by
-- transporting the reflexive case along the identity. This is used for
-- equations between natural numbers, Booleans, and finite coordinates, where
-- a decision procedure is written by recursion. It is not assumed for an
-- arbitrary identity.
uip : {a : Level} {A : Set a} (decide : (x y : A) → Dec (x ≡ y)) →
      {x y : A} (p q : x ≡ y) → p ≡ q
uip {a} {A} decide {x} {y} p q =
  begin
    p
  ≡⟨ path p ⟩
    trans (sym (canonical refl)) (canonical p)
  ≡⟨ cong (trans (sym (canonical refl))) (canonical-constant p q) ⟩
    trans (sym (canonical refl)) (canonical q)
  ≡⟨ sym (path q) ⟩
    q
  ∎
  where
  canonical : {z : A} → x ≡ z → x ≡ z
  canonical {z} r with decide x z
  ... | yes s = s
  ... | no ns = ⊥-elim (ns r)

  canonical-constant : {z : A} (r s : x ≡ z) → canonical r ≡ canonical s
  canonical-constant {z} r s with decide x z
  ... | yes _ = refl
  ... | no ns = ⊥-elim (ns r)

  subst-refl : {z : A} (r : x ≡ z) →
               subst (λ w → x ≡ w) r refl ≡ r
  subst-refl refl = refl

  cancel : {y : A} (c : x ≡ y) → trans (sym c) c ≡ refl
  cancel refl = refl

  slide : {z : A} (r : x ≡ z) (q c : x ≡ x) →
          subst (λ w → x ≡ w) r (trans q c) ≡
          trans q (subst (λ w → x ≡ w) r c)
  slide refl q c = refl

  follow : {z : A} (r : x ≡ z) →
           subst (λ w → x ≡ w) r (canonical refl) ≡ canonical r
  follow refl = refl

  path : {z : A} (r : x ≡ z) →
         r ≡ trans (sym (canonical refl)) (canonical r)
  path r =
    begin
      r
    ≡⟨ sym (subst-refl r) ⟩
      subst (λ w → x ≡ w) r refl
    ≡⟨ cong (subst (λ w → x ≡ w) r) (sym (cancel (canonical refl))) ⟩
      subst (λ w → x ≡ w) r (trans (sym (canonical refl)) (canonical refl))
    ≡⟨ slide r (sym (canonical refl)) (canonical refl) ⟩
      trans (sym (canonical refl)) (subst (λ w → x ≡ w) r (canonical refl))
    ≡⟨ cong (trans (sym (canonical refl))) (follow r) ⟩
      trans (sym (canonical refl)) (canonical r)
    ∎
