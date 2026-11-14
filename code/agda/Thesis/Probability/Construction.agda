module Thesis.Probability.Construction where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
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

-- Coordinatewise decidable equality decides equality of the telescope.
assign-≟ : {n : ℕ} {V : Fin n → Set} →
  (∀ i → (x y : V i) → Dec (x ≡ y)) →
  (a b : Assign n V) → Dec (a ≡ b)
assign-≟ {zero} _ empty empty = yes refl
assign-≟ {suc n} {V} eq (snoc ae ah) (snoc be bh)
  with eq last ah bh | assign-≟ {V = earlier V} (λ i → eq (castSucc i)) ae be
... | yes p | yes q =
  yes (trans (cong (λ r → snoc {n = n} {V = V} r ah) q)
             (cong (snoc {n = n} {V = V} be) p))
... | yes _ | no nq =
  no (λ e → nq (assign-ext {V = earlier V} ae be (λ j →
    trans (sym (lookup-castSucc {V = V} ae ah j))
      (trans (lookup-cong e (castSucc j)) (lookup-castSucc {V = V} be bh j)))))
... | no np | _ =
  no (λ e → np (trans (sym (lookup-last {V = V} ae ah))
                 (trans (lookup-cong e last) (lookup-last {V = V} be bh))))

-- Sequences whose entries live one universe above ordinary sets. Assignment
-- telescopes sit there, so their enumerations cannot be ordinary lists.
data Seq (A : Set₁) : Set₁ where
  []  : Seq A
  _∷_ : A → Seq A → Seq A

infixr 5 _∷_

map-seq : {A B : Set₁} → (A → B) → Seq A → Seq B
map-seq f []       = []
map-seq f (x ∷ xs) = f x ∷ map-seq f xs

_++ˢ_ : {A : Set₁} → Seq A → Seq A → Seq A
[]       ++ˢ ys = ys
(x ∷ xs) ++ˢ ys = x ∷ (xs ++ˢ ys)

infixr 5 _++ˢ_

-- The outer list is an ordinary list of last-coordinate values. Each value
-- produces a sequence of assignments.
flat-seq : {A : Set} {B : Set₁} → (A → Seq B) → List A → Seq B
flat-seq f []       = []
flat-seq f (x ∷ xs) = f x ++ˢ flat-seq f xs

infix 4 _∈ˢ_

data _∈ˢ_ {A : Set₁} (x : A) : Seq A → Set₁ where
  hereˢ  : ∀ {xs} → x ∈ˢ (x ∷ xs)
  thereˢ : ∀ {y xs} → x ∈ˢ xs → x ∈ˢ (y ∷ xs)

∈-map-seq : {A B : Set₁} {f : A → B} {x : A} {xs : Seq A} →
  x ∈ˢ xs → f x ∈ˢ map-seq f xs
∈-map-seq hereˢ        = hereˢ
∈-map-seq (thereˢ mem) = thereˢ (∈-map-seq mem)

∈-++ˡˢ : {A : Set₁} {x : A} {xs ys : Seq A} → x ∈ˢ xs → x ∈ˢ xs ++ˢ ys
∈-++ˡˢ hereˢ        = hereˢ
∈-++ˡˢ (thereˢ mem) = thereˢ (∈-++ˡˢ mem)

∈-++ʳˢ : {A : Set₁} {x : A} (xs : Seq A) {ys : Seq A} →
  x ∈ˢ ys → x ∈ˢ xs ++ˢ ys
∈-++ʳˢ []       mem = mem
∈-++ʳˢ (_ ∷ xs) mem = thereˢ (∈-++ʳˢ xs mem)

∈-flat-seq : {A : Set} {B : Set₁} {f : A → Seq B} {x : A} {y : B}
  {xs : List A} → x ∈ xs → y ∈ˢ f x → y ∈ˢ flat-seq f xs
∈-flat-seq here        mem = ∈-++ˡˢ mem
∈-flat-seq (there mem) y∈  = ∈-++ʳˢ _ (∈-flat-seq mem y∈)

-- Every way of choosing one listed value at each coordinate. The last
-- coordinate varies in the outer list, and each choice extends an assignment
-- to the earlier coordinates.
enumerate : {n : ℕ} {V : Fin n → Set} →
  (∀ i → List (V i)) → Seq (Assign n V)
enumerate {zero}  _ = empty ∷ []
enumerate {suc n} {V} values =
  flat-seq (λ final →
    map-seq (λ front → snoc {n = n} {V = V} front final)
      (enumerate {V = earlier V} (λ i → values (castSucc i))))
    (values last)

-- If every coordinate list contains every value of that coordinate, every
-- assignment appears in the enumeration.
enum-complete : {n : ℕ} {V : Fin n → Set}
  (values : ∀ i → List (V i)) →
  (∀ i (x : V i) → x ∈ values i) →
  (a : Assign n V) → a ∈ˢ enumerate values
enum-complete {zero}  _ _ empty = hereˢ
enum-complete {suc n} {V} values complete (snoc front final) =
  ∈-flat-seq (complete last final)
    (∈-map-seq
      (enum-complete {V = earlier V} (λ i → values (castSucc i))
        (λ i x → complete (castSucc i) x) front))

-- A rectangular test accepts an assignment when every coordinate test accepts
-- the value stored there. The empty assignment is accepted.
rect : {n : ℕ} {V : Fin n → Set} →
  (∀ i → V i → Bool) → Assign n V → Bool
rect {zero}  _ empty = true
rect {suc n} {V} tests (snoc front final) =
  tests last final ∧ rect {V = earlier V} (λ i → tests (castSucc i)) front

-- The rectangle holds exactly when every coordinate test holds.
rect-holds : {n : ℕ} {V : Fin n → Set}
  (tests : ∀ i → V i → Bool) (a : Assign n V) →
  (rect tests a ≡ true → ∀ i → tests i (lookup a i) ≡ true)
  × ( (∀ i → tests i (lookup a i) ≡ true) → rect tests a ≡ true )
rect-holds {zero} tests empty =
  (λ _ i → ⊥-elim (no-fin i)) , (λ _ → refl)
rect-holds {suc n} {V} tests (snoc front final) =
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
  to-coords : rect tests (snoc front final) ≡ true →
              ∀ i → tests i (lookup (snoc front final) i) ≡ true
  to-coords holds i with prefix i
  ... | end = ∧-left holds
  ... | before j = fst tail (∧-right holds) j
  from-coords : (∀ i → tests i (lookup (snoc front final) i) ≡ true) →
                rect tests (snoc front final) ≡ true
  from-coords all =
    ∧-both
      (trans (sym (cong (tests last) (lookup-last {V = V} front final)))
             (all last))
      (snd tail (λ j →
        trans (sym (cong (earlier-tests j) (lookup-castSucc {V = V} front final j)))
              (all (castSucc j))))
