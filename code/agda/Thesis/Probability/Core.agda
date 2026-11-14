module Thesis.Probability.Core where

open import Thesis.Equality
open import Thesis.Bool
open import Thesis.Nat
open import Thesis.List
open import Thesis.Fin hiding (zero; suc)

-- Finite probability is carried by Boolean events and by nonnegative rational
-- presentations. An event is a test that can be evaluated at a sample. A
-- rational presentation is a numerator over a positive denominator. Two
-- presentations stand for the same magnitude when their cross-multiples agree,
-- so no reduced representative is chosen, and a ratio whose divisor is zero
-- is not given a value.

------------------------------------------------------------------------
-- Boolean folds over a finite index
------------------------------------------------------------------------

-- Compare two natural numbers by recursion on their unary structure.
natBeq : ℕ → ℕ → Bool
natBeq zero zero       = true
natBeq zero (suc _)    = false
natBeq (suc _) zero    = false
natBeq (suc m) (suc n) = natBeq m n

-- The comparison does not depend on which argument is written first.
natBeq-comm : ∀ m n → natBeq m n ≡ natBeq n m
natBeq-comm zero zero       = refl
natBeq-comm zero (suc _)    = refl
natBeq-comm (suc _) zero    = refl
natBeq-comm (suc m) (suc n) = natBeq-comm m n

-- A number compares equal to itself.
natBeq-refl : ∀ n → natBeq n n ≡ true
natBeq-refl zero    = refl
natBeq-refl (suc n) = natBeq-refl n

-- Two coordinates agree when their positions do.
finBeq : ∀ {n} → Fin n → Fin n → Bool
finBeq i j = natBeq (toℕ i) (toℕ j)

-- Conjunction of a Boolean family over every coordinate below n. The empty
-- family is true. A larger family is the earlier conjunction together with
-- the value at the last coordinate.
finAll : ∀ n → (Fin n → Bool) → Bool
finAll zero     _ = true
finAll (suc n) p = finAll n (λ i → p (castSucc i)) ∧ p last

-- Disjunction of the same kind of family. The empty family is false.
finAny : ∀ n → (Fin n → Bool) → Bool
finAny zero     _ = false
finAny (suc n) p = finAny n (λ i → p (castSucc i)) ∨ p last

-- A constantly true family is accepted at every finite length.
finAll-true : ∀ n → finAll n (λ _ → true) ≡ true
finAll-true zero     = refl
finAll-true (suc n) rewrite finAll-true n = refl

-- Families that agree at every coordinate have the same conjunction. The
-- agreement is used at each coordinate; the two families are not identified.
finAll-cong : ∀ n {p q : Fin n → Bool} → (∀ i → p i ≡ q i) → finAll n p ≡ finAll n q
finAll-cong zero     _ = refl
finAll-cong (suc n) h rewrite finAll-cong n (λ i → h (castSucc i)) | h last = refl

∧-true : ∀ b c → b ∧ c ≡ true → (b ≡ true) × (c ≡ true)
∧-true true  true  refl = refl , refl
∧-true true  false ()
∧-true false _     ()

∧-intro : ∀ {b c} → b ≡ true → c ≡ true → b ∧ c ≡ true
∧-intro {true} {true} _ _ = refl
∧-intro {true} {false} _ ()
∧-intro {false} {_} () _

-- The conjunction is true exactly when every coordinate is true.
finAll-of-all : ∀ n (p : Fin n → Bool) → (∀ i → p i ≡ true) → finAll n p ≡ true
finAll-of-all zero     p _ = refl
finAll-of-all (suc n) p h =
  ∧-intro (finAll-of-all n (λ j → p (castSucc j)) (λ j → h (castSucc j))) (h last)

finAll-at : ∀ n (p : Fin n → Bool) → finAll n p ≡ true → ∀ i → p i ≡ true
finAll-at zero     p _ i = ⊥-elim (no-fin i)
finAll-at (suc n) p h i with ∧-true _ _ h
... | earlier-true , last-true with prefix i
...   | before j = finAll-at n (λ k → p (castSucc k)) earlier-true j
...   | end      = last-true

finAny-cong : ∀ n {p q : Fin n → Bool} → (∀ i → p i ≡ q i) → finAny n p ≡ finAny n q
finAny-cong zero     _ = refl
finAny-cong (suc n) h rewrite finAny-cong n (λ i → h (castSucc i)) | h last = refl

∨-false : ∀ b c → b ∨ c ≡ false → (b ≡ false) × (c ≡ false)
∨-false false false refl = refl , refl
∨-false false true  ()
∨-false true  _     ()

-- Both bits of a false disjunction are false.
∨-false-intro : ∀ {b c} → b ≡ false → c ≡ false → b ∨ c ≡ false
∨-false-intro {false} {false} _ _ = refl
∨-false-intro {false} {true}  _ ()
∨-false-intro {true}  {_}    () _

-- A true right bit makes the disjunction true, whatever the left bit is.
∨-true-right : ∀ b → b ∨ true ≡ true
∨-true-right true  = refl
∨-true-right false = refl

-- The disjunction is false exactly when every coordinate is false.
finAny-of-none : ∀ n (p : Fin n → Bool) → (∀ i → p i ≡ false) → finAny n p ≡ false
finAny-of-none zero     p _ = refl
finAny-of-none (suc n) p h =
  ∨-false-intro (finAny-of-none n (λ j → p (castSucc j)) (λ j → h (castSucc j))) (h last)

finAny-at-false : ∀ n (p : Fin n → Bool) → finAny n p ≡ false → ∀ i → p i ≡ false
finAny-at-false zero     p _ i = ⊥-elim (no-fin i)
finAny-at-false (suc n) p h i with ∨-false _ _ h
... | earlier-false , last-false with prefix i
...   | before j = finAny-at-false n (λ k → p (castSucc k)) earlier-false j
...   | end      = last-false

-- One true coordinate makes the disjunction true.
finAny-true-of : ∀ n (p : Fin n → Bool) i → p i ≡ true → finAny n p ≡ true
finAny-true-of (suc n) p i hi with prefix i
... | before j rewrite finAny-true-of n (λ k → p (castSucc k)) j hi = refl
... | end      = trans (cong (finAny n (λ k → p (castSucc k)) ∨_) hi) (∨-true-right _)

-- A coordinate at which a family holds. The index is data recovered from the
-- finite fold.
record Holds {n : ℕ} (p : Fin n → Bool) : Set where
  constructor hold
  field
    index : Fin n
    holds : p index ≡ true

open Holds

-- The disjunction is true exactly when some coordinate holds.
finAny-holds : ∀ n (p : Fin n → Bool) → finAny n p ≡ true → Holds p
finAny-holds zero     p ()
finAny-holds (suc n) p h with finAny n (λ j → p (castSucc j)) in earlier | p last in at-last
... | true  | _     =
  let found = finAny-holds n (λ j → p (castSucc j)) earlier
  in hold (castSucc (index found)) (holds found)
... | false | true  = hold last at-last
... | false | false = ⊥-elim (true≢false h)
  where
  true≢false : false ≡ true → ⊥
  true≢false ()

finAny-of-holds : ∀ n (p : Fin n → Bool) → Holds p → finAny n p ≡ true
finAny-of-holds n p (hold i hi) = finAny-true-of n p i hi

------------------------------------------------------------------------
-- Boolean events
------------------------------------------------------------------------

-- A decidable event on a sample type. `true` means the sample is selected.
Event : Set → Set
Event X = X → Bool

-- The event containing every sample.
topEvent : {X : Set} → Event X
topEvent _ = true

-- The event containing no sample.
bottomEvent : {X : Set} → Event X
bottomEvent _ = false

-- Pointwise Boolean union, intersection, and complement.
union : {X : Set} → Event X → Event X → Event X
union E F x = E x ∨ F x

inter : {X : Set} → Event X → Event X → Event X
inter E F x = E x ∧ F x

complement : {X : Set} → Event X → Event X
complement E x = not (E x)

-- Finite union. The empty list selects nothing.
unionList : {X : Set} → List (Event X) → Event X
unionList []             = bottomEvent
unionList (event ∷ rest) = union event (unionList rest)

-- No sample lies in both events.
disjoint : {X : Set} → Event X → Event X → Set
disjoint E F = ∀ x → E x ≡ true → F x ≡ true → ⊥

false≢true : false ≢ true
false≢true ()

-- How many entries of a finite list the event selects.
count : {X : Set} → List X → Event X → ℕ
count xs E = countP E xs

-- A count is a natural number, hence at least zero.
count-nonneg : {X : Set} (xs : List X) (E : Event X) → zero ≤ count xs E
count-nonneg _ _ = z≤n

-- An event cannot select more entries than the list contains.
count-≤-length : {X : Set} (xs : List X) (E : Event X) → count xs E ≤ length xs
count-≤-length xs E = countP-≤-length E xs

count-top : {X : Set} (xs : List X) → count xs topEvent ≡ length xs
count-top = countP-top

-- The empty event selects nothing from a finite enumeration.
count-bottom : {X : Set} (xs : List X) → count xs bottomEvent ≡ zero
count-bottom = countP-bottom

-- Events that agree at every sample have the same count on a finite list.
-- The tests are not identified; only their values on samples are used.
count-cong : {X : Set} {xs : List X} {E F : Event X} →
             (∀ x → E x ≡ F x) → count xs E ≡ count xs F
count-cong {xs = xs} h = countP-cong xs h

-- Reordering a finite enumeration does not change an event count.
count-reindex : {X : Set} {xs ys : List X} → Perm xs ys →
                (E : Event X) → count xs E ≡ count ys E
count-reindex π E = countP-perm E π

∧-comm : ∀ b c → b ∧ c ≡ c ∧ b
∧-comm false false = refl
∧-comm false true  = refl
∧-comm true  false = refl
∧-comm true  true  = refl

-- Conjunction associates. A true left factor disappears, and a false one
-- makes both associations false.
∧-assoc : ∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
∧-assoc true  b c = refl
∧-assoc false b c = refl

count-inter-comm : {X : Set} (xs : List X) (E F : Event X) →
                   count xs (inter E F) ≡ count xs (inter F E)
count-inter-comm xs E F =
  count-cong {xs = xs} {E = inter E F} {F = inter F E}
    (λ x → ∧-comm (E x) (F x))

-- A sample of two disjoint events contributes to at most one count, so the
-- union count is the sum of the two counts.
count-union-disjoint : {X : Set} (xs : List X) (E F : Event X) →
                       disjoint E F →
                       count xs (union E F) ≡ count xs E + count xs F
count-union-disjoint []       E F _ = refl
count-union-disjoint (x ∷ xs) E F h with E x in e | F x in f
... | false | false rewrite count-union-disjoint xs E F h = refl
... | false | true
    rewrite count-union-disjoint xs E F h
          | +-suc (count xs E) (count xs F) = refl
... | true  | false rewrite count-union-disjoint xs E F h = refl
... | true  | true  = ⊥-elim (h x e f)

-- An event and its complement partition every finite enumeration.
count-add-count-complement : {X : Set} (xs : List X) (E : Event X) →
  count xs E + count xs (complement E) ≡ length xs
count-add-count-complement []       E = refl
count-add-count-complement (x ∷ xs) E with E x
... | true  rewrite count-add-count-complement xs E = refl
... | false rewrite +-suc (count xs E) (count xs (complement E))
                  | count-add-count-complement xs E = refl

-- An event shares no sample with its complement.
disjoint-complement : {X : Set} (E : Event X) → disjoint E (complement E)
disjoint-complement E x hE hC with E x
disjoint-complement E x hE hC | true  = false≢true hC
disjoint-complement E x hE hC | false = false≢true hE

-- At every sample, an event together with its complement accepts that sample.
union-complement : {X : Set} (E : Event X) (x : X) →
                   union E (complement E) x ≡ topEvent x
union-complement E x with E x
... | true  = refl
... | false = refl

-- Disjointness from every listed event yields disjointness from their union.
disjoint-unionList : {X : Set} {E : Event X} {events : List (Event X)} →
                     All (λ F → disjoint E F) events →
                     disjoint E (unionList events)
disjoint-unionList {events = []}         []       x hE ()
disjoint-unionList {events = F ∷ events} (d ∷ ds) x hE hU
  with F x in eF | unionList events x in eU
... | true  | _     = d x hE eF
... | false | true  = disjoint-unionList ds x hE eU
... | false | false = false≢true hU

-- A pairwise disjoint finite union has the sum of its member counts.
count-unionList-pairwise : {X : Set} (xs : List X) {events : List (Event X)} →
                           Pairwise disjoint events →
                           count xs (unionList events) ≡ sum (map (count xs) events)
count-unionList-pairwise xs [] = count-bottom xs
count-unionList-pairwise xs (_∷_ {x = E} {xs = es} alls pw) =
  begin
    count xs (union E (unionList es))
  ≡⟨ count-union-disjoint xs E (unionList es) (disjoint-unionList alls) ⟩
    count xs E + count xs (unionList es)
  ≡⟨ cong (count xs E +_) (count-unionList-pairwise xs {es} pw) ⟩
    count xs E + sum (map (count xs) es)
  ∎

-- If every sample of `E` is a sample of `F`, then `E` cannot outcount `F`.
count-mono : {X : Set} {xs : List X} {E F : Event X} →
             (∀ x → E x ≡ true → F x ≡ true) →
             count xs E ≤ count xs F
count-mono {xs = []}     h = z≤n
count-mono {xs = x ∷ xs} {E} {F} h with E x in e
... | false = ≤-trans (count-mono {xs = xs} h) (≤-extra (F x) (count xs F))
  where
  ≤-extra : ∀ b n → n ≤ extra b + n
  ≤-extra false n = ≤-refl n
  ≤-extra true  n = ≤-step (≤-refl n)
... | true rewrite h x e = s≤s (count-mono {xs = xs} h)

-- Samples in the union, together with samples in the intersection, match the
-- two events counted separately.
count-union-inter : {X : Set} (xs : List X) (E F : Event X) →
  count xs (union E F) + count xs (inter E F) ≡ count xs E + count xs F
count-union-inter []       E F = refl
count-union-inter (x ∷ xs) E F with E x | F x
... | false | false rewrite count-union-inter xs E F = refl
... | false | true
    rewrite count-union-inter xs E F
          | +-suc (count xs E) (count xs F) = refl
... | true  | false rewrite count-union-inter xs E F = refl
... | true  | true =
  begin
    suc (count xs (union E F)) + suc (count xs (inter E F))
  ≡⟨ cong suc (+-suc (count xs (union E F)) (count xs (inter E F))) ⟩
    suc (suc (count xs (union E F) + count xs (inter E F)))
  ≡⟨ cong (λ n → suc (suc n)) (count-union-inter xs E F) ⟩
    suc (suc (count xs E + count xs F))
  ≡⟨ cong suc (sym (+-suc (count xs E) (count xs F))) ⟩
    suc (count xs E + suc (count xs F))
  ∎

------------------------------------------------------------------------
-- Inspection status
------------------------------------------------------------------------

-- The three outcomes of a finite inspection of a claim.
data Status : Set where
  proved refuted unresolved : Status

isProved : Status → Bool
isProved proved = true
isProved _      = false

isRefuted : Status → Bool
isRefuted refuted = true
isRefuted _       = false

isUnresolved : Status → Bool
isUnresolved unresolved = true
isUnresolved _          = false

-- Every status satisfies exactly one of the three tests.
status-exhaustive : ∀ s → isProved s ∨ isRefuted s ∨ isUnresolved s ≡ true
status-exhaustive proved     = refl
status-exhaustive refuted    = refl
status-exhaustive unresolved = refl

proved-refuted-disjoint : ∀ s → isProved s ≡ true → isRefuted s ≡ true → ⊥
proved-refuted-disjoint proved     _  ()
proved-refuted-disjoint refuted    () _
proved-refuted-disjoint unresolved () _

proved-unresolved-disjoint : ∀ s → isProved s ≡ true → isUnresolved s ≡ true → ⊥
proved-unresolved-disjoint proved     _  ()
proved-unresolved-disjoint refuted    () _
proved-unresolved-disjoint unresolved () _

refuted-unresolved-disjoint : ∀ s → isRefuted s ≡ true → isUnresolved s ≡ true → ⊥
refuted-unresolved-disjoint proved     () _
refuted-unresolved-disjoint refuted    _  ()
refuted-unresolved-disjoint unresolved () _

-- A finite inspection of a state-indexed claim.
--
-- The status tag is a concrete function, so it can be evaluated. `proved`
-- and `refuted` are sound for the claim they report: a proved state carries
-- a witness, and a refuted state excludes one. `unresolved` has no soundness
-- field, because it only records that this inspection found neither.
record Inspection (S : Set) (A : S → Set) : Set where
  constructor inspection
  field
    status        : S → Status
    proved-sound  : ∀ s → status s ≡ proved → A s
    refuted-sound : ∀ s → status s ≡ refuted → A s → ⊥

open Inspection

provedEvent : {S : Set} {A : S → Set} → Inspection S A → Event S
provedEvent I s = isProved (status I s)

refutedEvent : {S : Set} {A : S → Set} → Inspection S A → Event S
refutedEvent I s = isRefuted (status I s)

unresolvedEvent : {S : Set} {A : S → Set} → Inspection S A → Event S
unresolvedEvent I s = isUnresolved (status I s)

inspection-proved-refuted : {S : Set} {A : S → Set} (I : Inspection S A) →
                            disjoint (provedEvent I) (refutedEvent I)
inspection-proved-refuted I s hp hr =
  proved-refuted-disjoint (status I s) hp hr

inspection-proved-unresolved : {S : Set} {A : S → Set} (I : Inspection S A) →
                               disjoint (provedEvent I) (unresolvedEvent I)
inspection-proved-unresolved I s hp hu =
  proved-unresolved-disjoint (status I s) hp hu

inspection-refuted-unresolved : {S : Set} {A : S → Set} (I : Inspection S A) →
                                disjoint (refutedEvent I) (unresolvedEvent I)
inspection-refuted-unresolved I s hr hu =
  refuted-unresolved-disjoint (status I s) hr hu

-- On a finite list, the three status counts sum to the length. Each state
-- carries one tag, the corresponding tests are disjoint, and together they
-- accept every state.
status-count-partition : {S : Set} (xs : List S) (tag : S → Status) →
  count xs (λ s → isProved (tag s)) +
  count xs (λ s → isRefuted (tag s)) +
  count xs (λ s → isUnresolved (tag s)) ≡ length xs
status-count-partition {S} xs tag =
  begin
    count xs P + count xs R + count xs U
  ≡⟨ cong (_+ count xs U) (sym (count-union-disjoint xs P R provedR)) ⟩
    count xs (union P R) + count xs U
  ≡⟨ sym (count-union-disjoint xs (union P R) U provedRU) ⟩
    count xs (union (union P R) U)
  ≡⟨ count-cong {xs = xs} cover ⟩
    count xs topEvent
  ≡⟨ count-top xs ⟩
    length xs
  ∎
  where
  P : Event S
  P = λ s → isProved (tag s)
  R : Event S
  R = λ s → isRefuted (tag s)
  U : Event S
  U = λ s → isUnresolved (tag s)

  provedR : disjoint P R
  provedR s hp hr = proved-refuted-disjoint (tag s) hp hr

  provedRU : disjoint (union P R) U
  provedRU s hUnion hu with tag s
  ... | proved     = false≢true hu
  ... | refuted    = false≢true hu
  ... | unresolved = false≢true hUnion

  cover : ∀ s → union (union P R) U s ≡ true
  cover s with tag s
  ... | proved     = refl
  ... | refuted    = refl
  ... | unresolved = refl

-- Rational presentations, cross-multiplication, and their order. The name
-- `zero` for the zero presentation stays qualified, so it is not confused
-- with the natural number zero.
open import Thesis.Probability.QProb public hiding (zero)
