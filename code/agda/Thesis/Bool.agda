module Thesis.Bool where

-- Two-point type used as the carrier of decidable events. `true` means the
-- sample lies in the event. Boolean operations are the pointwise algebra of
-- those events; they do not decide an arbitrary proposition.

data Bool : Set where
  false true : Bool

not : Bool → Bool
not true  = false
not false = true

infixr 6 _∧_
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

-- Conditional used by counting. The two branches are values, not proofs,
-- so the choice is executable.
if_then_else_ : {A : Set} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f
