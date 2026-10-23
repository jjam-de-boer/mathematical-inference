import Thesis.Causality.Derivation

namespace Thesis.Causality

/-!
# One distinguished subproof in the existing derivation language

A context records where an actual derivation may be replaced, with the hole's
two literal endpoint expressions fixed in its type. Its other subproofs remain
unchanged data. In particular, a binary congruence may have a nonreflexive
sibling: expression frames alone would not describe every enclosing proof.

Every constructor below is an existing structural derivation constructor
with exactly one distinguished recursive argument. Primitive probability and
do-rule leaves have no recursive argument, so they need no context constructor.
`fill` only rebuilds the old derivation; it adds no equation, certificate leaf,
serialized proof language, search procedure or permission to identify terms
having the same support status.
-/

variable {S : ObservedSignature} {G : ObservedGraph S} [RuleSeparation G]

/-- A one-hole proof tree. The hole's source and target are unchanged even
when symmetry or an enclosing congruence changes the whole proof's endpoints. -/
inductive DoCalculusDerivationContext (G : ObservedGraph S) [RuleSeparation G]
    (holeLeft holeRight : ProbabilityTerm S) : ProbabilityTerm S → ProbabilityTerm S → Type where
  | hole : DoCalculusDerivationContext G holeLeft holeRight holeLeft holeRight
  | symm {left right} (inner : DoCalculusDerivationContext G holeLeft holeRight left right) :
      DoCalculusDerivationContext G holeLeft holeRight right left
  | transLeft {left middle right} (inner : DoCalculusDerivationContext G holeLeft holeRight left middle)
      (fixed : DoCalculusDerivation G middle right) :
      DoCalculusDerivationContext G holeLeft holeRight left right
  | transRight {left middle right} (fixed : DoCalculusDerivation G left middle)
      (inner : DoCalculusDerivationContext G holeLeft holeRight middle right) :
      DoCalculusDerivationContext G holeLeft holeRight left right
  | marginalize {left right} (nodes : NodeSet S)
      (inner : DoCalculusDerivationContext G holeLeft holeRight left right) :
      DoCalculusDerivationContext G holeLeft holeRight (.marginalize nodes left) (.marginalize nodes right)
  | evaluateAt {left right} (reference : S.Assignment)
      (inner : DoCalculusDerivationContext G holeLeft holeRight left right) :
      DoCalculusDerivationContext G holeLeft holeRight (.evaluateAt reference left) (.evaluateAt reference right)
  | addLeft {left left' right right'} (inner : DoCalculusDerivationContext G holeLeft holeRight left left')
      (fixed : DoCalculusDerivation G right right') :
      DoCalculusDerivationContext G holeLeft holeRight (.add left right) (.add left' right')
  | addRight {left left' right right'} (fixed : DoCalculusDerivation G left left')
      (inner : DoCalculusDerivationContext G holeLeft holeRight right right') :
      DoCalculusDerivationContext G holeLeft holeRight (.add left right) (.add left' right')
  | multiplyLeft {left left' right right'} (inner : DoCalculusDerivationContext G holeLeft holeRight left left')
      (fixed : DoCalculusDerivation G right right') :
      DoCalculusDerivationContext G holeLeft holeRight (.multiply left right) (.multiply left' right')
  | multiplyRight {left left' right right'} (fixed : DoCalculusDerivation G left left')
      (inner : DoCalculusDerivationContext G holeLeft holeRight right right') :
      DoCalculusDerivationContext G holeLeft holeRight (.multiply left right) (.multiply left' right')
  | weightedLeft {weight weight' factor factor'}
      (inner : DoCalculusDerivationContext G holeLeft holeRight weight weight')
      (fixed : DoCalculusDerivation G factor factor') :
      DoCalculusDerivationContext G holeLeft holeRight (.weightedMultiply weight factor) (.weightedMultiply weight' factor')
  | weightedRight {weight weight' factor factor'} (fixed : DoCalculusDerivation G weight weight')
      (inner : DoCalculusDerivationContext G holeLeft holeRight factor factor') :
      DoCalculusDerivationContext G holeLeft holeRight (.weightedMultiply weight factor) (.weightedMultiply weight' factor')
  | divideLeft {left left' right right'} (inner : DoCalculusDerivationContext G holeLeft holeRight left left')
      (fixed : DoCalculusDerivation G right right') :
      DoCalculusDerivationContext G holeLeft holeRight (.divide left right) (.divide left' right')
  | divideRight {left left' right right'} (fixed : DoCalculusDerivation G left left')
      (inner : DoCalculusDerivationContext G holeLeft holeRight right right') :
      DoCalculusDerivationContext G holeLeft holeRight (.divide left right) (.divide left' right')
  | eqCongr {left left' right right'} (sameLeft : left = left') (sameRight : right = right')
      (inner : DoCalculusDerivationContext G holeLeft holeRight left' right') :
      DoCalculusDerivationContext G holeLeft holeRight left right

namespace DoCalculusDerivationContext

/-- Rebuild the original proof constructors, keeping all siblings and all
literal endpoints. No comparison or case analysis on the replacement is used. -/
def fill {holeLeft holeRight left right : ProbabilityTerm S}
    (context : DoCalculusDerivationContext G holeLeft holeRight left right)
    (replacement : DoCalculusDerivation G holeLeft holeRight) : DoCalculusDerivation G left right :=
  match context with
  | .hole => replacement
  | .symm inner => .symm (inner.fill replacement)
  | .transLeft inner fixed => .trans (inner.fill replacement) fixed
  | .transRight fixed inner => .trans fixed (inner.fill replacement)
  | .marginalize nodes inner => .marginalizeCongr nodes (inner.fill replacement)
  | .evaluateAt reference inner => .evaluateAtCongr reference (inner.fill replacement)
  | .addLeft inner fixed => .addCongr (inner.fill replacement) fixed
  | .addRight fixed inner => .addCongr fixed (inner.fill replacement)
  | .multiplyLeft inner fixed => .multiplyCongr (inner.fill replacement) fixed
  | .multiplyRight fixed inner => .multiplyCongr fixed (inner.fill replacement)
  | .weightedLeft inner fixed => .weightedMultiplyCongr (inner.fill replacement) fixed
  | .weightedRight fixed inner => .weightedMultiplyCongr fixed (inner.fill replacement)
  | .divideLeft inner fixed => .divideCongr (inner.fill replacement) fixed
  | .divideRight fixed inner => .divideCongr fixed (inner.fill replacement)
  | .eqCongr sameLeft sameRight inner => .eqCongr sameLeft sameRight (inner.fill replacement)

end DoCalculusDerivationContext
end Thesis.Causality
