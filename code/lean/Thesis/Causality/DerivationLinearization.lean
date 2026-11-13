import Thesis.Causality.Derivation

namespace Thesis.Causality

/-!
# Elementary steps and finite paths for the existing derivation language

This is a change of proof presentation, not a stronger equation calculus.
An elementary step has exactly one existing probability/do-rule or strict
multiplication AC leaf, possibly reversed and placed under unary expression
frames. In particular it cannot hide a transitivity tree. A path is a finite
cons-list of these steps, with its source and target retained in its type.

`DoCalculusDerivation.linearize` serializes all original constructors. Binary
congruence changes the left operand first and then the right. For weighted
multiplication this means changing the weight before its factor; the native
support module separately proves that this ordering loses no applications.
Neither this syntax transformation nor finiteness of each resulting path
provides a bound on all possible paths, a search procedure, or a stopping law.
-/

variable {S : ObservedSignature} {G : ObservedGraph S} [RuleSeparation G]

/-- A single expression layer with one distinguished hole. The unchanged
operand remains literal syntax, including any unsupported conditional inside
a factor that a defined zero weight may legitimately skip. -/
inductive ProbabilityTermFrame (S : ObservedSignature) where
  | marginalize (nodes : NodeSet S)
  | evaluateAt (reference : S.Assignment)
  | addLeft (right : ProbabilityTerm S)
  | addRight (left : ProbabilityTerm S)
  | multiplyLeft (right : ProbabilityTerm S)
  | multiplyRight (left : ProbabilityTerm S)
  | weightedLeft (factor : ProbabilityTerm S)
  | weightedRight (weight : ProbabilityTerm S)
  | divideLeft (denominator : ProbabilityTerm S)
  | divideRight (numerator : ProbabilityTerm S)

namespace ProbabilityTermFrame

def fill : ProbabilityTermFrame S → ProbabilityTerm S → ProbabilityTerm S
  | .marginalize nodes, term => .marginalize nodes term
  | .evaluateAt reference, term => .evaluateAt reference term
  | .addLeft right, term => .add term right
  | .addRight left, term => .add left term
  | .multiplyLeft right, term => .multiply term right
  | .multiplyRight left, term => .multiply left term
  | .weightedLeft factor, term => .weightedMultiply term factor
  | .weightedRight weight, term => .weightedMultiply weight term
  | .divideLeft denominator, term => .divide term denominator
  | .divideRight numerator, term => .divide numerator term

/-- Fill a frame using only an original congruence and reflexivity for its
unchanged operand. There is no evaluation or assumed numerical equality. -/
def lift (frame : ProbabilityTermFrame S) {left right : ProbabilityTerm S}
    (inner : DoCalculusDerivation G left right) :
    DoCalculusDerivation G (frame.fill left) (frame.fill right) :=
  match frame with
  | .marginalize nodes => .marginalizeCongr nodes inner
  | .evaluateAt reference => .evaluateAtCongr reference inner
  | .addLeft right => .addCongr inner (.refl right)
  | .addRight left => .addCongr (.refl left) inner
  | .multiplyLeft right => .multiplyCongr inner (.refl right)
  | .multiplyRight left => .multiplyCongr (.refl left) inner
  | .weightedLeft factor => .weightedMultiplyCongr inner (.refl factor)
  | .weightedRight weight => .weightedMultiplyCongr (.refl weight) inner
  | .divideLeft denominator => .divideCongr inner (.refl denominator)
  | .divideRight numerator => .divideCongr (.refl numerator) inner

end ProbabilityTermFrame

/-- The original nonstructural leaves, with no arbitrary derivation field.
For a fixed finite signature/graph the four-mask leaves have finitely many
instances. The two strict multiplication leaves remain AC schemas. -/
inductive DoCalculusAtom (G : ObservedGraph S) [RuleSeparation G] :
    ProbabilityTerm S → ProbabilityTerm S → Type where
  | doRule {left right} (application : DoRuleApplication G left right) :
      DoCalculusAtom G (.kernel left) (.kernel right)
  | marginalization (x y z w) (disjoint : FourWayDisjoint x y z w) :
      DoCalculusAtom G (.kernel ⟨y, x, w⟩)
        (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩))
  | conditioning (x y z w) (disjoint : FourWayDisjoint x y z w) :
      DoCalculusAtom G (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.divide (.kernel ⟨NodeSet.union y z, x, w⟩) (.kernel ⟨z, x, w⟩))
  | chain (x y z w) (disjoint : FourWayDisjoint x y z w) :
      DoCalculusAtom G (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.multiply (.kernel ⟨y, x, NodeSet.union z w⟩) (.kernel ⟨z, x, w⟩))
  | weightedChain (x y z w) (disjoint : FourWayDisjoint x y z w) :
      DoCalculusAtom G (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.weightedMultiply (.kernel ⟨z, x, w⟩) (.kernel ⟨y, x, NodeSet.union z w⟩))
  | multiplyComm (left right) :
      DoCalculusAtom G (.multiply left right) (.multiply right left)
  | multiplyAssoc (first second third) :
      DoCalculusAtom G (.multiply (.multiply first second) third)
        (.multiply first (.multiply second third))

def DoCalculusAtom.toDerivation {left right : ProbabilityTerm S} :
    DoCalculusAtom G left right → DoCalculusDerivation G left right
  | .doRule application => .doRule application
  | .marginalization x y z w disjoint => .marginalization x y z w disjoint
  | .conditioning x y z w disjoint => .conditioning x y z w disjoint
  | .chain x y z w disjoint => .chain x y z w disjoint
  | .weightedChain x y z w disjoint => .weightedChain x y z w disjoint
  | .multiplyComm left right => .multiplyComm left right
  | .multiplyAssoc first second third => .multiplyAssoc first second third

/-- A unary tree with exactly one atomic leaf. `under` may nest expression
frames, but neither it nor reversal permits a second leaf or transitivity. -/
inductive DoCalculusRewriteStep (G : ObservedGraph S) [RuleSeparation G] :
    ProbabilityTerm S → ProbabilityTerm S → Type where
  | atom {left right} (leaf : DoCalculusAtom G left right) : DoCalculusRewriteStep G left right
  | symm {left right} (inner : DoCalculusRewriteStep G left right) : DoCalculusRewriteStep G right left
  | under (frame : ProbabilityTermFrame S) {left right} (inner : DoCalculusRewriteStep G left right) :
      DoCalculusRewriteStep G (frame.fill left) (frame.fill right)

def DoCalculusRewriteStep.toDerivation {left right : ProbabilityTerm S} :
    DoCalculusRewriteStep G left right → DoCalculusDerivation G left right
  | .atom leaf => leaf.toDerivation
  | .symm inner => .symm inner.toDerivation
  | .under frame inner => frame.lift inner.toDerivation

/-- A genuinely finite chain, indexed by the unchanged probability terms.
The empty chain still has its source as a vertex; it does not erase support. -/
inductive DoCalculusRewritePath (G : ObservedGraph S) [RuleSeparation G] :
    ProbabilityTerm S → ProbabilityTerm S → Type where
  | nil (term) : DoCalculusRewritePath G term term
  | cons {first middle last} (step : DoCalculusRewriteStep G first middle)
      (tail : DoCalculusRewritePath G middle last) : DoCalculusRewritePath G first last

namespace DoCalculusRewritePath

def length {left right : ProbabilityTerm S} : DoCalculusRewritePath G left right → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

def single {left right : ProbabilityTerm S} (step : DoCalculusRewriteStep G left right) :
    DoCalculusRewritePath G left right := .cons step (.nil right)

def append {first middle last : ProbabilityTerm S} (headPath : DoCalculusRewritePath G first middle)
    (tailPath : DoCalculusRewritePath G middle last) : DoCalculusRewritePath G first last :=
  match headPath with
  | .nil _ => tailPath
  | .cons step tail => .cons step (tail.append tailPath)

def reverse {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right) :
    DoCalculusRewritePath G right left :=
  match path with
  | .nil term => .nil term
  | .cons step tail => tail.reverse.append (single (.symm step))

def mapFrame (frame : ProbabilityTermFrame S) {left right : ProbabilityTerm S}
    (path : DoCalculusRewritePath G left right) :
    DoCalculusRewritePath G (frame.fill left) (frame.fill right) :=
  match path with
  | .nil term => .nil (frame.fill term)
  | .cons step tail => .cons (.under frame step) (tail.mapFrame frame)

/-- Interpreting a path back into the old language reconstructs only its
original leaves, congruences and transitivity. Soundness is not an input. -/
def toDerivation {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right) :
    DoCalculusDerivation G left right :=
  match path with
  | .nil term => .refl term
  | .cons step tail => .trans step.toDerivation tail.toDerivation

/-- Explicit data for every vertex, including both endpoints. Recursive
products let native proofs retain actual rational witnesses without choosing
data from a propositional list-membership or existence proof. -/
def AllVertices (property : ProbabilityTerm S → Type) {left right : ProbabilityTerm S} :
    DoCalculusRewritePath G left right → Type
  | .nil term => property term
  | @cons _ _ _ first _ _ _ tail => property first × tail.AllVertices property

namespace AllVertices

def first {property : ProbabilityTerm S → Type} {left right : ProbabilityTerm S}
    (path : DoCalculusRewritePath G left right) : path.AllVertices property → property left :=
  match path with
  | .nil _ => id
  | .cons _ _ => Prod.fst

def last {property : ProbabilityTerm S → Type} {left right : ProbabilityTerm S}
    (path : DoCalculusRewritePath G left right) : path.AllVertices property → property right :=
  match path with
  | .nil _ => id
  | .cons _ tail => fun values => last tail values.2

def map {property result : ProbabilityTerm S → Type} {left right : ProbabilityTerm S}
    (path : DoCalculusRewritePath G left right) (transform : ∀ term, property term → result term) :
    path.AllVertices property → path.AllVertices result :=
  match path with
  | .nil term => transform term
  | @cons _ _ _ first _ _ _ tail => fun values => ⟨transform first values.1, map tail transform values.2⟩

/-- Only vertex-witness reconstruction needs the indexed recursor that the
compiler cannot currently generate. The path operations themselves remain
computable; this annotation introduces no choice or extra axiom. -/
noncomputable def append {property : ProbabilityTerm S → Type} {first middle last : ProbabilityTerm S}
    (headPath : DoCalculusRewritePath G first middle) (tailPath : DoCalculusRewritePath G middle last) :
    headPath.AllVertices property → tailPath.AllVertices property → (headPath.append tailPath).AllVertices property := by
  induction headPath with
  | nil => exact fun _ suffixValues => suffixValues
  | cons step tail ih => exact fun headValues tailValues => ⟨headValues.1, ih tailPath headValues.2 tailValues⟩

noncomputable def reverse {property : ProbabilityTerm S → Type} {left right : ProbabilityTerm S}
    (path : DoCalculusRewritePath G left right) : path.AllVertices property → path.reverse.AllVertices property :=
  match path with
  | .nil _ => id
  | .cons step tail => fun values =>
      append tail.reverse (single (.symm step)) (reverse tail values.2) ⟨first tail values.2, values.1⟩

def mapFrame {property : ProbabilityTerm S → Type} (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (path : DoCalculusRewritePath G left right) :
    path.AllVertices (fun term => property (frame.fill term)) → (path.mapFrame frame).AllVertices property :=
  match path with
  | .nil _ => id
  | .cons _ tail => fun values => ⟨values.1, mapFrame frame tail values.2⟩

/-- Commute universal data with the finite product of vertices. This is
ordinary function application and pairing, not an invocation of choice. -/
def pi {A : Type} {property : A → ProbabilityTerm S → Type} {left right : ProbabilityTerm S}
    (path : DoCalculusRewritePath G left right) :
    (∀ index, path.AllVertices (property index)) → path.AllVertices (fun term => ∀ index, property index term) :=
  match path with
  | .nil _ => id
  | .cons _ tail => fun values => ⟨fun index => (values index).1, pi tail (fun index => (values index).2)⟩

end AllVertices
end DoCalculusRewritePath

/-- Produce one fixed path from syntax alone, before seeing any native
model, reference or support profile. Every old constructor is covered. -/
def DoCalculusDerivation.linearize {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right) : DoCalculusRewritePath G left right :=
  match derivation with
  | .refl term => .nil term
  | .symm inner => inner.linearize.reverse
  | .trans first second => first.linearize.append second.linearize
  | .doRule application => .single (.atom (.doRule application))
  | .marginalization x y z w disjoint => .single (.atom (.marginalization x y z w disjoint))
  | .conditioning x y z w disjoint => .single (.atom (.conditioning x y z w disjoint))
  | .chain x y z w disjoint => .single (.atom (.chain x y z w disjoint))
  | .weightedChain x y z w disjoint => .single (.atom (.weightedChain x y z w disjoint))
  | .multiplyComm left right => .single (.atom (.multiplyComm left right))
  | .multiplyAssoc first second third => .single (.atom (.multiplyAssoc first second third))
  | .marginalizeCongr nodes inner => inner.linearize.mapFrame (.marginalize nodes)
  | .evaluateAtCongr reference inner => inner.linearize.mapFrame (.evaluateAt reference)
  | @DoCalculusDerivation.addCongr _ _ _ left left' right right' first second =>
      (first.linearize.mapFrame (.addLeft right)).append (second.linearize.mapFrame (.addRight left'))
  | @DoCalculusDerivation.multiplyCongr _ _ _ left left' right right' first second =>
      (first.linearize.mapFrame (.multiplyLeft right)).append (second.linearize.mapFrame (.multiplyRight left'))
  | @DoCalculusDerivation.weightedMultiplyCongr _ _ _ weight weight' factor factor' first second =>
      (first.linearize.mapFrame (.weightedLeft factor)).append (second.linearize.mapFrame (.weightedRight weight'))
  | @DoCalculusDerivation.divideCongr _ _ _ left left' right right' first second =>
      (first.linearize.mapFrame (.divideLeft right)).append (second.linearize.mapFrame (.divideRight left'))
  | .eqCongr sameLeft sameRight inner => sameLeft.symm ▸ sameRight.symm ▸ inner.linearize

end Thesis.Causality
