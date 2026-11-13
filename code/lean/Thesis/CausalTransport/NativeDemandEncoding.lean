import Thesis.CausalTransport.NativeTermAlphabet

namespace Thesis.Causality.NativeDemandEncoding

open Probability NativeDemandTyping

/-!
# Faithful term encoding with checked demand annotations

Every raw constructor and every subtree is retained, including unsupported
or actionful syntax beneath a defined zero weight. Only the support demand
is suppressed there. Erasure therefore recovers literal syntax, while the
action-free check still visits both children regardless of their demand.

Annotations pull demands through all marginal substitutions and fixed
references. A weighted factor receives precisely its weight's positive
cells; the weight itself keeps the original demand. Annotation validation
is separate from the existing exact support checker, which is reused rather
than replaced by an assumed type interpretation. Acceptance agrees exactly
on canonical encodings, including zeros and empty demands. Malformed demand
annotations cannot gain support by hiding a required cell.

The constructors give ranked trees over the preceding finite alphabet.
There is no finite catalogue of all trees or contexts, no rewrite relation,
and no new causal equality. Context/path correspondence and completion are
separate proof stages.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- Finite table equality, using only the supplied finite reference domain. -/
def demandEqual (profiles : List (NativeTemplateInstance P)) (left right : Demand profiles) : Bool :=
  allNeeded profiles (fun _ _ => true) (fun index reference => decide (left index reference = right index reference))

theorem demandEqual_exact (profiles : List (NativeTemplateInstance P)) (left right : Demand profiles) :
    demandEqual profiles left right = true ↔ left = right := by
  constructor
  · intro accepted
    funext index reference
    exact of_decide_eq_true ((allNeeded_exact ..).mp accepted index reference rfl)
  · intro same
    subst right
    exact (allNeeded_exact ..).mpr (fun _ _ _ => decide_eq_true rfl)

inductive Term (profiles : List (NativeTemplateInstance P)) where
  | zero (demand : Demand profiles)
  | kernel (demand : Demand profiles) (kernel : Kernel S)
  | marginalize (demand : Demand profiles) (nodes : NodeSet S) (inner : Term profiles)
  | evaluateAt (demand : Demand profiles) (reference : S.Assignment) (inner : Term profiles)
  | add (demand : Demand profiles) (left right : Term profiles)
  | multiply (demand : Demand profiles) (left right : Term profiles)
  | weightedMultiply (demand : Demand profiles) (weight factor : Term profiles)
  | divide (demand : Demand profiles) (numerator denominator : Term profiles)

namespace Term

variable {profiles : List (NativeTemplateInstance P)}

def label : Term profiles → Symbol profiles
  | .zero requested => .zero requested
  | .kernel requested current => .kernel requested current
  | .marginalize requested nodes _ => .marginalize requested nodes
  | .evaluateAt requested reference _ => .evaluateAt requested reference
  | .add requested _ _ => .add requested
  | .multiply requested _ _ => .multiply requested
  | .weightedMultiply requested _ _ => .weightedMultiply requested
  | .divide requested _ _ => .divide requested

def demand (term : Term profiles) : Demand profiles := term.label.demand

def children : Term profiles → List (Term profiles)
  | .zero _ | .kernel _ _ => []
  | .marginalize _ _ inner | .evaluateAt _ _ inner => [inner]
  | .add _ left right | .multiply _ left right | .weightedMultiply _ left right | .divide _ left right => [left, right]

theorem children_length (term : Term profiles) : term.children.length = term.label.arity := by cases term <;> rfl

def erase : Term profiles → ProbabilityTerm S
  | .zero _ => .zero
  | .kernel _ current => .kernel current
  | .marginalize _ nodes inner => .marginalize nodes inner.erase
  | .evaluateAt _ reference inner => .evaluateAt reference inner.erase
  | .add _ left right => .add left.erase right.erase
  | .multiply _ left right => .multiply left.erase right.erase
  | .weightedMultiply _ weight factor => .weightedMultiply weight.erase factor.erase
  | .divide _ numerator denominator => .divide numerator.erase denominator.erase

def encode (profiles : List (NativeTemplateInstance P)) : ProbabilityTerm S → Demand profiles → Term profiles
  | .zero, requested => .zero requested
  | .kernel current, requested => .kernel requested current
  | .marginalize nodes inner, requested =>
      .marginalize requested nodes (encode profiles inner (marginalDemand profiles requested nodes))
  | .evaluateAt reference inner, requested =>
      .evaluateAt requested reference (encode profiles inner (fixedDemand profiles requested reference))
  | .add left right, requested => .add requested (encode profiles left requested) (encode profiles right requested)
  | .multiply left right, requested => .multiply requested (encode profiles left requested) (encode profiles right requested)
  | .weightedMultiply weight factor, requested => .weightedMultiply requested (encode profiles weight requested)
      (encode profiles factor (positiveDemand profiles requested (termStatus profiles weight)))
  | .divide numerator denominator, requested =>
      .divide requested (encode profiles numerator requested) (encode profiles denominator requested)

theorem erase_encode (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (requested : Demand profiles) :
    (encode profiles term requested).erase = term := by
  induction term generalizing requested <;> simp only [encode, erase, *]

theorem demand_encode (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (requested : Demand profiles) :
    (encode profiles term requested).demand = requested := by cases term <;> rfl

/-- Validate every annotation, even inside an unused subtree. Support there
may be absent, but its raw syntax and coherent empty demand remain present. -/
def checkAnnotations : Term profiles → Demand profiles → Bool
  | .zero actual, requested | .kernel actual _, requested => demandEqual profiles requested actual
  | .marginalize actual nodes inner, requested => demandEqual profiles requested actual &&
      checkAnnotations inner (marginalDemand profiles requested nodes)
  | .evaluateAt actual reference inner, requested => demandEqual profiles requested actual &&
      checkAnnotations inner (fixedDemand profiles requested reference)
  | .add actual left right, requested | .multiply actual left right, requested | .divide actual left right, requested =>
      demandEqual profiles requested actual && (checkAnnotations left requested && checkAnnotations right requested)
  | .weightedMultiply actual weight factor, requested => demandEqual profiles requested actual &&
      (checkAnnotations weight requested &&
        checkAnnotations factor (positiveDemand profiles requested (termStatus profiles weight.erase)))

/-- A passing annotation tree is exactly the canonical encoding of its
erasure. In particular, an empty mask cannot be substituted at a needed child. -/
theorem checkAnnotations_exact (term : Term profiles) (requested : Demand profiles) :
    term.checkAnnotations requested = true ↔ encode profiles term.erase requested = term := by
  induction term generalizing requested <;>
    simp only [checkAnnotations, demandEqual_exact, Bool.and_eq_true_iff, erase, encode,
      Term.zero.injEq, Term.kernel.injEq, Term.marginalize.injEq, Term.evaluateAt.injEq,
      Term.add.injEq, Term.multiply.injEq, Term.weightedMultiply.injEq, Term.divide.injEq, true_and, and_true, *]

theorem checkAnnotations_encode (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (requested : Demand profiles) :
    (encode profiles term requested).checkAnnotations requested = true :=
  (checkAnnotations_exact ..).mpr (by rw [erase_encode])

def wellFormed (term : Term profiles) : Bool := term.checkAnnotations term.demand

theorem wellFormed_iff (term : Term profiles) : term.wellFormed = true ↔ encode profiles term.erase term.demand = term :=
  checkAnnotations_exact term term.demand

def check (term : Term profiles) : Bool :=
  term.wellFormed && NativeDemandTyping.check profiles term.erase term.demand

/-- Exact support agreement for every raw term and demand, without a
positivity assumption or an exception for declared null references. -/
theorem check_encode (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (requested : Demand profiles) :
    (encode profiles term requested).check = NativeDemandTyping.check profiles term requested := by
  simp only [check, wellFormed, demand_encode, checkAnnotations_encode, erase_encode, Bool.true_and]

theorem supported_of_check (term : Term profiles) (accepted : term.check = true)
    (index : Fin profiles.length) (reference : S.Assignment) (needed : term.demand index reference = true) :
    ((profiles.get index).model.termDenote term.erase reference).isSome = true := by
  have supported := (Bool.and_eq_true_iff.mp accepted).2
  rw [NativeDemandTyping.check_exact] at supported
  exact (allNeeded_exact ..).mp supported index reference needed

def infer (term : Term profiles) : Option (TermType profiles) :=
  if term.check then some (typeOf profiles term.erase term.demand) else none

theorem infer_encode (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (requested : Demand profiles) :
    (encode profiles term requested).infer = NativeDemandTyping.infer profiles term requested := by
  simp only [infer, check_encode, erase_encode, demand_encode, NativeDemandTyping.infer]

/-- This is a syntactic check: unused children are still visited. -/
def actionFreeCheck : Term profiles → Bool
  | .zero _ => true
  | .kernel _ current => NodeSet.isEmpty current.action
  | .marginalize _ _ inner | .evaluateAt _ _ inner => inner.actionFreeCheck
  | .add _ left right | .multiply _ left right | .weightedMultiply _ left right | .divide _ left right =>
      left.actionFreeCheck && right.actionFreeCheck

theorem actionFreeCheck_eq_erased (term : Term profiles) : term.actionFreeCheck = term.erase.actionFreeCheck := by
  induction term <;> simp only [actionFreeCheck, erase, ProbabilityTerm.actionFreeCheck, *]

theorem actionFreeCheck_encode (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (requested : Demand profiles) :
    (encode profiles term requested).actionFreeCheck = term.actionFreeCheck := by
  rw [actionFreeCheck_eq_erased, erase_encode]

end Term
end Thesis.Causality.NativeDemandEncoding
