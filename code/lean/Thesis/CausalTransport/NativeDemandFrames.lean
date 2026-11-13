import Thesis.CausalTransport.NativeDemandEncoding
import Thesis.Causality.DerivationLinearization

namespace Thesis.Causality.NativeDemandEncoding

open Probability NativeDemandTyping

/-!
# One-hole expression frames preserve faithful demand encoding

All ten existing frame forms are covered, with arbitrary literal siblings.
Frame data contain encoded sibling trees; they do not turn those unbounded
trees into new alphabet symbols. Filling therefore uses exactly the finite
term alphabet already established, and erasure retains each original sibling.

The outer application supplies its demand explicitly. Marginalization and
fixed evaluation pull that demand to their actual references; a weighted
factor receives only the fixed weight's positive cells. When the weight is
the hole, native soundness on the matching graph proves that a supported
inner derivation leaves the fixed factor's mask unchanged. Hence one encoded
frame works at both endpoints, uniformly over all supplied profiles.

Inner support alone does not supply missing sibling support or a positive
denominator. The final equivalence keeps support of both complete endpoints
explicit and compares it with the original lifted proof checker. No equation
is inferred from matching types. This is a single-frame bridge, with no bound
on sibling syntax; nested rewrite-path correspondence, AC normalization and
completion remain separate stages.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- Demand on the distinguished hole, pulled back from the outer request.
This is separate from the fixed sibling's demand and the filled root's demand. -/
def frameDemand (profiles : List (NativeTemplateInstance P)) : ProbabilityTermFrame S → Demand profiles → Demand profiles
  | .marginalize nodes, requested => marginalDemand profiles requested nodes
  | .evaluateAt reference, requested => fixedDemand profiles requested reference
  | .weightedRight weight, requested => positiveDemand profiles requested (termStatus profiles weight)
  | _, requested => requested

/-- One expression layer with exactly one omitted child. Unbounded siblings
are ordinary encoded trees, not parameters of a new alphabet symbol. -/
inductive Frame (profiles : List (NativeTemplateInstance P)) where
  | marginalize (demand : Demand profiles) (nodes : NodeSet S)
  | evaluateAt (demand : Demand profiles) (reference : S.Assignment)
  | addLeft (demand : Demand profiles) (right : Term profiles)
  | addRight (demand : Demand profiles) (left : Term profiles)
  | multiplyLeft (demand : Demand profiles) (right : Term profiles)
  | multiplyRight (demand : Demand profiles) (left : Term profiles)
  | weightedLeft (demand : Demand profiles) (factor : Term profiles)
  | weightedRight (demand : Demand profiles) (weight : Term profiles)
  | divideLeft (demand : Demand profiles) (denominator : Term profiles)
  | divideRight (demand : Demand profiles) (numerator : Term profiles)

namespace Frame

variable {profiles : List (NativeTemplateInstance P)}

def demand : Frame profiles → Demand profiles
  | .marginalize requested _ | .evaluateAt requested _ | .addLeft requested _ | .addRight requested _
  | .multiplyLeft requested _ | .multiplyRight requested _ | .weightedLeft requested _ | .weightedRight requested _
  | .divideLeft requested _ | .divideRight requested _ => requested

def fill : Frame profiles → Term profiles → Term profiles
  | .marginalize requested nodes, term => .marginalize requested nodes term
  | .evaluateAt requested reference, term => .evaluateAt requested reference term
  | .addLeft requested fixed, term => .add requested term fixed
  | .addRight requested fixed, term => .add requested fixed term
  | .multiplyLeft requested fixed, term => .multiply requested term fixed
  | .multiplyRight requested fixed, term => .multiply requested fixed term
  | .weightedLeft requested fixed, term => .weightedMultiply requested term fixed
  | .weightedRight requested fixed, term => .weightedMultiply requested fixed term
  | .divideLeft requested fixed, term => .divide requested term fixed
  | .divideRight requested fixed, term => .divide requested fixed term

def erase : Frame profiles → ProbabilityTermFrame S
  | .marginalize _ nodes => .marginalize nodes
  | .evaluateAt _ reference => .evaluateAt reference
  | .addLeft _ fixed => .addLeft fixed.erase
  | .addRight _ fixed => .addRight fixed.erase
  | .multiplyLeft _ fixed => .multiplyLeft fixed.erase
  | .multiplyRight _ fixed => .multiplyRight fixed.erase
  | .weightedLeft _ fixed => .weightedLeft fixed.erase
  | .weightedRight _ fixed => .weightedRight fixed.erase
  | .divideLeft _ fixed => .divideLeft fixed.erase
  | .divideRight _ fixed => .divideRight fixed.erase

theorem demand_fill (frame : Frame profiles) (term : Term profiles) : (frame.fill term).demand = frame.demand := by
  cases frame <;> rfl

/-- Erasure commutes even for malformed annotations; no hidden deletion or
change of the literal sibling is built into filling a context. -/
theorem erase_fill (frame : Frame profiles) (term : Term profiles) :
    (frame.fill term).erase = frame.erase.fill term.erase := by cases frame <;> rfl

def encode (profiles : List (NativeTemplateInstance P)) : ProbabilityTermFrame S → ProbabilityTerm S → Demand profiles → Frame profiles
  | .marginalize nodes, _, requested => .marginalize requested nodes
  | .evaluateAt reference, _, requested => .evaluateAt requested reference
  | .addLeft fixed, _, requested => .addLeft requested (Term.encode profiles fixed requested)
  | .addRight fixed, _, requested => .addRight requested (Term.encode profiles fixed requested)
  | .multiplyLeft fixed, _, requested => .multiplyLeft requested (Term.encode profiles fixed requested)
  | .multiplyRight fixed, _, requested => .multiplyRight requested (Term.encode profiles fixed requested)
  | .weightedLeft fixed, hole, requested => .weightedLeft requested
      (Term.encode profiles fixed (positiveDemand profiles requested (termStatus profiles hole)))
  | .weightedRight fixed, _, requested => .weightedRight requested (Term.encode profiles fixed requested)
  | .divideLeft fixed, _, requested => .divideLeft requested (Term.encode profiles fixed requested)
  | .divideRight fixed, _, requested => .divideRight requested (Term.encode profiles fixed requested)

theorem erase_encode (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    (hole : ProbabilityTerm S) (requested : Demand profiles) : (encode profiles frame hole requested).erase = frame := by
  cases frame <;> simp only [encode, erase, Term.erase_encode]

theorem demand_encode (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    (hole : ProbabilityTerm S) (requested : Demand profiles) : (encode profiles frame hole requested).demand = requested := by
  cases frame <;> rfl

/-- Every single endpoint has its canonical encoding, using the frame's
actual pulled-back hole demand, including declared null substitutions. -/
theorem encode_fill (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    (hole : ProbabilityTerm S) (requested : Demand profiles) :
    (encode profiles frame hole requested).fill (Term.encode profiles hole (frameDemand profiles frame requested)) =
      Term.encode profiles (frame.fill hole) requested := by cases frame <;> rfl

/-- The only hole-dependent sibling annotation is a weighted factor's mask.
Its equality comes from a supported derivation on the actual projected graph. -/
theorem encode_eq_of_checked (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true) :
    encode profiles frame left requested = encode profiles frame right requested := by
  cases frame <;> try rfl
  case weightedLeft fixed =>
    exact congrArg (fun factorDemand => Frame.weightedLeft requested (Term.encode profiles fixed factorDemand))
      (positiveDemand_eq_of_checked profiles requested derivation accepted)

theorem encode_fill_right (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true) :
    (encode profiles frame left requested).fill (Term.encode profiles right (frameDemand profiles frame requested)) =
      Term.encode profiles (frame.fill right) requested := by
  rw [encode_eq_of_checked profiles frame derivation requested accepted]
  exact encode_fill profiles frame right requested

theorem check_fill (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    (hole : ProbabilityTerm S) (requested : Demand profiles) :
    ((encode profiles frame hole requested).fill (Term.encode profiles hole (frameDemand profiles frame requested))).check =
      NativeDemandTyping.check profiles (frame.fill hole) requested := by
  rw [encode_fill, Term.check_encode]

theorem check_fill_right (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true) :
    ((encode profiles frame left requested).fill (Term.encode profiles right (frameDemand profiles frame requested))).check =
      NativeDemandTyping.check profiles (frame.fill right) requested := by
  rw [encode_fill_right profiles frame derivation requested accepted, Term.check_encode]

private theorem refl_checked (profiles : List (NativeTemplateInstance P)) (requested : Demand profiles) (term : ProbabilityTerm S)
    (accepted : NativeDemandTyping.check profiles term requested = true) :
    checkDerivation profiles requested (DoCalculusDerivation.refl (G := P.observedGraph) term) = true := by
  change ((NativeDemandTyping.check profiles term requested && NativeDemandTyping.check profiles term requested) && true) = true
  rw [accepted]
  rfl

/-- Read the required inner check back from an accepted lift. This retains
the empty factor demand under a zero weight, rather than demanding the
inner proof at all of the outer references. -/
theorem inner_checked_of_lift (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles requested (frame.lift derivation) = true) :
    checkDerivation profiles (frameDemand profiles frame requested) derivation = true := by
  cases frame
  all_goals have body := (Bool.and_eq_true_iff.mp accepted).2
  case marginalize => exact body
  case evaluateAt => exact body
  case addLeft => exact (Bool.and_eq_true_iff.mp body).1
  case addRight => exact (Bool.and_eq_true_iff.mp body).2
  case multiplyLeft => exact (Bool.and_eq_true_iff.mp body).1
  case multiplyRight => exact (Bool.and_eq_true_iff.mp body).2
  case weightedLeft => exact (Bool.and_eq_true_iff.mp body).1
  case weightedRight => exact (Bool.and_eq_true_iff.mp body).2
  case divideLeft => exact (Bool.and_eq_true_iff.mp body).1
  case divideRight => exact (Bool.and_eq_true_iff.mp body).2

/-- Supply the actual complete endpoint checks as well as the inner proof.
Sibling support and positive denominators are retained by these endpoint
premises, rather than inferred merely from support of the hole. -/
theorem lift_checked (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) (accepted : checkDerivation profiles (frameDemand profiles frame requested) derivation = true)
    (leftChecked : NativeDemandTyping.check profiles (frame.fill left) requested = true)
    (rightChecked : NativeDemandTyping.check profiles (frame.fill right) requested = true) :
    checkDerivation profiles requested (frame.lift derivation) = true := by
  cases frame
  all_goals
    change ((_ && _) && _) = true
    rw [leftChecked, rightChecked]
    simp only [Bool.true_and]
  case marginalize => exact accepted
  case evaluateAt => exact accepted
  case addLeft fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨accepted, refl_checked profiles requested fixed (Bool.and_eq_true_iff.mp leftChecked).2⟩
  case addRight fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨refl_checked profiles requested fixed (Bool.and_eq_true_iff.mp leftChecked).1, accepted⟩
  case multiplyLeft fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨accepted, refl_checked profiles requested fixed (Bool.and_eq_true_iff.mp leftChecked).2⟩
  case multiplyRight fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨refl_checked profiles requested fixed (Bool.and_eq_true_iff.mp leftChecked).1, accepted⟩
  case weightedLeft fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨accepted,
      refl_checked profiles (positiveDemand profiles requested (termStatus profiles left)) fixed (Bool.and_eq_true_iff.mp leftChecked).2⟩
  case weightedRight fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨refl_checked profiles requested fixed (Bool.and_eq_true_iff.mp leftChecked).1, accepted⟩
  case divideLeft fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨accepted, refl_checked profiles requested fixed (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp leftChecked).1).2⟩
  case divideRight fixed =>
    exact Bool.and_eq_true_iff.mpr ⟨refl_checked profiles requested fixed (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp leftChecked).1).1, accepted⟩

/-- Exact support correspondence for the single common encoded frame and
the original lifted proof. The same derivation is used for every profile. -/
theorem lift_check_iff (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation P.observedGraph left right)
    (requested : Demand profiles) :
    checkDerivation profiles requested (frame.lift derivation) = true ↔
      checkDerivation profiles (frameDemand profiles frame requested) derivation = true ∧
      ((encode profiles frame left requested).fill (Term.encode profiles left (frameDemand profiles frame requested))).check = true ∧
      ((encode profiles frame left requested).fill (Term.encode profiles right (frameDemand profiles frame requested))).check = true := by
  constructor
  · intro checked
    have inner := inner_checked_of_lift profiles frame derivation requested checked
    refine ⟨inner, ?_⟩
    rw [check_fill, check_fill_right profiles frame derivation requested inner]
    cases frame <;> exact Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1
  · rintro ⟨inner, leftChecked, rightChecked⟩
    rw [check_fill] at leftChecked
    rw [check_fill_right profiles frame derivation requested inner] at rightChecked
    exact lift_checked profiles frame derivation requested inner leftChecked rightChecked

end Frame
end Thesis.Causality.NativeDemandEncoding
