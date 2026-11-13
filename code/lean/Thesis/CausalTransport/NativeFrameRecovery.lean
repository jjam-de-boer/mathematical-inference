import Thesis.CausalTransport.NativeFramePreservation

namespace Thesis.Causality.NativeDemandEncoding.Frame

open Probability NativeDemandTyping

/-!
# Recover a canonical frame from one valid filled source

A frame and its literal siblings may initially carry arbitrary annotations.
Checking the complete filled source fixes them: the outer request is retained,
the hole has exactly its routed demand, and the unchanged siblings are their
canonical encodings. This includes unused subtrees; a zero weight suppresses
their support obligation, never their annotation check or literal syntax.

The second recovery fact reads the hole's actual support from the filled
source. Combining these facts with the preceding frame-preservation theorem
lets a checked inner replacement keep this very frame, without assuming that
the input frame was constructed canonically or checking its target first.
No equation is inferred from annotations, and no rewrite search is introduced.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
variable {profiles : List (NativeTemplateInstance P)}

/-- Coherence of the whole source recovers both the literal frame and the
hole. An unrelated mask, including an empty mask at a demanded hole, fails. -/
theorem recover_of_fill_annotations (frame : Frame profiles) (hole : Term profiles) (requested : Demand profiles)
    (annotated : (frame.fill hole).checkAnnotations requested = true) :
    encode profiles frame.erase hole.erase requested = frame ∧
      Term.encode profiles hole.erase (frameDemand profiles frame.erase requested) = hole := by
  have canonical := (Term.checkAnnotations_exact (frame.fill hole) requested).mp annotated
  rw [erase_fill] at canonical
  cases frame <;>
    simp only [fill, erase, ProbabilityTermFrame.fill, Term.encode,
      Term.marginalize.injEq, Term.evaluateAt.injEq, Term.add.injEq, Term.multiply.injEq,
      Term.weightedMultiply.injEq, Term.divide.injEq, true_and] at canonical
  all_goals
    rcases canonical with ⟨root, parts⟩
    cases root
  case marginalize | evaluateAt => exact ⟨rfl, parts⟩
  case addLeft | multiplyLeft | weightedLeft | divideLeft =>
    rcases parts with ⟨holeSame, fixedSame⟩
    constructor
    · simp only [erase, encode, fixedSame]
    · exact holeSame
  case addRight | multiplyRight | weightedRight | divideRight =>
    rcases parts with ⟨fixedSame, holeSame⟩
    constructor
    · simp only [erase, encode, fixedSame]
    · exact holeSame

/-- The source supplies the hole's support at the pulled-back references.
An unused weighted factor receives its genuinely empty demand. -/
theorem inner_supported_of_fill (profiles : List (NativeTemplateInstance P)) (frame : ProbabilityTermFrame S)
    (hole : ProbabilityTerm S) (requested : Demand profiles)
    (source : NativeDemandTyping.check profiles (frame.fill hole) requested = true) :
    NativeDemandTyping.check profiles hole (frameDemand profiles frame requested) = true := by
  cases frame
  case marginalize => exact source
  case evaluateAt => exact source
  case addLeft | multiplyLeft | weightedLeft => exact (Bool.and_eq_true_iff.mp source).1
  case addRight | multiplyRight | weightedRight => exact (Bool.and_eq_true_iff.mp source).2
  case divideLeft => exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp source).1).1
  case divideRight => exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp source).1).2

/-- Recover the whole hole check, keeping annotation coherence separate
from numerical support even when the routed demand is empty. -/
theorem inner_checks_of_fill (frame : Frame profiles) (hole : Term profiles) (requested : Demand profiles)
    (source : (frame.fill hole).checkAnnotations requested = true ∧
      NativeDemandTyping.check profiles (frame.fill hole).erase requested = true) :
    hole.checkAnnotations (frameDemand profiles frame.erase requested) = true ∧
      NativeDemandTyping.check profiles hole.erase (frameDemand profiles frame.erase requested) = true := by
  refine ⟨(Term.checkAnnotations_exact ..).mpr (recover_of_fill_annotations frame hole requested source.1).2, ?_⟩
  exact inner_supported_of_fill profiles frame.erase hole.erase requested (by simpa only [erase_fill] using source.2)

/-- Keep an arbitrary input frame literally unchanged. Source coherence
recovers its canonical form; actual inner soundness then preserves any
hole-dependent sibling mask. The target hole must retain its routed encoding. -/
theorem fill_checks_of_checked (frame : Frame profiles) {left right : Term profiles}
    (derivation : DoCalculusDerivation P.observedGraph left.erase right.erase) (requested : Demand profiles)
    (accepted : checkDerivation profiles (frameDemand profiles frame.erase requested) derivation = true)
    (source : (frame.fill left).checkAnnotations requested = true ∧
      NativeDemandTyping.check profiles (frame.fill left).erase requested = true)
    (targetCanonical : Term.encode profiles right.erase (frameDemand profiles frame.erase requested) = right) :
    (frame.fill right).checkAnnotations requested = true ∧
      NativeDemandTyping.check profiles (frame.fill right).erase requested = true := by
  have recovered := recover_of_fill_annotations frame left requested source.1
  have encoded := encode_fill_right profiles frame.erase derivation requested accepted
  rw [recovered.1, targetCanonical] at encoded
  refine ⟨(Term.checkAnnotations_exact ..).mpr ?_, ?_⟩
  · rw [erase_fill]
    exact encoded.symm
  · rw [erase_fill]
    exact right_checked_of_left profiles frame.erase derivation requested accepted (by simpa only [erase_fill] using source.2)

end Thesis.Causality.NativeDemandEncoding.Frame
