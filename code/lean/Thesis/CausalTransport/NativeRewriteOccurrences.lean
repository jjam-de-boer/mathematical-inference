import Thesis.CausalTransport.NativePrimitiveRules
import Thesis.CausalTransport.NativeStepPreservation

namespace Thesis.Causality.NativeDemandEncoding

open Probability NativeDemandTyping

/-!
# Flat rule occurrences correspond to existing encoded elementary steps

A root replacement is one accepted finite primitive-rule code or one of the
two existing strict multiplication AC instances. A direction bit and an
outermost-first list of literal frames locate that replacement in a term.
Frames retain their sibling trees and demand labels as occurrence data;
they do not enlarge the finite term alphabet with whole-expression symbols.
AC operands remain arbitrary trees, and weighted multiplication has no AC
instance. No arbitrary `Step` or old derivation is an occurrence input field.

Reconstruction produces an actual encoded step on the same profile family.
Conversely, flattening an encoded step retains its literal endpoint trees,
all sibling syntax and every demand label. Reversal is moved to one bit, so
this correspondence does not claim identity of the original proof trees.
The unchanged source gate includes both complete annotations and native
support at the explicit outer demand. The preceding preservation theorem
then supplies target validity and the original recursive support check.

The primitive equation catalogue is finite; contexts, AC operands and
occurrences are unbounded finite syntax. These definitions introduce no
finite trace language, AC quotient or normalization, path search, universal
formula-coverage theorem or stopping argument. No catalogue is evaluated.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace Frame

variable {profiles : List (NativeTemplateInstance P)}

/-- The head is the outermost frame. Every sibling is kept literally. -/
def fillList : List (Frame profiles) → Term profiles → Term profiles
  | [], term => term
  | frame :: rest, term => frame.fill (fillList rest term)

def liftList : List (Frame profiles) → Step profiles → Step profiles
  | [], step => step
  | frame :: rest, step => .under frame (liftList rest step)

theorem liftList_endpoints (frames : List (Frame profiles)) (step : Step profiles) :
    (liftList frames step).left = fillList frames step.left ∧
      (liftList frames step).right = fillList frames step.right := by
  induction frames with
  | nil => exact ⟨rfl, rfl⟩
  | cons frame rest ih => exact ⟨congrArg frame.fill ih.1, congrArg frame.fill ih.2⟩

end Frame

/-- Only a primitive code is drawn from the finite equation catalogue.
The two AC constructors are schemas with literal operand trees. -/
inductive RewriteRedex (profiles : List (NativeTemplateInstance P)) where
  | primitive (rule : CheckedPrimitiveRule profiles)
  | multiplyComm (demand : Demand profiles) (left right : Term profiles)
  | multiplyAssoc (demand : Demand profiles) (first second third : Term profiles)

namespace RewriteRedex

variable {profiles : List (NativeTemplateInstance P)}

def left : RewriteRedex profiles → Term profiles
  | .primitive rule => rule.left
  | .multiplyComm demand first second => .multiply demand first second
  | .multiplyAssoc demand first second third => .multiply demand (.multiply demand first second) third

def right : RewriteRedex profiles → Term profiles
  | .primitive rule => rule.right
  | .multiplyComm demand first second => .multiply demand second first
  | .multiplyAssoc demand first second third => .multiply demand first (.multiply demand second third)

def toStep : RewriteRedex profiles → Step profiles
  | .primitive rule => .primitive rule.entry
  | .multiplyComm demand first second => .multiplyComm demand first second
  | .multiplyAssoc demand first second third => .multiplyAssoc demand first second third

theorem toStep_left (redex : RewriteRedex profiles) : redex.toStep.left = redex.left := by cases redex <;> rfl
theorem toStep_right (redex : RewriteRedex profiles) : redex.toStep.right = redex.right := by cases redex <;> rfl

end RewriteRedex

structure RewriteOccurrence (profiles : List (NativeTemplateInstance P)) where
  redex : RewriteRedex profiles
  reversed : Bool
  context : List (Frame profiles)

namespace RewriteOccurrence

variable {profiles : List (NativeTemplateInstance P)}

def left (occurrence : RewriteOccurrence profiles) : Term profiles :=
  Frame.fillList occurrence.context (if occurrence.reversed then occurrence.redex.right else occurrence.redex.left)

def right (occurrence : RewriteOccurrence profiles) : Term profiles :=
  Frame.fillList occurrence.context (if occurrence.reversed then occurrence.redex.left else occurrence.redex.right)

def reverse (occurrence : RewriteOccurrence profiles) : RewriteOccurrence profiles :=
  { occurrence with reversed := !occurrence.reversed }

def under (frame : Frame profiles) (occurrence : RewriteOccurrence profiles) : RewriteOccurrence profiles :=
  { occurrence with context := frame :: occurrence.context }

theorem reverse_left (occurrence : RewriteOccurrence profiles) : occurrence.reverse.left = occurrence.right := by
  cases occurrence with
  | mk redex reversed context => cases reversed <;> rfl

theorem reverse_right (occurrence : RewriteOccurrence profiles) : occurrence.reverse.right = occurrence.left := by
  cases occurrence with
  | mk redex reversed context => cases reversed <;> rfl

theorem under_left (frame : Frame profiles) (occurrence : RewriteOccurrence profiles) :
    (occurrence.under frame).left = frame.fill occurrence.left := rfl

theorem under_right (frame : Frame profiles) (occurrence : RewriteOccurrence profiles) :
    (occurrence.under frame).right = frame.fill occurrence.right := rfl

/-- Reconstruct from the explicit root data, bit and frame stack. A single
step is used for every supplied profile, with no modelwise proof selection. -/
def toStep (occurrence : RewriteOccurrence profiles) : Step profiles :=
  Frame.liftList occurrence.context
    (if occurrence.reversed then .symm occurrence.redex.toStep else occurrence.redex.toStep)

theorem toStep_endpoints (occurrence : RewriteOccurrence profiles) :
    occurrence.toStep.left = occurrence.left ∧ occurrence.toStep.right = occurrence.right := by
  have lifted := Frame.liftList_endpoints occurrence.context
    (if occurrence.reversed then .symm occurrence.redex.toStep else occurrence.redex.toStep)
  cases direction : occurrence.reversed <;>
    simpa only [toStep, left, right, direction, Bool.false_eq_true, if_false, if_true,
      Step.left, Step.right, RewriteRedex.toStep_left, RewriteRedex.toStep_right] using lifted

/-- Source validation remains explicit even for an empty context or mask.
Primitive decoding has already checked the local rule's own support. -/
def check (occurrence : RewriteOccurrence profiles) (requested : Demand profiles) : Bool :=
  occurrence.left.checkAnnotations requested && NativeDemandTyping.check profiles occurrence.left.erase requested

theorem toStep_check (occurrence : RewriteOccurrence profiles) (requested : Demand profiles) :
    occurrence.toStep.check requested = occurrence.check requested := by
  rw [Step.check_eq_left, (toStep_endpoints occurrence).1]
  rfl

theorem target_checks_of_check (occurrence : RewriteOccurrence profiles) (requested : Demand profiles)
    (accepted : occurrence.check requested = true) :
    occurrence.right.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles occurrence.right.erase requested = true := by
  have target := (Step.check_iff_right occurrence.toStep requested).mp ((toStep_check occurrence requested).trans accepted)
  simpa only [(toStep_endpoints occurrence).2] using target

theorem erase_checked (occurrence : RewriteOccurrence profiles) (requested : Demand profiles)
    (accepted : occurrence.check requested = true) :
    checkDerivation profiles requested occurrence.toStep.erase.toDerivation = true :=
  occurrence.toStep.erase_checked requested ((toStep_check occurrence requested).trans accepted)

/-- Flatten only the proof's reversal/frame wrappers. Literal siblings and
AC operands stay in their original trees; no expression is reassociated. -/
def ofStep : Step profiles → RewriteOccurrence profiles
  | .primitive entry => ⟨.primitive (.ofPrimitive entry), false, []⟩
  | .multiplyComm demand first second => ⟨.multiplyComm demand first second, false, []⟩
  | .multiplyAssoc demand first second third => ⟨.multiplyAssoc demand first second third, false, []⟩
  | .symm inner => (ofStep inner).reverse
  | .under frame inner => (ofStep inner).under frame

theorem ofStep_endpoints (step : Step profiles) :
    (ofStep step).left = step.left ∧ (ofStep step).right = step.right := by
  induction step with
  | primitive entry =>
      simp only [ofStep, left, right, Frame.fillList, Bool.false_eq_true, if_false,
        RewriteRedex.left, RewriteRedex.right, CheckedPrimitiveRule.left, CheckedPrimitiveRule.right,
        CheckedPrimitiveRule.entry_ofPrimitive, Step.left, Step.right, and_self]
  | multiplyComm | multiplyAssoc => exact ⟨rfl, rfl⟩
  | symm inner ih =>
      simpa only [ofStep, reverse_left, reverse_right, Step.left, Step.right] using And.intro ih.2 ih.1
  | under frame inner ih =>
      exact ⟨congrArg frame.fill ih.1, congrArg frame.fill ih.2⟩

/-- The exact support/annotation boundary is preserved even for rejected
steps. Flattening cannot repair malformed labels or a null denominator. -/
theorem ofStep_check (step : Step profiles) (requested : Demand profiles) :
    (ofStep step).check requested = step.check requested := by
  rw [check, (ofStep_endpoints step).1, Step.check_eq_left]

theorem toStep_ofStep_endpoints (step : Step profiles) :
    (ofStep step).toStep.left = step.left ∧ (ofStep step).toStep.right = step.right :=
  ⟨(toStep_endpoints _).1.trans (ofStep_endpoints step).1,
    (toStep_endpoints _).2.trans (ofStep_endpoints step).2⟩

theorem ofStep_toStep_endpoints (occurrence : RewriteOccurrence profiles) :
    (ofStep occurrence.toStep).left = occurrence.left ∧ (ofStep occurrence.toStep).right = occurrence.right :=
  ⟨(ofStep_endpoints _).1.trans (toStep_endpoints occurrence).1,
    (ofStep_endpoints _).2.trans (toStep_endpoints occurrence).2⟩

theorem ofStep_toStep_check (occurrence : RewriteOccurrence profiles) (requested : Demand profiles) :
    (ofStep occurrence.toStep).check requested = occurrence.check requested :=
  (ofStep_check _ requested).trans (toStep_check occurrence requested)

end RewriteOccurrence
end Thesis.Causality.NativeDemandEncoding
