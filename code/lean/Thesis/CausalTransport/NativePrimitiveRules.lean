import Thesis.CausalTransport.NativeDemandEncoding

namespace Thesis.Causality.NativeDemandEncoding

open Probability ProbabilityCode NativeDemandTyping

/-!
# Finite accepted primitive-rule codes and their ground equations

A raw code retains the existing primitive tag, four numeric mask indices,
and the complete finite demand table. Decoding uses the original graph and
native support checker. Invalid indices, graphical conditions and demanded
null conditionals retain that checker's rejection.

A checked rule stores just its code and the decoder's Boolean acceptance.
Its actual primitive proof is reconstructed by reading the computed option;
there is no arbitrary derivation field or selected existential witness.
Conversion from an existing typed primitive recovers exactly that primitive.

Raw numeric codes may be invalid. The successfully decoded codes have an
explicit finite catalogue, inherited from the existing primitive catalogue.
Their endpoint pairs are ground equations over the existing finite alphabet.
Enumeration stays opt-in: the proofs below do not search or normalize the
catalogue. Contexts and arbitrary AC operands are not extra rule parameters;
the two strict multiplication schemas are handled separately by occurrences.
No external byte parser, formula selector or terminating search is asserted.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

structure PrimitiveRuleCode (profiles : List (NativeTemplateInstance P)) where
  kind : PrimitiveCode
  quad : QuadCode
  demand : Demand profiles

namespace PrimitiveRuleCode

variable {profiles : List (NativeTemplateInstance P)}

def decode (code : PrimitiveRuleCode profiles) : Option (TypedPrimitive profiles) :=
  TypedPrimitive.check profiles code.kind code.quad code.demand

def ofPrimitive (entry : TypedPrimitive profiles) : PrimitiveRuleCode profiles :=
  ⟨entry.kind, entry.quad, entry.demand⟩

theorem decode_ofPrimitive (entry : TypedPrimitive profiles) :
    (ofPrimitive entry).decode = some entry := entry.check_of_certificate

/-- Successful decoding retains all input fields, including the exact
demand table. A graph/support success never substitutes another rule code. -/
theorem ofPrimitive_of_decoded (code : PrimitiveRuleCode profiles) (entry : TypedPrimitive profiles)
    (decoded : code.decode = some entry) : ofPrimitive entry = code := by
  cases code with
  | mk kind quad demand =>
      unfold decode TypedPrimitive.check at decoded
      split at decoded
      · simp only [reduceCtorEq] at decoded
      · split at decoded
        · cases Option.some.inj decoded
          rfl
        · simp only [reduceCtorEq] at decoded

end PrimitiveRuleCode

structure CheckedPrimitiveRule (profiles : List (NativeTemplateInstance P)) where
  code : PrimitiveRuleCode profiles
  accepted : code.decode.isSome = true

namespace CheckedPrimitiveRule

variable {profiles : List (NativeTemplateInstance P)}

def entry (rule : CheckedPrimitiveRule profiles) : TypedPrimitive profiles := rule.code.decode.get rule.accepted

theorem decoded_entry (rule : CheckedPrimitiveRule profiles) : rule.code.decode = some rule.entry := by
  have accepted := rule.accepted
  cases decoded : rule.code.decode with
  | none => simp only [decoded, Option.isSome_none, Bool.false_eq_true] at accepted
  | some value => simp only [entry, decoded, Option.get_some]

def ofPrimitive (entry : TypedPrimitive profiles) : CheckedPrimitiveRule profiles :=
  ⟨PrimitiveRuleCode.ofPrimitive entry, by rw [PrimitiveRuleCode.decode_ofPrimitive]; rfl⟩

theorem entry_ofPrimitive (primitive : TypedPrimitive profiles) : (ofPrimitive primitive).entry = primitive := by
  simp only [entry, ofPrimitive, PrimitiveRuleCode.decode_ofPrimitive, Option.get_some]

private theorem eq_of_code_eq (first second : CheckedPrimitiveRule profiles) (same : first.code = second.code) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

theorem ofPrimitive_entry (rule : CheckedPrimitiveRule profiles) : ofPrimitive rule.entry = rule :=
  eq_of_code_eq _ _ (PrimitiveRuleCode.ofPrimitive_of_decoded rule.code rule.entry rule.decoded_entry)

/-- Complete finite coverage of checked rule data. The witness is the
rule's own decoded entry, so no catalogue search or choice is needed. -/
def catalogue (profiles : List (NativeTemplateInstance P)) : List (CheckedPrimitiveRule profiles) :=
  (primitiveCatalogue profiles).map ofPrimitive

theorem mem_catalogue (rule : CheckedPrimitiveRule profiles) : rule ∈ catalogue profiles :=
  List.mem_map.mpr ⟨rule.entry, mem_primitiveCatalogue _, ofPrimitive_entry rule⟩

def left (rule : CheckedPrimitiveRule profiles) : Term profiles :=
  Term.encode profiles rule.entry.checked.left rule.entry.demand

def right (rule : CheckedPrimitiveRule profiles) : Term profiles :=
  Term.encode profiles rule.entry.checked.right rule.entry.demand

/-- These are literal ground pairs; a sibling expression never becomes
an infinite-alphabet parameter of a primitive rule. -/
def equations (profiles : List (NativeTemplateInstance P)) : List (Term profiles × Term profiles) :=
  (catalogue profiles).map (fun rule => (rule.left, rule.right))

theorem mem_equations (rule : CheckedPrimitiveRule profiles) : (rule.left, rule.right) ∈ equations profiles :=
  List.mem_map_of_mem (f := fun candidate => (candidate.left, candidate.right)) rule.mem_catalogue

end CheckedPrimitiveRule

namespace PrimitiveRuleCode

variable {profiles : List (NativeTemplateInstance P)}

/-- Opt-in checking of one supplied code. It does not enumerate rules or
contexts, and rejection retains the existing syntax/graph/support boundary. -/
def check (code : PrimitiveRuleCode profiles) : Option (CheckedPrimitiveRule profiles) :=
  if accepted : code.decode.isSome = true then some ⟨code, accepted⟩ else none

theorem check_isSome (code : PrimitiveRuleCode profiles) : code.check.isSome = code.decode.isSome := by
  unfold check
  split
  · next accepted => simp only [Option.isSome_some, accepted]
  · next rejected =>
      cases decoded : code.decode.isSome with
      | false => rfl
      | true => exact False.elim (rejected decoded)

end PrimitiveRuleCode
end Thesis.Causality.NativeDemandEncoding
