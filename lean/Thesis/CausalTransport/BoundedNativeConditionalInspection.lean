import Thesis.CausalTransport.BoundedNativeSearch

namespace Thesis.Causality

open Probability

/-!
# Independent evidence-support and conditional-value inspection

A conditional query is evaluated in its actual interventional distribution.
Its value requires positive evidence; there is deliberately no totalized value
at a null event. Two finite-list inspections answer different questions:

* `inspectSupport` either proves positivity throughout the list or returns a
  listed model with exactly zero evidence mass.
* `inspectValues` compares only positive-evidence models. It returns exclusion
  of all supported models, an attained common conditional value, or two
  supported models whose conditional values differ.

In particular, finding a null-evidence model does not discard the conditional
comparison among the remaining models. Empty-list support is vacuous at this
internal level; the public bounded checker separately reports compatibility.
Only finite event-mass positivity and exact rational equalities are decided.
-/

/-- A supported conditional under one hard intervention, not an observational
evidence test substituted for causal evidence. -/
structure NativeConditionalQuery (S : ObservedSignature) where
  intervention : HardIntervention S
  evidence : Event S.Assignment
  event : Event S.Assignment

namespace NativeConditionalQuery

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

def Supported (query : NativeConditionalQuery S) (model : FiniteHiddenDAGSCM S P) : Prop :=
  (model.interventionalDist query.intervention).EventPositive query.evidence

/-- This instance computes just one finite event mass. It does not decide a
quantified model-class statement or invoke the bounded catalogue search. -/
instance (query : NativeConditionalQuery S) (model : FiniteHiddenDAGSCM S P) :
    Decidable (query.Supported model) := by
  unfold Supported
  infer_instance

def value (query : NativeConditionalQuery S) (model : FiniteHiddenDAGSCM S P)
    (supported : query.Supported model) : QProb :=
  ((model.interventionalDist query.intervention).conditionOn query.evidence supported).probVal query.event

/-- The finite-record numerator is the evidence mass itself. This equivalence
does not infer positivity from a nonzero denominator of the ambient law. -/
theorem supported_iff_num_pos (query : NativeConditionalQuery S) (model : FiniteHiddenDAGSCM S P) :
    query.Supported model ↔ 0 < (model.interventionalValue query.intervention query.evidence).num := Iff.rfl

theorem num_zero_of_not_supported (query : NativeConditionalQuery S) (model : FiniteHiddenDAGSCM S P)
    (unsupported : ¬ query.Supported model) :
    (model.interventionalValue query.intervention query.evidence).num = 0 :=
  Nat.eq_zero_of_not_pos unsupported

end NativeConditionalQuery

namespace NativeTemplateInstance

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

inductive ConditionalSupportInspection (query : NativeConditionalQuery S)
    (candidates : List (NativeTemplateInstance P)) where
  | allSupported (positive : ∀ entry, entry ∈ candidates → query.Supported entry.model)
  | nullWitness (witness : NativeTemplateInstance P) (listed : witness ∈ candidates)
      (nullEvidence : (witness.model.interventionalValue query.intervention query.evidence).num = 0)

/-- Search for an actual null-evidence witness independently of the values.
The negative answer is a proof about every listed candidate, not a failed
attempt to locate a witness. -/
def inspectSupport (query : NativeConditionalQuery S) :
    (candidates : List (NativeTemplateInstance P)) → ConditionalSupportInspection query candidates
  | [] => .allSupported (by intro _ member; exact False.elim (List.not_mem_nil member))
  | head :: tail =>
      if positive : query.Supported head.model then
        match inspectSupport query tail with
        | .allSupported remaining => .allSupported (by
            intro entry member
            rcases List.mem_cons.mp member with same | listed
            · subst entry; exact positive
            · exact remaining entry listed)
        | .nullWitness witness listed nullEvidence =>
            .nullWitness witness (List.mem_cons_of_mem head listed) nullEvidence
      else .nullWitness head List.mem_cons_self (query.num_zero_of_not_supported head.model positive)

inductive ConditionalValueInspection (query : NativeConditionalQuery S)
    (candidates : List (NativeTemplateInstance P)) where
  | unsupported (noSupport : ∀ entry, entry ∈ candidates → ¬ query.Supported entry.model)
  | identified (witness : NativeTemplateInstance P) (listed : witness ∈ candidates)
      (supported : query.Supported witness.model)
      (constant : ∀ entry, entry ∈ candidates → (positive : query.Supported entry.model) →
        QProb.Equiv (query.value entry.model positive) (query.value witness.model supported))
  | ambiguous (left right : NativeTemplateInstance P)
      (leftListed : left ∈ candidates) (rightListed : right ∈ candidates)
      (leftSupported : query.Supported left.model) (rightSupported : query.Supported right.model)
      (different : ¬ QProb.Equiv (query.value left.model leftSupported) (query.value right.model rightSupported))

namespace ConditionalValueInspection

variable {query : NativeConditionalQuery S} {tail : List (NativeTemplateInstance P)}

/-- A null-evidence head contributes no conditional value. In particular it
cannot turn an attained common supported value into an undefined result. -/
def prependNull (answer : ConditionalValueInspection query tail) (head : NativeTemplateInstance P)
    (nullEvidence : ¬ query.Supported head.model) : ConditionalValueInspection query (head :: tail) :=
  match answer with
  | .unsupported noSupport => .unsupported (by
      intro entry member
      rcases List.mem_cons.mp member with same | listed
      · subst entry; exact nullEvidence
      · exact noSupport entry listed)
  | .identified witness listed supported constant =>
      .identified witness (List.mem_cons_of_mem head listed) supported (by
        intro entry member positive
        rcases List.mem_cons.mp member with same | remaining
        · subst entry; exact False.elim (nullEvidence positive)
        · exact constant entry remaining positive)
  | .ambiguous left right leftListed rightListed leftSupported rightSupported different =>
      .ambiguous left right (List.mem_cons_of_mem head leftListed) (List.mem_cons_of_mem head rightListed)
        leftSupported rightSupported different

/-- A supported head either supplies the first attained value, agrees with
the previous common value, or supplies a genuine supported countermodel. -/
def prependSupported (answer : ConditionalValueInspection query tail) (head : NativeTemplateInstance P)
    (positive : query.Supported head.model) : ConditionalValueInspection query (head :: tail) :=
  match answer with
  | .unsupported noSupport => .identified head List.mem_cons_self positive (by
      intro entry member supported
      rcases List.mem_cons.mp member with same | listed
      · subst entry; exact QProb.equiv_refl _
      · exact False.elim (noSupport entry listed supported))
  | .identified witness listed supported constant =>
      if same : QProb.Equiv (query.value head.model positive) (query.value witness.model supported) then
        .identified head List.mem_cons_self positive (by
          intro entry member entrySupported
          rcases List.mem_cons.mp member with equalHead | remaining
          · subst entry; exact QProb.equiv_refl _
          · exact QProb.equiv_trans (constant entry remaining entrySupported) (QProb.equiv_symm same))
      else .ambiguous head witness List.mem_cons_self (List.mem_cons_of_mem head listed) positive supported same
  | .ambiguous left right leftListed rightListed leftSupported rightSupported different =>
      .ambiguous left right (List.mem_cons_of_mem head leftListed) (List.mem_cons_of_mem head rightListed)
        leftSupported rightSupported different

end ConditionalValueInspection

/-- A structural recursion over the finite list, with no conditioning operation
in the null branch and no unbounded formula or model search. -/
def inspectValues (query : NativeConditionalQuery S) :
    (candidates : List (NativeTemplateInstance P)) → ConditionalValueInspection query candidates
  | [] => .unsupported (by intro _ member; exact False.elim (List.not_mem_nil member))
  | head :: tail =>
      if positive : query.Supported head.model then
        (inspectValues query tail).prependSupported head positive
      else (inspectValues query tail).prependNull head positive

end NativeTemplateInstance
end Thesis.Causality
