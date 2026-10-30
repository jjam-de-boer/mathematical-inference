import Thesis.CausalTransport.NativeTypedPrimitives
import Thesis.Causality.PrimitiveAtomCode

namespace Thesis.Causality.NativeDemandTyping

open Probability ProbabilityCode

/-!
# Native support and finite catalogue coverage for actual primitive atoms

A typed primitive entry is reflected from the existing decoder's actual
proof constructor. The resulting atom retains both literal endpoints and
the same interpreted derivation. A hidden transitivity tree cannot enter
through this interface, and no numerical equality is inferred from types.

Conversely, any of the seven primitive atom kinds has a constructive finite
code. If its full native support check passes on the requested profile cells,
it produces an actual entry of the existing finite catalogue. Membership is
proved symbolically; constructing this one entry does not search the whole
catalogue or impose a proof-depth, denominator or hidden-alphabet bound.

AC atoms retain their separate existing schemas, and `actionOne` remains a
top-level wrapper. This stage introduces no encoded step/path language,
normalization algorithm or universal stopping claim.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- Atomic support is exactly support of its two endpoints. This also
applies to the old AC atoms, without putting them in the seven-tag catalogue. -/
theorem check_atom_endpoints (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (atom : DoCalculusAtom P.observedGraph left right) :
    checkDerivation profiles demand atom.toDerivation = (check profiles left demand && check profiles right demand) := by
  cases atom <;> simp only [DoCalculusAtom.toDerivation, checkDerivation, Bool.and_true]

namespace TypedPrimitive

variable {profiles : List (NativeTemplateInstance P)}

def atom (entry : TypedPrimitive profiles) : DoCalculusAtom P.observedGraph entry.checked.left entry.checked.right :=
  (primitiveReflection P.observedGraph entry.kind entry.quad entry.checked entry.decoded).atom

theorem atom_toDerivation (entry : TypedPrimitive profiles) : entry.atom.toDerivation = entry.checked.derivation :=
  (primitiveReflection P.observedGraph entry.kind entry.quad entry.checked entry.decoded).toDerivation_eq

theorem atom_checked (entry : TypedPrimitive profiles) : checkDerivation profiles entry.demand entry.atom.toDerivation = true := by
  rw [entry.atom_toDerivation]
  exact entry.accepted

theorem endpoints_checked (entry : TypedPrimitive profiles) :
    (NativeDemandTyping.check profiles entry.checked.left entry.demand && NativeDemandTyping.check profiles entry.checked.right entry.demand) = true := by
  rw [← check_atom_endpoints profiles entry.demand entry.atom]
  exact entry.atom_checked

/-- Build one real checked entry from the supplied raw primitive and its
support proof. The decoder round-trip supplies its graph/syntax acceptance. -/
def ofAtom (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right)
    (kind : PrimitiveCode) (code : QuadCode) (encoded : leaf.primitiveCode? = some (kind, code))
    (accepted : checkDerivation profiles demand leaf.toDerivation = true) : TypedPrimitive profiles where
  kind := kind
  quad := code
  demand := demand
  checked := ⟨left, right, leaf.toDerivation⟩
  decoded := leaf.check_primitiveCode kind code encoded
  accepted := accepted

theorem ofAtom_endpoints (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right)
    (kind : PrimitiveCode) (code : QuadCode) (encoded : leaf.primitiveCode? = some (kind, code))
    (accepted : checkDerivation profiles demand leaf.toDerivation = true) :
    (ofAtom profiles demand leaf kind code encoded accepted).checked.left = left ∧
      (ofAtom profiles demand leaf kind code encoded accepted).checked.right = right := ⟨rfl, rfl⟩

/-- Coverage is relative to the seven primitive kinds but has no mask-size
or derivation-depth cutoff. The constructed entry is the witness data. -/
theorem ofAtom_mem_catalogue (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right)
    (kind : PrimitiveCode) (code : QuadCode) (encoded : leaf.primitiveCode? = some (kind, code))
    (accepted : checkDerivation profiles demand leaf.toDerivation = true) :
    ofAtom profiles demand leaf kind code encoded accepted ∈ primitiveCatalogue profiles :=
  mem_primitiveCatalogue _

/-- Opt-in execution on one supplied atom. Unsupported atoms and the two
separate AC schemas return `none`; no catalogue enumeration is executed. -/
def ofAtom? (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right) : Option (TypedPrimitive profiles) :=
  match encoded : leaf.primitiveCode? with
  | none => none
  | some (kind, code) =>
      if accepted : checkDerivation profiles demand leaf.toDerivation = true then
        some (ofAtom profiles demand leaf kind code encoded accepted)
      else none

/-- Successful execution retains the supplied literal endpoints, proof and
demand. Future path joins therefore need no metadata-based reconstruction. -/
theorem ofAtom?_checked (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right)
    (entry : TypedPrimitive profiles) (returned : ofAtom? profiles demand leaf = some entry) :
    entry.checked = ⟨left, right, leaf.toDerivation⟩ ∧ entry.demand = demand := by
  unfold ofAtom? at returned
  split at returned
  · simp only [reduceCtorEq] at returned
  · split at returned
    · cases Option.some.inj returned
      exact ⟨rfl, rfl⟩
    · simp only [reduceCtorEq] at returned

theorem ofAtom?_isSome (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles)
    {left right : ProbabilityTerm S} (leaf : DoCalculusAtom P.observedGraph left right) :
    (ofAtom? profiles demand leaf).isSome = (leaf.primitiveCode?.isSome && checkDerivation profiles demand leaf.toDerivation) := by
  unfold ofAtom?
  split
  · next missing => simp only [missing, Option.isSome_none, Bool.false_and]
  · next kind code encoded =>
      split
      · next accepted => simp only [encoded, Option.isSome_some, accepted, Bool.true_and]
      · next rejected =>
          simp only [encoded, Option.isSome_some, Option.isSome_none, Bool.true_and]
          cases checked : checkDerivation profiles demand leaf.toDerivation with
          | false => rfl
          | true => exact False.elim (rejected checked)

end TypedPrimitive
end Thesis.Causality.NativeDemandTyping
