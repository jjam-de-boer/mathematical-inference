import Thesis.CausalTransport.NativeTypePreservation
import Thesis.Causality.DerivationEnumeration

namespace Thesis.Causality.NativeDemandTyping

open Probability ProbabilityCode

/-!
# A finite checked catalogue of demanded primitive rules

The seven serialized primitive tags have only four finite node-mask
parameters. A demand is another finite table: one Boolean for every supplied
profile and every declared reference. Enumerating these data and retaining
only successful syntax/graph and recursive-support checks therefore gives
all accepted primitive instances, without a proof- or expression-depth cap.

Each retained entry carries its actual derivation on the profiles' matching
graph. Its endpoint types agree by native soundness, not by identifying
terms that happen to have equal metadata. The catalogue does not include
contexts, arbitrary commutativity/associativity instances, or the separate
top-level `actionOne` wrapper. It is not a rewrite solver or a universal
formula-coverage theorem.

Enumeration is explicit and opt-in. Its finiteness is not a practical size
bound: the demand table alone has exponentially many possibilities. The
coverage theorem below does not execute that list to find a certificate.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

def referenceDemands (signature : ObservedSignature) : List (signature.Assignment → Bool) :=
  (FiniteFunctionTable.enumeration (referenceWitness signature) [false, true]).map
    (FiniteFunctionTable.lookup (referenceWitness signature))

theorem mem_referenceDemands (signature : ObservedSignature) (demand : signature.Assignment → Bool) :
    demand ∈ referenceDemands signature := by
  apply List.mem_map.mpr
  refine ⟨FiniteFunctionTable.tabulate (referenceWitness signature) demand, ?_, FiniteFunctionTable.lookup_tabulate _ _⟩
  apply FiniteFunctionTable.enumeration_complete
  intro needed
  cases needed <;> simp only [List.mem_cons, true_or, or_true, reduceCtorEq]

/-- All demands on these particular profile/reference cells. This includes
the empty demand and preserves separately requested, conflicting profiles. -/
def demandCatalogue (profiles : List (NativeTemplateInstance P)) : List (Demand profiles) :=
  FiniteProduct.enumeration profiles.length (fun _ => S.Assignment → Bool) (fun _ => referenceDemands S)

theorem mem_demandCatalogue (profiles : List (NativeTemplateInstance P)) (demand : Demand profiles) :
    demand ∈ demandCatalogue profiles :=
  FiniteProduct.enumeration_complete _ _ _ (fun _ => mem_referenceDemands S) demand

/-- The graph decoder and the original recursive support gate both have to
accept. The input supplies finite codes and demands, not a semantic oracle. -/
structure TypedPrimitive (profiles : List (NativeTemplateInstance P)) where
  kind : PrimitiveCode
  quad : QuadCode
  demand : Demand profiles
  checked : CheckedDerivation P.observedGraph
  decoded : checkPrimitive P.observedGraph kind quad = some checked
  accepted : checkDerivation profiles demand checked.derivation = true

namespace TypedPrimitive

def check (profiles : List (NativeTemplateInstance P)) (kind : PrimitiveCode)
    (quad : QuadCode) (demand : Demand profiles) : Option (TypedPrimitive profiles) :=
  match decoded : checkPrimitive P.observedGraph kind quad with
  | none => none
  | some checked =>
      if accepted : checkDerivation profiles demand checked.derivation = true then
        some ⟨kind, quad, demand, checked, decoded, accepted⟩
      else none

def leftType {profiles : List (NativeTemplateInstance P)} (entry : TypedPrimitive profiles) : TermType profiles :=
  typeOf profiles entry.checked.left entry.demand

def rightType {profiles : List (NativeTemplateInstance P)} (entry : TypedPrimitive profiles) : TermType profiles :=
  typeOf profiles entry.checked.right entry.demand

/-- Every retained primitive is a well-supported, type-preserving equation
at precisely its demanded cells. Undemanded cells remain `unused`. -/
theorem types_eq {profiles : List (NativeTemplateInstance P)} (entry : TypedPrimitive profiles) :
    entry.leftType = entry.rightType :=
  typeOf_eq_of_checked profiles entry.demand entry.checked.derivation entry.accepted

theorem check_of_certificate {profiles : List (NativeTemplateInstance P)} (entry : TypedPrimitive profiles) :
    check profiles entry.kind entry.quad entry.demand = some entry := by
  cases entry with
  | mk kind quad demand checked decoded accepted =>
      unfold check
      split
      · next failed => simp only [decoded, reduceCtorEq] at failed
      · next actual recovered =>
          have same : actual = checked := Option.some.inj (recovered.symm.trans decoded)
          subst actual
          rw [dif_pos accepted]

end TypedPrimitive

private theorem mask_bounded {index : Nat} {nodes : NodeSet S} (decoded : mask S index = some nodes) :
    index < (CodeDictionaries.ofSignature S).masks := by
  exact (List.getElem?_eq_some_iff.mp decoded).1

/-- Successful decoding already entails finite dictionary bounds; the
catalogue does not impose an extra assumption on an accepted primitive. -/
private theorem quad_within_of_decoded {code : QuadCode} {quad : Quad S}
    (decoded : code.decode S = some quad) : code.Within (CodeDictionaries.ofSignature S) := by
  cases xDecoded : mask S code.x with
  | none => simp only [QuadCode.decode, xDecoded, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at decoded
  | some x =>
      cases yDecoded : mask S code.y with
      | none => simp only [QuadCode.decode, xDecoded, yDecoded, Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at decoded
      | some y =>
          cases zDecoded : mask S code.z with
          | none => simp only [QuadCode.decode, xDecoded, yDecoded, zDecoded, Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at decoded
          | some z =>
              cases wDecoded : mask S code.w with
              | none => simp only [QuadCode.decode, xDecoded, yDecoded, zDecoded, wDecoded, Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at decoded
              | some w => exact ⟨mask_bounded xDecoded, mask_bounded yDecoded, mask_bounded zDecoded, mask_bounded wDecoded⟩

private theorem checked_primitive_within {graph : ObservedGraph S} {kind : PrimitiveCode}
    {quad : QuadCode} {checked : CheckedDerivation graph}
    (accepted : checkPrimitive graph kind quad = some checked) : quad.Within (CodeDictionaries.ofSignature S) := by
  cases decoded : quad.decode S with
  | none => simp only [checkPrimitive, decoded, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at accepted
  | some fields => exact quad_within_of_decoded decoded

def primitiveCatalogue (profiles : List (NativeTemplateInstance P)) : List (TypedPrimitive profiles) :=
  PrimitiveCode.enumerate.flatMap (fun kind =>
    (QuadCode.enumerate (CodeDictionaries.ofSignature S)).flatMap (fun quad =>
      (demandCatalogue profiles).filterMap (TypedPrimitive.check profiles kind quad)))

/-- Exact finite coverage of accepted *primitive* certificates. No list
search, witness choice or bound on arbitrary derivations is used here. -/
theorem mem_primitiveCatalogue {profiles : List (NativeTemplateInstance P)} (entry : TypedPrimitive profiles) :
    entry ∈ primitiveCatalogue profiles := by
  apply List.mem_flatMap.mpr
  refine ⟨entry.kind, PrimitiveCode.mem_enumerate entry.kind, List.mem_flatMap.mpr ?_⟩
  refine ⟨entry.quad, (QuadCode.mem_enumerate_iff _ _).mpr (checked_primitive_within entry.decoded), List.mem_filterMap.mpr ?_⟩
  exact ⟨entry.demand, mem_demandCatalogue profiles entry.demand, entry.check_of_certificate⟩

end Thesis.Causality.NativeDemandTyping
