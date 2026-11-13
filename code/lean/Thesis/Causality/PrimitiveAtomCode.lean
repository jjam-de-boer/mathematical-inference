import Thesis.Causality.DerivationCode
import Thesis.Causality.DerivationLinearization

namespace Thesis.Causality

open Probability

/-!
# Constructive codes and reflection for the seven primitive decoder leaves

Masks are encoded by their positions in the existing complete, duplicate-free
dictionary. The finite witness computes both directions; no inverse is
selected from a propositional existence proof. All node selections remain
available, independently of observational or intervention support.

Reflection inspects the actual decoded derivation constructor. It returns
an existing `DoCalculusAtom` together with equality of its interpretation to
the decoded proof. It has no recursive branch: transitivity, congruence,
reflexivity and reversal cannot hide beneath a claimed primitive leaf.
The existing decoder supplies every graphical condition, including rule 3's
incoming cut; it is neither replaced nor relaxed here. The two AC schemas
remain outside this seven-tag primitive encoder.

This module supplies graph/syntax data only. Native support, finite typed
catalogue coverage, and any later encoded-step language are separate layers.
-/

variable {S : ObservedSignature} {G : ObservedGraph S}

namespace ProbabilityCode

def maskWitness (signature : ObservedSignature) : FiniteWitness (NodeSet signature) :=
  .ofList (NodeSet.subsets NodeSet.full)
    (fun _ => (NodeSet.subsets_member_iff _ _).mpr (fun _ _ => rfl))
    (NodeSet.subsets_nodup NodeSet.full)

def encodeMask (signature : ObservedSignature) (nodes : NodeSet signature) : Nat :=
  ((maskWitness signature).encode nodes).val

theorem encodeMask_lt (signature : ObservedSignature) (nodes : NodeSet signature) :
    encodeMask signature nodes < (NodeSet.subsets (S := signature) NodeSet.full).length :=
  ((maskWitness signature).encode nodes).isLt

theorem mask_encodeMask (signature : ObservedSignature) (nodes : NodeSet signature) :
    mask signature (encodeMask signature nodes) = some nodes := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨encodeMask_lt signature nodes, (maskWitness signature).decode_encode nodes⟩

/-- Valid indices recover their original code; out-of-range inputs retain
the original decoder's rejection rather than acquiring a default mask. -/
theorem encodeMask_of_mask {index : Nat} {nodes : NodeSet S} (decoded : mask S index = some nodes) :
    encodeMask S nodes = index := by
  rcases List.getElem?_eq_some_iff.mp decoded with ⟨bounded, same⟩
  let code : Fin (maskWitness S).card := ⟨index, bounded⟩
  have decodedCode : (maskWitness S).decode code = nodes := same
  have recovered := congrArg Fin.val ((maskWitness S).encode_decode code)
  rw [decodedCode] at recovered
  exact recovered

def Quad.encode (quad : Quad S) : QuadCode :=
  ⟨encodeMask S quad.x, encodeMask S quad.y, encodeMask S quad.z, encodeMask S quad.w⟩

theorem Quad.decode_encode (quad : Quad S) : quad.encode.decode S = some quad := by
  cases quad
  simp only [Quad.encode, QuadCode.decode, mask_encodeMask, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem Quad.disjoint_eq_true_iff (quad : Quad S) :
    quad.disjoint = true ↔ FourWayDisjoint quad.x quad.y quad.z quad.w := by
  constructor
  · exact quad.disjointOfCheck
  · intro witness
    simp only [Quad.disjoint, Bool.and_eq_true_iff, NodeSet.disjointBool_eq_true_iff]
    exact ⟨⟨⟨⟨⟨witness.xy, witness.xz⟩, witness.xw⟩, witness.yz⟩, witness.yw⟩, witness.zw⟩

/-- The atom has the decoded proof's literal endpoint indices. Its equality
field concerns actual proof data, not denotational or metadata equivalence. -/
structure AtomReflection {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) where
  atom : DoCalculusAtom G left right
  toDerivation_eq : atom.toDerivation = derivation

def reflectPrimitive? {left right : ProbabilityTerm S} :
    (derivation : DoCalculusDerivation G left right) → Option (AtomReflection derivation)
  | .doRule application => some ⟨.doRule application, rfl⟩
  | .marginalization x y z w disjoint => some ⟨.marginalization x y z w disjoint, rfl⟩
  | .conditioning x y z w disjoint => some ⟨.conditioning x y z w disjoint, rfl⟩
  | .chain x y z w disjoint => some ⟨.chain x y z w disjoint, rfl⟩
  | .weightedChain x y z w disjoint => some ⟨.weightedChain x y z w disjoint, rfl⟩
  | _ => none

/-- Every successful primitive decoding really has one of the seven leaf
forms. The proof follows the existing decoder, without a second graph test. -/
theorem checkPrimitive_reflects (graph : ObservedGraph S) (kind : PrimitiveCode) (code : QuadCode)
    (checked : CheckedDerivation graph) (accepted : checkPrimitive graph kind code = some checked) :
    (reflectPrimitive? checked.derivation).isSome = true := by
  cases decoded : code.decode S with
  | none => simp only [checkPrimitive, decoded, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at accepted
  | some quad =>
      simp only [checkPrimitive, decoded, Option.bind_eq_bind, Option.bind_some] at accepted
      split at accepted
      · cases kind <;> simp only [] at accepted <;> (try split at accepted)
        all_goals
          simp only [Option.pure_def, reduceCtorEq] at accepted <;>
            cases Option.some.inj accepted <;> rfl
      · simp only [reduceCtorEq] at accepted

def primitiveReflection (graph : ObservedGraph S) (kind : PrimitiveCode) (code : QuadCode)
    (checked : CheckedDerivation graph) (accepted : checkPrimitive graph kind code = some checked) :
    AtomReflection checked.derivation :=
  (reflectPrimitive? checked.derivation).get (checkPrimitive_reflects graph kind code checked accepted)

end ProbabilityCode

namespace DoCalculusAtom

open ProbabilityCode

/-- The existing seven-tag language, with constructive finite mask codes.
AC atoms are intentionally represented by their separate existing schemas. -/
def primitiveCode? {left right : ProbabilityTerm S} :
    DoCalculusAtom G left right → Option (PrimitiveCode × QuadCode)
  | .doRule application => match application with
    | .rule1 x y z w _ _ => some (.rule1, (⟨x, y, z, w⟩ : Quad S).encode)
    | .rule2 x y z w _ _ => some (.rule2, (⟨x, y, z, w⟩ : Quad S).encode)
    | .rule3 x y z w _ _ => some (.rule3, (⟨x, y, z, w⟩ : Quad S).encode)
  | .marginalization x y z w _ => some (.marginalization, (⟨x, y, z, w⟩ : Quad S).encode)
  | .conditioning x y z w _ => some (.conditioning, (⟨x, y, z, w⟩ : Quad S).encode)
  | .chain x y z w _ => some (.chain, (⟨x, y, z, w⟩ : Quad S).encode)
  | .weightedChain x y z w _ => some (.weightedChain, (⟨x, y, z, w⟩ : Quad S).encode)
  | .multiplyComm _ _ | .multiplyAssoc _ _ _ => none

/-- The finite code returns the original primitive's literal endpoints and
proof constructor. Round-trip equalities replace the dictionary lookups
before comparing proof data; no definitional equality of mask functions is
assumed. Disjointness and separation come from the original atom. -/
theorem check_primitiveCode {left right : ProbabilityTerm S} (atom : DoCalculusAtom G left right)
    (kind : PrimitiveCode) (code : QuadCode) (encoded : atom.primitiveCode? = some (kind, code)) :
    checkPrimitive G kind code = some ⟨left, right, atom.toDerivation⟩ := by
  cases atom with
  | doRule application =>
      cases application with
      | rule1 x y z w disjoint separated =>
          change _ = true at separated
          simp only [primitiveCode?, Option.some.injEq, Prod.mk.injEq] at encoded
          rcases encoded with ⟨rfl, rfl⟩
          simp only [checkPrimitive, Quad.decode_encode, Option.bind_eq_bind, Option.bind_some,
            dif_pos ((Quad.disjoint_eq_true_iff (⟨x, y, z, w⟩ : Quad S)).mpr disjoint),
            dif_pos separated, Option.pure_def, DoCalculusAtom.toDerivation]
      | rule2 x y z w disjoint separated =>
          change _ = true at separated
          simp only [primitiveCode?, Option.some.injEq, Prod.mk.injEq] at encoded
          rcases encoded with ⟨rfl, rfl⟩
          simp only [checkPrimitive, Quad.decode_encode, Option.bind_eq_bind, Option.bind_some,
            dif_pos ((Quad.disjoint_eq_true_iff (⟨x, y, z, w⟩ : Quad S)).mpr disjoint),
            dif_pos separated, Option.pure_def, DoCalculusAtom.toDerivation]
      | rule3 x y z w disjoint separated =>
          change _ = true at separated
          simp only [primitiveCode?, Option.some.injEq, Prod.mk.injEq] at encoded
          rcases encoded with ⟨rfl, rfl⟩
          simp only [checkPrimitive, Quad.decode_encode, Option.bind_eq_bind, Option.bind_some,
            dif_pos ((Quad.disjoint_eq_true_iff (⟨x, y, z, w⟩ : Quad S)).mpr disjoint),
            dif_pos separated, Option.pure_def, DoCalculusAtom.toDerivation]
  | marginalization x y z w disjoint =>
      simp only [primitiveCode?, Option.some.injEq, Prod.mk.injEq] at encoded
      rcases encoded with ⟨rfl, rfl⟩
      simp only [checkPrimitive, Quad.decode_encode, Option.bind_eq_bind, Option.bind_some,
        dif_pos ((Quad.disjoint_eq_true_iff (⟨x, y, z, w⟩ : Quad S)).mpr disjoint), Option.pure_def, DoCalculusAtom.toDerivation]
  | conditioning x y z w disjoint =>
      simp only [primitiveCode?, Option.some.injEq, Prod.mk.injEq] at encoded
      rcases encoded with ⟨rfl, rfl⟩
      simp only [checkPrimitive, Quad.decode_encode, Option.bind_eq_bind, Option.bind_some,
        dif_pos ((Quad.disjoint_eq_true_iff (⟨x, y, z, w⟩ : Quad S)).mpr disjoint), Option.pure_def, DoCalculusAtom.toDerivation]
  | chain x y z w disjoint =>
      simp only [primitiveCode?, Option.some.injEq, Prod.mk.injEq] at encoded
      rcases encoded with ⟨rfl, rfl⟩
      simp only [checkPrimitive, Quad.decode_encode, Option.bind_eq_bind, Option.bind_some,
        dif_pos ((Quad.disjoint_eq_true_iff (⟨x, y, z, w⟩ : Quad S)).mpr disjoint), Option.pure_def, DoCalculusAtom.toDerivation]
  | weightedChain x y z w disjoint =>
      simp only [primitiveCode?, Option.some.injEq, Prod.mk.injEq] at encoded
      rcases encoded with ⟨rfl, rfl⟩
      simp only [checkPrimitive, Quad.decode_encode, Option.bind_eq_bind, Option.bind_some,
        dif_pos ((Quad.disjoint_eq_true_iff (⟨x, y, z, w⟩ : Quad S)).mpr disjoint), Option.pure_def, DoCalculusAtom.toDerivation]
  | multiplyComm => simp only [primitiveCode?, reduceCtorEq] at encoded
  | multiplyAssoc => simp only [primitiveCode?, reduceCtorEq] at encoded

end DoCalculusAtom
end Thesis.Causality
