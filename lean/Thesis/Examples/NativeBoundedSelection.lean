import Thesis.CausalTransport.NativeBoundedSelection
import Thesis.Examples.NativeSearchMetadata

namespace Thesis.Causality.Examples.NativeBoundedSelection

open Probability ProbabilityCode NativeSupportProfiles NativeCertificateCheck NativeSearchPreflight

/-!
# Bounded selection: refusal, unavailable catalogues and genuine zero values

Use only the existing tiny three-valued native fixture and supplied support
profiles. Concrete admitted searches inspect eight native leaves, never a
complete model-class catalogue or a large derivation list. The deeper null
reference coverage test uses the general theorem symbolically instead.

An empty guard rejects even a well-formed printed expression. A rejected
first candidate must not hide a later available one. Conversely, an admitted
nonempty catalogue can have no available member. Resource refusals remain
different results, not aliases for either an empty or an unavailable list.

The null observational outcome has a defined probability zero and is retained
by selection. A separate null original conditioner remains unsupported even
when a checked formula can be selected; it cannot satisfy the explicit native
soundness premise. Selection is not itself a source-support oracle.
-/

def sizes : DomainSizeMetadata signature := NativeSearchMetadata.sizes

/-- Keep the certificate and its printed formula, but deliberately reject
all applications. Checking an empty guard is constructive and vacuous. -/
def unavailable : CheckedNativeFormula projection.observedGraph profiles :=
  { good with guard := [], guardChecked := rfl }

theorem unavailable_rejected : unavailable.available entry.model.observationalDist (reference 2) = false := rfl

theorem later_available_selected :
    CheckedNativeFormula.select entry.model.observationalDist (reference 2) [unavailable, good] = some good := by
  rw [CheckedNativeFormula.select_cons_of_unavailable _ _ unavailable [good] unavailable_rejected]
  exact CheckedNativeFormula.select_cons_of_available _ _ good [] good_available

example : CheckedNativeFormula.select entry.model.observationalDist (reference 2) [unavailable] = none := by
  rw [CheckedNativeFormula.select_cons_of_unavailable _ _ unavailable [] unavailable_rejected]
  rfl

example : CheckedNativeFormula.select entry.model.observationalDist (reference 2) [good, unavailable] = some good :=
  CheckedNativeFormula.select_cons_of_available _ _ good [unavailable] good_available

example : CheckedNativeFormula.select entry.model.observationalDist (reference 2) [conditional] = none := by
  rw [CheckedNativeFormula.select_cons_of_unavailable _ _ conditional [] (by decide +kernel)]
  rfl

example : CheckedNativeFormula.select entry.model.observationalDist (reference 2) [nullSource] = some nullSource :=
  CheckedNativeFormula.select_cons_of_available _ _ nullSource [] (by decide +kernel)

example : ¬ Nonempty (entry.model.TermSupportedAt nullSource.source (reference 2)) := null_source_has_no_support

example : NativeProofCode.guardedSelectOnWithMetadata limits projection.observedGraph sizes profiles source
    1000000 1 entry.model.observationalDist (reference 2) = .error (.expressionDepth 1000000 4) := rfl
example : NativeProofCode.guardedSelectOnWithMetadata { limits with maxDictionaryEntries := 2 }
    projection.observedGraph sizes profiles source 0 1 entry.model.observationalDist (reference 2) =
      .error (.referenceDictionary 2) := rfl
example : NativeProofCode.guardedSelectOnWithMetadata { limits with maxRawCandidates := 0 }
    projection.observedGraph sizes profiles source 0 1 entry.model.observationalDist (reference 2) =
      .error (.rawCandidates 0) := rfl
example : NativeProofCode.guardedSelectOnWithMetadata { limits with maxProfiles := 0 }
    projection.observedGraph sizes profiles source 0 1 entry.model.observationalDist (reference 2) =
      .error (.profiles 0) := rfl
example : NativeProofCode.guardedSelectOnWithMetadata { limits with maxTotalProfileComparisons := 0 }
    projection.observedGraph sizes profiles source 0 1 entry.model.observationalDist (reference 2) =
      .error (.totalProfileComparisons 0) := rfl

example : NativeProofCode.guardedSelectOnWithMetadata limits projection.observedGraph sizes profiles source
    0 0 entry.model.observationalDist (reference 2) = .ok none := rfl

/-- A defined zero at the declared null outcome is a successful selection,
not an undefined result and not grounds for deleting this reference. -/
example : (match NativeProofCode.guardedSelectOnWithMetadata limits projection.observedGraph sizes profiles source
    0 1 entry.model.observationalDist (reference 2) with
    | .ok (some chosen) => ProbabilityResult.status (chosen.formula.observationalDenote entry.model.observationalDist (reference 2)) == .zero
    | _ => false) = true := by decide +kernel

def actionSource : TermCode := .kernel ⟨1, 1, 0⟩

/-- The action-one leaf exists but its compiled guard has no accepted row
for this non-degenerate law. This is not an empty raw/certified catalogue. -/
example : (match NativeProofCode.guardedCatalogueOnWithMetadata limits projection.observedGraph sizes profiles actionSource 0 1 with
    | .ok catalogue => !catalogue.isEmpty
    | .error _ => false) = true := by decide +kernel

example : (match NativeProofCode.guardedSelectOnWithMetadata limits projection.observedGraph sizes profiles actionSource
    0 1 entry.model.observationalDist (reference 2) with
    | .ok none => true
    | _ => false) = true := by decide +kernel

/-- Apply actual selection soundness to the original decoded joint query.
The source value is independently supported; selection did not assume it. -/
noncomputable def selected_sound (chosen : CheckedNativeFormula projection.observedGraph profiles)
    (selected : NativeProofCode.guardedSelectOnWithMetadata limits projection.observedGraph sizes profiles source
      0 1 entry.model.observationalDist (reference 2) = .ok (some chosen)) :
    entry.model.TermEquivalentAt (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩) chosen.formula (reference 2) :=
  NativeProofCode.guardedSelectOnWithMetadata_soundAt limits projection.observedGraph sizes profiles source 0 1
    (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩) (by decide +kernel) entry.model rfl
    ⟨entry.uniformSupport, List.mem_cons_self, entry.uniformSupport_agreement⟩ (reference 2) chosen selected
    (ProbabilityResult.supportedOfIsSome _ (by decide +kernel))

theorem admitted_null_cell_selected (catalogue : List (CheckedNativeFormula projection.observedGraph profiles))
    (admitted : NativeProofCode.guardedCatalogueOnWithMetadata limits projection.observedGraph sizes profiles source 1 2 = .ok catalogue) :
    ∃ chosen, NativeProofCode.guardedSelectOnWithMetadata limits projection.observedGraph sizes profiles source
      1 2 entry.model.observationalDist (reference 2) = .ok (some chosen) ∧
      chosen.available entry.model.observationalDist (reference 2) = true :=
  NativeProofCode.guardedSelectOnWithMetadata_covers limits projection.observedGraph sizes profiles 1 2
    goodCode (by decide +kernel) good NativeProofEnumeration.good_checked catalogue admitted entry.model
    ⟨entry.uniformSupport, List.mem_cons_self, entry.uniformSupport_agreement⟩ (reference 2) good_available

end Thesis.Causality.Examples.NativeBoundedSelection
