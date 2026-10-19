import Thesis.CausalTransport.NativeCertificateCheck

namespace Thesis.Causality

open Probability

/-!
# Maximal observable guards for a fixed checked support discipline

For a supplied proof, generate rows from the observed support patterns that
actually occur in its finite causal-profile catalogue and every declared
reference index. Retain exactly those rows passing the existing universal
profile check. No separate cube of hypothetical observed patterns is needed.
Duplicate rows are harmless; no minimality or deduplication claim is made.

The resulting table is checked by construction. Any other checked table for
the same demand has no greater acceptance on records whose observed pattern
is represented in the catalogue. Complete causal profile coverage supplies
that premise for every original model in both public native model classes.
The original conditional-source premise remains separate from availability.

"Maximal" is relative to the supplied proof's declared support requirements,
not every semantically valid argument for its formula. A derivation with an
undefined intermediate may be rejected where a different proof succeeds.
Neither proof enumeration, formula selection, semantic validity decision nor
universal alternative-formula coverage follows from this construction.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace NativeSupportGuard

/-- Only represented observed patterns are needed for native coverage.
Every reference remains included, also a factually null intervention value. -/
def rows (profiles : List (NativeTemplateInstance Q)) : Code :=
  profiles.flatMap (fun entry => (List.range S.assignmentEnumeration.length).map
    (fun index => ⟨pattern S entry.model.observationalDist, index⟩))

theorem row_mem (profiles : List (NativeTemplateInstance Q)) (entry : NativeTemplateInstance Q)
    (listed : entry ∈ profiles) (index : Nat) (bounded : index < S.assignmentEnumeration.length) :
    (⟨pattern S entry.model.observationalDist, index⟩ : Cell) ∈ rows profiles :=
  List.mem_flatMap_of_mem listed (List.mem_map_of_mem (f := fun current =>
    (⟨pattern S entry.model.observationalDist, current⟩ : Cell)) (List.mem_range.mpr bounded))

def compile (profiles : List (NativeTemplateInstance Q)) (demand : Demand S) : Code :=
  (rows profiles).filter (checkCell profiles demand)

theorem mem_compile_iff (profiles : List (NativeTemplateInstance Q)) (demand : Demand S) (cell : Cell) :
    cell ∈ compile profiles demand ↔ cell ∈ rows profiles ∧ checkCell profiles demand cell = true :=
  List.mem_filter

/-- Certification is a theorem of the generated data, not a new assumption
about the profile producer or a test against one chosen representative. -/
theorem compile_checked (profiles : List (NativeTemplateInstance Q)) (demand : Demand S) :
    check profiles demand (compile profiles demand) = true := by
  apply List.all_eq_true.mpr
  intro cell listed
  exact (List.mem_filter.mp listed).2

/-- A row accepted at a represented observed pattern is among the generated
rows. The index bound follows from successful decoding, not from choice of
an assignment representative or a fabricated default for invalid input. -/
theorem row_mem_of_accepts (profiles : List (NativeTemplateInstance Q)) (cell : Cell)
    (record : FiniteProbRecord S.Assignment)
    (represented : ∃ entry, entry ∈ profiles ∧ pattern S entry.model.observationalDist = pattern S record)
    (reference : S.Assignment) (accepted : cell.accepts record reference = true) : cell ∈ rows profiles := by
  rcases represented with ⟨entry, listed, observed⟩
  cases decoded : ProbabilityCode.assignment S cell.reference with
  | none =>
      simp only [Cell.accepts, decoded, Bool.and_false, Bool.false_eq_true] at accepted
  | some fixed =>
      have atCell : cell.observed = pattern S record ∧ fixed = reference := by
        simpa only [Cell.accepts, decoded, Bool.and_eq_true_iff, decide_eq_true_eq] using accepted
      have bounded : cell.reference < S.assignmentEnumeration.length := by
        rcases List.getElem?_eq_some_iff.mp decoded with ⟨bounded, _⟩
        exact bounded
      have same : pattern S entry.model.observationalDist = cell.observed := observed.trans atCell.1.symm
      have generated := row_mem profiles entry listed cell.reference bounded
      have recovered : (⟨cell.observed, cell.reference⟩ : Cell) = cell := by cases cell; rfl
      rw [same, recovered] at generated
      exact generated

/-- Maximality concerns observable acceptance on represented patterns. It
does not claim to cover impossible patterns or arbitrary semantic proofs. -/
theorem compile_maximalAt (profiles : List (NativeTemplateInstance Q)) (demand : Demand S)
    (code : Code) (checked : check profiles demand code = true) (record : FiniteProbRecord S.Assignment)
    (represented : ∃ entry, entry ∈ profiles ∧ pattern S entry.model.observationalDist = pattern S record)
    (reference : S.Assignment) (accepted : accepts code record reference = true) :
    accepts (compile profiles demand) record reference = true := by
  rcases List.any_eq_true.mp accepted with ⟨cell, listed, atCell⟩
  have generated := row_mem_of_accepts profiles cell record represented reference atCell
  have passes := (List.all_eq_true.mp checked) cell listed
  exact List.any_eq_true.mpr ⟨cell, List.mem_filter.mpr ⟨generated, passes⟩, atCell⟩

theorem compile_soundAt (profiles : List (NativeTemplateInstance Q)) (demand : Demand S)
    (invariant : Invariant demand) (model : FiniteHiddenDAGSCM S P)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment)
    (accepted : accepts (compile profiles demand) model.observationalDist reference = true) :
    demand P model reference = true :=
  soundAt profiles demand invariant (compile profiles demand) (compile_checked profiles demand)
    model covered reference accepted

end NativeSupportGuard

namespace ProbabilityCode

variable {graph : ObservedGraph S} {profiles : List (NativeTemplateInstance Q)}

namespace CheckedNativeFormula

/-- Replace only the observable guard. The actual source, formula, checked
proof and action-free guarantee are retained without changing semantics. -/
def withCompiledGuard (checked : CheckedNativeFormula graph profiles) : CheckedNativeFormula graph profiles :=
  { checked with
    guard := NativeSupportGuard.compile profiles checked.proof.demand
    guardChecked := NativeSupportGuard.compile_checked profiles checked.proof.demand }

/-- Expose the unchanged fields without asking application elaboration to
unfold the generated guard or its potentially enormous profile catalogue. -/
theorem withCompiledGuard_source (checked : CheckedNativeFormula graph profiles) :
    checked.withCompiledGuard.source = checked.source := rfl

theorem withCompiledGuard_formula (checked : CheckedNativeFormula graph profiles) :
    checked.withCompiledGuard.formula = checked.formula := rfl

/-- Every already accepted cell remains accepted wherever this catalogue
covers the original model. Numerical source/formula values are unchanged. -/
theorem withCompiledGuard_available (checked : CheckedNativeFormula graph profiles)
    (model : FiniteHiddenDAGSCM S P)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment) (accepted : checked.available model.observationalDist reference = true) :
    checked.withCompiledGuard.available model.observationalDist reference = true := by
  have represented : ∃ entry, entry ∈ profiles ∧
      NativeSupportGuard.pattern S entry.model.observationalDist = NativeSupportGuard.pattern S model.observationalDist := by
    rcases covered with ⟨entry, listed, same⟩
    exact ⟨entry, listed, congrArg (fun support => S.assignmentEnumeration.map support) same.observational_support⟩
  exact Bool.and_eq_true_iff.mpr ⟨NativeSupportGuard.compile_maximalAt profiles checked.proof.demand
    checked.guard checked.guardChecked model.observationalDist represented reference (Bool.and_eq_true_iff.mp accepted).1,
    (Bool.and_eq_true_iff.mp accepted).2⟩

end CheckedNativeFormula

/-- Reuse the existing source/graph/action-free checker with an empty seed
guard, then replace that guard by the generated table. This enumerates rows
for one supplied proof, never proof trees or alternative formulas. -/
def NativeProofCode.compileGuardOn (graph : ObservedGraph S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (proof : NativeProofCode) : Option (CheckedNativeFormula graph profiles) :=
  ((⟨source, proof, []⟩ : NativeCertificateCode).checkOn graph profiles).map CheckedNativeFormula.withCompiledGuard

def NativeProofCode.compileGuardFixed (projection : FiniteLatentProjection S) (source : TermCode) (proof : NativeProofCode) :=
  proof.compileGuardOn projection.observedGraph projection.completeSupportCatalogue source

def NativeProofCode.compileGuardProjected (graph : ObservedGraph S) (source : TermCode) (proof : NativeProofCode) :=
  proof.compileGuardOn graph graph.cliqueRootProjection.completeSupportCatalogue source

end ProbabilityCode
end Thesis.Causality
