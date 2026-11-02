import Thesis.CausalTransport.NativeRewriteTraces
import Thesis.Examples.NativeRewriteOccurrences
import Thesis.Examples.NativeDemandPaths

namespace Thesis.Causality.Examples.NativeRewriteTraces

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Empty sources, literal finite loops and common-profile trace conversion

Empty traces retain both the real source and the requested mask. A supplied
code-driven occurrence and its reverse form an actual two-step loop, with
the middle tree retained literally. Only its first source is supplied as a
validity premise; the certified occurrence grammar propagates that validity.

Existing zero-weight and mixed-profile paths are converted by the general
theorems, without asking kernel reduction to normalize function-equality
transports. The final boundary excludes a trace from a supported unit source
to a demanded null conditional with the same coherent masks. This concerns
the local decoder/support boundary, not a general non-identifiability test.
There is no trace enumeration, reachability algorithm or execution pilot.
-/

def requested : Demand family := NativeRewriteOccurrences.requested
def outerRequested : Demand family := NativeRewriteOccurrences.outerRequested
def unitTree : Term family := Term.encode family unitTerm requested
def nullTree : Term family := Term.encode family (.kernel carrier) requested

theorem empty_source_and_mask_checks :
    (RewriteTrace.nil unitTree).check requested = true ∧
      (RewriteTrace.nil nullTree).check requested = false ∧
      (RewriteTrace.nil (Term.encode family unitTerm (fun _ _ => false))).check requested = false ∧
      (RewriteTrace.nil (Term.encode family (.kernel carrier) (fun _ _ => false))).check (fun _ _ => false) = true := by
  decide +kernel

theorem empty_vertex_is_retained : (RewriteTrace.nil nullTree).vertices = [nullTree] := rfl

theorem empty_path_conversion_keeps_refusal : (RewriteTrace.nil nullTree).toPath.check requested = false := by
  rw [RewriteTrace.toPath_check]
  decide +kernel

/-- These joins use the literal reversal endpoint equalities. They do not
compare statuses, probability values or erased kernels. -/
private def loop {profiles : List (NativeTemplateInstance projection)} (occurrence : RewriteOccurrence profiles) :
    RewriteTrace profiles occurrence.left occurrence.left :=
  .cons occurrence
    ((RewriteTrace.cons occurrence.reverse (.nil occurrence.reverse.right)).reindex
      occurrence.reverse_left occurrence.reverse_right)

def suppliedLoop := loop NativeRewriteOccurrences.suppliedOccurrence

theorem supplied_loop_checked : suppliedLoop.check outerRequested = true :=
  (RewriteTrace.check_iff_first suppliedLoop outerRequested).mpr
    (Bool.and_eq_true_iff.mp NativeRewriteOccurrences.supplied_source_checked)

theorem supplied_loop_vertices : suppliedLoop.vertices =
    [NativeRewriteOccurrences.suppliedOccurrence.left, NativeRewriteOccurrences.suppliedOccurrence.right,
      NativeRewriteOccurrences.suppliedOccurrence.left] := by
  simp only [suppliedLoop, loop, RewriteTrace.vertices, RewriteTrace.vertices_reindex,
    RewriteOccurrence.reverse_left, RewriteOccurrence.reverse_right]

theorem reconstructed_loop_checked : suppliedLoop.toPath.check outerRequested = true :=
  (suppliedLoop.toPath_check outerRequested).trans supplied_loop_checked

theorem reconstructed_loop_vertices : suppliedLoop.toPath.vertices = suppliedLoop.vertices :=
  suppliedLoop.toPath_vertices

theorem reconstructed_old_support_checked :
    checkDerivation family outerRequested suppliedLoop.toPath.erase.toDerivation = true :=
  suppliedLoop.erase_checked outerRequested supplied_loop_checked

def nestedTrace := RewriteTrace.ofPath NativeDemandPaths.encodedNested

theorem nested_zero_trace_checked : nestedTrace.check NativeDemandPaths.requested = true :=
  (RewriteTrace.ofPath_check _ _).trans NativeDemandPaths.nested_zero_path_checked

theorem nested_vertices_are_retained : nestedTrace.vertices = NativeDemandPaths.encodedNested.vertices :=
  RewriteTrace.ofPath_vertices _

def mixedTrace := RewriteTrace.ofPath NativeDemandPaths.encodedMixed

theorem one_trace_checks_both_profiles : mixedTrace.check NativeDemandPaths.mixedRequested = true :=
  (RewriteTrace.ofPath_check _ _).trans NativeDemandPaths.one_path_checks_both_profiles

theorem mixed_vertices_are_retained : mixedTrace.vertices = NativeDemandPaths.encodedMixed.vertices :=
  RewriteTrace.ofPath_vertices _

theorem mixed_reconstruction_checked : mixedTrace.toPath.check NativeDemandPaths.mixedRequested = true :=
  (mixedTrace.toPath_check _).trans one_trace_checks_both_profiles

def wrongOccurrence := RewriteOccurrence.ofStep NativeStepPreservation.wrongReference
def wrongTrace := RewriteTrace.cons wrongOccurrence (.nil wrongOccurrence.right)

theorem wrong_reference_trace_rejected : wrongTrace.check outerRequested = false := by
  rw [RewriteTrace.check_eq_first]
  exact NativeRewriteOccurrences.wrong_reference_stays_rejected

/-- The real unit source is supported, but the demanded target conditional
is undefined. Literal joins and local rule certificates cannot hide that gap. -/
theorem null_target_has_no_trace_from_supported_source :
    ¬ Nonempty (RewriteTrace family unitTree nullTree) := by
  rintro ⟨trace⟩
  have source : unitTree.checkAnnotations requested = true ∧ check family unitTree.erase requested = true := by decide +kernel
  have accepted := (trace.check_iff_first requested).mpr source
  have target := (trace.target_checks_of_check requested accepted).2
  have missing : check family nullTree.erase requested = false := by decide +kernel
  exact Bool.noConfusion (missing.symm.trans target)

end Thesis.Causality.Examples.NativeRewriteTraces
