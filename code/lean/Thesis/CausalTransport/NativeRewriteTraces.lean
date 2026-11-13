import Thesis.CausalTransport.NativeRewriteOccurrences
import Thesis.CausalTransport.NativeDemandPaths

namespace Thesis.Causality.NativeDemandEncoding

open Probability NativeDemandTyping

/-!
# Finite occurrence traces correspond to checked encoded paths

Every cons cell joins an occurrence's complete encoded target to the tail's
literal source. Status agreement, equivalent probabilities or erased kernel
metadata cannot replace that equality. The empty trace retains its source
term and checks both its annotations and native support at the explicit
outer demand. A nil trace therefore supplies no value for a null conditional.

Conversions traverse one supplied finite trace or path. Endpoint transports
use only the occurrence bridge's literal equalities. Vertex-list theorems
retain every intermediate tree, including the last vertex of an empty tail.
Reversal may move within each elementary proof as previously documented;
neither the original nested proof tree nor an external byte format is claimed
to round-trip. One common trace serves the entire supplied profile family.

The checker visits each occurrence source and the final vertex. Within this
already certified occurrence grammar, validity propagates from the initial
source through literal joins. This fact does not waive local primitive
certification or the full support checks on an arbitrary raw proof detour.
Empty demands remain unused applications, not new causal probability values.

These are finite proof witnesses and constructive conversions. There is no
search for a trace, AC quotient or normalization, graph-wide feasibility
procedure, universal formula coverage or stopping theorem.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace Path

variable {profiles : List (NativeTemplateInstance P)}

/-- The final vertex is retained by the nil constructor. -/
def vertices {first last : Term profiles} : Path profiles first last → List (Term profiles)
  | .nil term => [term]
  | .cons step tail => step.left :: tail.vertices

theorem vertices_reindex {first last source target : Term profiles} (path : Path profiles first last)
    (source_eq : first = source) (target_eq : last = target) :
    (path.reindex source_eq target_eq).vertices = path.vertices := by
  cases source_eq
  cases target_eq
  rfl

end Path

inductive RewriteTrace (profiles : List (NativeTemplateInstance P)) : Term profiles → Term profiles → Type where
  | nil (term : Term profiles) : RewriteTrace profiles term term
  | cons (occurrence : RewriteOccurrence profiles) {last : Term profiles}
      (tail : RewriteTrace profiles occurrence.right last) : RewriteTrace profiles occurrence.left last

namespace RewriteTrace

variable {profiles : List (NativeTemplateInstance P)}

def vertices {first last : Term profiles} : RewriteTrace profiles first last → List (Term profiles)
  | .nil term => [term]
  | .cons occurrence tail => occurrence.left :: tail.vertices

/-- Both scans are retained at every vertex, including an empty trace.
The occurrence's own finite rule certificate is part of its input data. -/
def check {first last : Term profiles} : RewriteTrace profiles first last → Demand profiles → Bool
  | .nil term, requested => term.checkAnnotations requested && NativeDemandTyping.check profiles term.erase requested
  | .cons occurrence tail, requested => occurrence.check requested && tail.check requested

/-- Reindex only by literal term equality. No metadata join or new
probability equation is introduced by these endpoint transports. -/
def reindex {first last source target : Term profiles} (trace : RewriteTrace profiles first last)
    (source_eq : first = source) (target_eq : last = target) : RewriteTrace profiles source target :=
  cast ((congrArg (fun term => RewriteTrace profiles term last) source_eq).trans
    (congrArg (RewriteTrace profiles source) target_eq)) trace

theorem check_reindex {first last source target : Term profiles} (trace : RewriteTrace profiles first last)
    (source_eq : first = source) (target_eq : last = target) (requested : Demand profiles) :
    (trace.reindex source_eq target_eq).check requested = trace.check requested := by
  cases source_eq
  cases target_eq
  rfl

theorem vertices_reindex {first last source target : Term profiles} (trace : RewriteTrace profiles first last)
    (source_eq : first = source) (target_eq : last = target) :
    (trace.reindex source_eq target_eq).vertices = trace.vertices := by
  cases source_eq
  cases target_eq
  rfl

/-- Primitive certificates and literal joins propagate validity; the
starting vertex still has to pass the application's actual outer demand. -/
theorem check_iff_first {first last : Term profiles} (trace : RewriteTrace profiles first last) (requested : Demand profiles) :
    trace.check requested = true ↔
      first.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles first.erase requested = true := by
  induction trace with
  | nil term => exact Bool.and_eq_true_iff
  | cons occurrence tail ih =>
      constructor
      · intro accepted
        exact Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1
      · intro source
        have headChecked := Bool.and_eq_true_iff.mpr source
        have next := occurrence.target_checks_of_check requested headChecked
        exact Bool.and_eq_true_iff.mpr ⟨headChecked, ih.mpr next⟩

theorem check_eq_first {first last : Term profiles} (trace : RewriteTrace profiles first last) (requested : Demand profiles) :
    trace.check requested = (first.checkAnnotations requested && NativeDemandTyping.check profiles first.erase requested) :=
  Bool.eq_iff_iff.mpr ((check_iff_first trace requested).trans Bool.and_eq_true_iff.symm)

theorem target_checks_of_check {first last : Term profiles} (trace : RewriteTrace profiles first last) (requested : Demand profiles)
    (accepted : trace.check requested = true) :
    last.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles last.erase requested = true := by
  induction trace with
  | nil term => exact Bool.and_eq_true_iff.mp accepted
  | cons occurrence tail ih => exact ih (Bool.and_eq_true_iff.mp accepted).2

/-- Reconstruct the actual elementary path. Each transport uses the
occurrence's full endpoint equality, never a status-table comparison. -/
def toPath {first last : Term profiles} : RewriteTrace profiles first last → Path profiles first last
  | .nil term => .nil term
  | .cons occurrence tail =>
      let endpoints := occurrence.toStep_endpoints
      let convertedTail := toPath tail
      (Path.cons occurrence.toStep (convertedTail.reindex endpoints.2.symm rfl)).reindex endpoints.1 rfl

theorem toPath_check {first last : Term profiles} (trace : RewriteTrace profiles first last) (requested : Demand profiles) :
    trace.toPath.check requested = trace.check requested := by
  induction trace with
  | nil term => rfl
  | cons occurrence tail ih =>
      simp only [toPath, Path.check_reindex, Path.check_cons, RewriteOccurrence.toStep_check, check, ih]

theorem toPath_vertices {first last : Term profiles} (trace : RewriteTrace profiles first last) :
    trace.toPath.vertices = trace.vertices := by
  induction trace with
  | nil term => rfl
  | cons occurrence tail ih =>
      simp only [toPath, Path.vertices_reindex, Path.vertices, (occurrence.toStep_endpoints).1, vertices, ih]

/-- Flatten every actual elementary step once. Its literal source and
target equalities are the only information used to join the converted tail. -/
def ofPath {first last : Term profiles} : Path profiles first last → RewriteTrace profiles first last
  | .nil term => .nil term
  | .cons step tail =>
      let occurrence := RewriteOccurrence.ofStep step
      let endpoints := RewriteOccurrence.ofStep_endpoints step
      let convertedTail := ofPath tail
      (RewriteTrace.cons occurrence (convertedTail.reindex endpoints.2.symm rfl)).reindex endpoints.1 rfl

theorem ofPath_check {first last : Term profiles} (path : Path profiles first last) (requested : Demand profiles) :
    (ofPath path).check requested = path.check requested := by
  induction path with
  | nil term => rfl
  | cons step tail ih =>
      simp only [ofPath, check_reindex, check, RewriteOccurrence.ofStep_check, ih, Path.check_cons]

theorem ofPath_vertices {first last : Term profiles} (path : Path profiles first last) :
    (ofPath path).vertices = path.vertices := by
  induction path with
  | nil term => rfl
  | cons step tail ih =>
      simp only [ofPath, vertices_reindex, vertices, (RewriteOccurrence.ofStep_endpoints step).1, Path.vertices, ih]

/-- Recover acceptance of the original full recursive support checker
from one checked finite trace on the common supplied profile family. -/
theorem erase_checked {first last : Term profiles} (trace : RewriteTrace profiles first last) (requested : Demand profiles)
    (accepted : trace.check requested = true) :
    checkDerivation profiles requested trace.toPath.erase.toDerivation = true :=
  trace.toPath.erase_checked requested ((trace.toPath_check requested).trans accepted)

end RewriteTrace
end Thesis.Causality.NativeDemandEncoding
