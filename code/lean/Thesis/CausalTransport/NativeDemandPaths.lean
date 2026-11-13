import Thesis.CausalTransport.NativeDemandSteps

namespace Thesis.Causality.NativeDemandEncoding

open Probability NativeDemandTyping

/-!
# Typed finite paths retain literal joins and every demanded vertex

A cons cell joins the complete encoded target of its elementary step to the
source index of its tail. Equal status tables, equal rational values, or
equal erased kernel metadata cannot replace this literal term equality.
The independent step grammar still supplies every equation; a path adds
only finite composition, without an arbitrary old-language proof field.

Annotation and support scans both visit every vertex, including the sole
vertex of an empty path. The application supplies one outer demand for the
whole path and profile family. Support is not reduced to the two final
endpoints: an unavailable intermediate conditional still blocks a detour.
Within a step, the established frame rules retain their exact pulled-back
demands, including skipped support beneath a defined zero weight.

Erasure produces an actual old elementary path. Its vertex scan agrees
exactly with the old recursive support checker; annotation validation stays
explicit. The endpoint transports below use only literal equalities. These
are internal typed paths, not a serialized external decoder, an enumeration
of all paths, a normalization algorithm, or a universal stopping theorem.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

inductive Path (profiles : List (NativeTemplateInstance P)) : Term profiles → Term profiles → Type where
  | nil (term : Term profiles) : Path profiles term term
  | cons (step : Step profiles) {last : Term profiles} (tail : Path profiles step.right last) :
      Path profiles step.left last

namespace Path

variable {profiles : List (NativeTemplateInstance P)}

def erase {first last : Term profiles} : Path profiles first last → DoCalculusRewritePath P.observedGraph first.erase last.erase
  | .nil term => .nil term.erase
  | .cons step tail => .cons step.erase tail.erase

/-- Endpoint indices travel with the interpreted path, so exact round-trip
statements can compare the original proof data as well as its endpoints. -/
def eraseData {first last : Term profiles} (path : Path profiles first last) :
    (Σ source target : ProbabilityTerm S, DoCalculusRewritePath P.observedGraph source target) :=
  ⟨first.erase, last.erase, path.erase⟩

/-- Transport only literal endpoint equality. Finite demand tables can be
equal extensionally without being definitionally identical, so a transported
path need not normalize in `decide`. `check_reindex` certifies its checker
without any native-evaluation axiom or replacement of the equation. -/
def reindex {first last source target : Term profiles} (path : Path profiles first last)
    (source_eq : first = source) (target_eq : last = target) : Path profiles source target :=
  cast ((congrArg (fun term => Path profiles term last) source_eq).trans
    (congrArg (Path profiles source) target_eq)) path

theorem eraseData_reindex {first last source target : Term profiles} (path : Path profiles first last)
    (source_eq : first = source) (target_eq : last = target) :
    (path.reindex source_eq target_eq).eraseData = path.eraseData := by
  cases source_eq
  cases target_eq
  rfl

def checkAnnotations {first last : Term profiles} : Path profiles first last → Demand profiles → Bool
  | .nil term, requested => term.checkAnnotations requested
  | .cons step tail, requested => step.left.checkAnnotations requested && tail.checkAnnotations requested

def checkSupport {first last : Term profiles} : Path profiles first last → Demand profiles → Bool
  | .nil term, requested => NativeDemandTyping.check profiles term.erase requested
  | .cons step tail, requested => NativeDemandTyping.check profiles step.left.erase requested && tail.checkSupport requested

def check {first last : Term profiles} (path : Path profiles first last) (requested : Demand profiles) : Bool :=
  path.checkAnnotations requested && path.checkSupport requested

theorem check_reindex {first last source target : Term profiles} (path : Path profiles first last)
    (source_eq : first = source) (target_eq : last = target) (requested : Demand profiles) :
    (path.reindex source_eq target_eq).check requested = path.check requested := by
  cases source_eq
  cases target_eq
  rfl

/-- The original raw scan is aggregated over precisely the supplied cells,
without selecting a separate path for each model or reference. -/
def rawCheck (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles) : Bool :=
  allNeeded profiles requested (fun index reference => path.checkVertices (profiles.get index).model reference)

theorem rawCheck_eq_toDerivation (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles) :
    rawCheck profiles path requested = checkDerivation profiles requested path.toDerivation := by
  rw [checkDerivation_exact]
  simp only [rawCheck, DoCalculusRewritePath.checkVertices_eq_toDerivation]

theorem rawCheck_nil (profiles : List (NativeTemplateInstance P)) (term : ProbabilityTerm S) (requested : Demand profiles) :
    rawCheck profiles (.nil term) requested = NativeDemandTyping.check profiles term requested :=
  (NativeDemandTyping.check_exact ..).symm

theorem rawCheck_cons (profiles : List (NativeTemplateInstance P)) {first middle last : ProbabilityTerm S}
    (step : DoCalculusRewriteStep P.observedGraph first middle) (tail : DoCalculusRewritePath P.observedGraph middle last)
    (requested : Demand profiles) :
    rawCheck profiles (.cons step tail) requested = (NativeDemandTyping.check profiles first requested && rawCheck profiles tail requested) := by
  simp only [rawCheck, DoCalculusRewritePath.checkVertices, allNeeded_and, ← NativeDemandTyping.check_exact]

theorem rawCheck_first (profiles : List (NativeTemplateInstance P)) {first last : ProbabilityTerm S}
    (path : DoCalculusRewritePath P.observedGraph first last) (requested : Demand profiles)
    (accepted : rawCheck profiles path requested = true) : NativeDemandTyping.check profiles first requested = true := by
  cases path with
  | nil => exact (rawCheck_nil profiles _ requested).symm.trans accepted
  | cons step tail => exact (Bool.and_eq_true_iff.mp ((rawCheck_cons profiles step tail requested).symm.trans accepted)).1

theorem checkSupport_exact {first last : Term profiles} (path : Path profiles first last) (requested : Demand profiles) :
    path.checkSupport requested = rawCheck profiles path.erase requested := by
  induction path with
  | nil term => exact (rawCheck_nil profiles term.erase requested).symm
  | cons step tail ih => simp only [checkSupport, erase, rawCheck_cons, ih]

/-- Exact comparison with the complete recursive proof checker, retaining
annotation validation and every actual intermediate vertex. -/
theorem check_exact {first last : Term profiles} (path : Path profiles first last) (requested : Demand profiles) :
    path.check requested = (path.checkAnnotations requested && checkDerivation profiles requested path.erase.toDerivation) := by
  rw [check, checkSupport_exact, rawCheck_eq_toDerivation]

theorem erase_checked {first last : Term profiles} (path : Path profiles first last) (requested : Demand profiles)
    (accepted : path.check requested = true) : checkDerivation profiles requested path.erase.toDerivation = true :=
  (Bool.and_eq_true_iff.mp ((path.check_exact requested).symm.trans accepted)).2

/-- Literal joins let the tail provide the target vertex, even if it has
no steps. Thus every vertex is checked, rather than only every nonempty edge. -/
theorem check_first {first last : Term profiles} (path : Path profiles first last) (requested : Demand profiles)
    (accepted : path.check requested = true) :
    first.checkAnnotations requested = true ∧ NativeDemandTyping.check profiles first.erase requested = true := by
  have both := Bool.and_eq_true_iff.mp accepted
  cases path with
  | nil term => exact both
  | cons step tail => exact ⟨(Bool.and_eq_true_iff.mp both.1).1, (Bool.and_eq_true_iff.mp both.2).1⟩

theorem check_cons (step : Step profiles) {last : Term profiles} (tail : Path profiles step.right last) (requested : Demand profiles) :
    (Path.cons step tail).check requested = (step.check requested && tail.check requested) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    have both := Bool.and_eq_true_iff.mp accepted
    have annotations := Bool.and_eq_true_iff.mp both.1
    have support := Bool.and_eq_true_iff.mp both.2
    have tailChecked := Bool.and_eq_true_iff.mpr ⟨annotations.2, support.2⟩
    have middle := tail.check_first requested tailChecked
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨annotations.1, middle.1⟩,
        Bool.and_eq_true_iff.mpr ⟨support.1, middle.2⟩⟩, tailChecked⟩
  · intro accepted
    have both := Bool.and_eq_true_iff.mp accepted
    have edge := Bool.and_eq_true_iff.mp both.1
    have tailChecked := Bool.and_eq_true_iff.mp both.2
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp edge.1).1, tailChecked.1⟩,
        Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp edge.2).1, tailChecked.2⟩⟩

end Path
end Thesis.Causality.NativeDemandEncoding
