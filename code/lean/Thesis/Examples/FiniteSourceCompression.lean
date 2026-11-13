import Thesis.Probability.FiniteSourceCompression

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteSourceCompression

open Probability.FiniteSourceCompression

/-!
# A nonrectangular event survives source compression

The event uses both source and background, with source responses zero,
two thirds and one.  Its original probability is five ninths.  Compressing
the three positive source atoms to two preserves this event exactly and
keeps the source independent of the unchanged, nonuniform background.

Zero input atoms and a zero response slice are intentional.  An empty query
family additionally checks that normalization/independence do not require a
positive observed event or a nonempty list of requested probabilities.
-/

def source : FiniteProbRecord Nat := ⟨[(0, 0), (0, 1), (1, 1), (2, 1), (9, 0)], 3, by decide, rfl⟩
def background : FiniteProbRecord Bool := ⟨[(false, 1), (true, 2)], 3, by decide, rfl⟩
def event : Event (Nat × Bool) := fun pair =>
  if pair.1 = 0 then false else if pair.1 = 1 then pair.2 else true
def events : Fin 1 → Event (Nat × Bool) := fun _ => event
def replaced := compress source background events

theorem support_bound : replaced.factor.atoms.length ≤ 2 := replaced.bound
theorem event_preserved : QProb.Equiv ((replaced.factor.product background).probVal event)
    ((source.product background).probVal event) := replaced.preserved 0
theorem original_value : QProb.Equiv ((source.product background).probVal event) ⟨5, 9, by decide⟩ := by decide +kernel
theorem replaced_value : QProb.Equiv ((replaced.factor.product background).probVal event) ⟨5, 9, by decide⟩ :=
  QProb.equiv_trans event_preserved original_value
theorem computed_support : replaced.factor.atoms.length = 2 := by decide +kernel
theorem computed_value : QProb.Equiv ((replaced.factor.product background).probVal event) ⟨5, 9, by decide⟩ := by decide +kernel
theorem remains_independent (sourceEvent : Event Nat) (backgroundEvent : Event Bool) :
    QProb.Equiv ((replaced.factor.product background).probVal (fun pair => sourceEvent pair.1 && backgroundEvent pair.2))
      (QProb.mul (replaced.factor.probVal sourceEvent) (background.probVal backgroundEvent)) :=
  replaced.independent sourceEvent backgroundEvent

def noEvents : Fin 0 → Event (Nat × Bool) := fun index => Fin.elim0 index
def normalizedOnly := compress source background noEvents
theorem no_queries_single_atom : normalizedOnly.factor.atoms.length = 1 := by decide +kernel

end FiniteSourceCompression
end Examples
end Probability
end Thesis
