import Thesis.CausalTransport.ActivePathForkRouting

namespace Thesis
namespace Causality

open PathSpecification ActivePathInput

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}

/-!
# A fork exit cancels the source-side input, independently of vertex numbering

The routing candidate scan now preserves the actual active-path list order.
For an internal omitted observed vertex, simplicity allows only its preceding
and following neighbours to receive an outgoing path input.  Neither can occur
in the earlier prefix.  The first candidate which really receives the input
is therefore the preceding head, regardless of the two heads' DAG indices.

Absorption cancels that source-side read and leaves the following head's
original read.  When the omitted vertex is retained as a new mandatory-prefix
row, its observed column consequently connects its own row to the outcome-side
head, not to an arbitrarily numbered side.  The conditional incidence module
derives those exact installed column facts and proves that every actually
retained fork is internal; no fork-window or exit-orientation readiness field
is added to an irreducible terminal.

The theorem here concerns a displayed actual internal window.  Outgoing
endpoints remain supported by the general scan, but are not silently treated
as internal forks.  All candidate and exit data are finite executable scans;
window existentials are eliminated only in proofs.
-/

namespace PathSpecification.ActivePath

variable (path : ActivePath graph m given (.observed source) (.observed target))

/-- Both neighbours of an actual internal omitted vertex are genuine
outgoing observed inputs.  This helper accepts observed neighbours explicitly;
the conditional constructor separately proves their observed form. -/
theorem forkNodes_internal_inputs (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : path.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : path.forkNodes parent = true) :
    incomingEdge graph m path.nodes (.observed parent) previous = true ∧
      incomingEdge graph m path.nodes (.observed parent) next = true := by
  have previousStep : stepOnPath (.observed parent) (.observed previous) path.nodes = true := by
    rw [stepOnPath_symm]
    exact (stepOnPath_internal_window path.simple before after _ _ _ _ window).mpr (Or.inl rfl)
  have nextStep : stepOnPath (.observed parent) (.observed next) path.nodes = true := by
    rw [stepOnPath_symm]
    exact (stepOnPath_internal_window path.simple before after _ _ _ _ window).mpr (Or.inr rfl)
  exact ⟨Bool.and_eq_true_iff.mpr ⟨previousStep, path.forkNodes_outgoing_step parent _ fork previousStep⟩,
    Bool.and_eq_true_iff.mpr ⟨nextStep, path.forkNodes_outgoing_step parent _ fork nextStep⟩⟩

/-- The path-order scan returns the preceding head in every actual internal
fork window.  Earlier observed candidates are rejected by simplicity and the
proved two-neighbour classification, not by a topological index comparison. -/
theorem forkSuccessor_internal_window (distinct : source ≠ target) (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : path.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : path.forkNodes parent = true) : path.forkSuccessor distinct parent = some previous := by
  have inputs := path.forkNodes_internal_inputs parent previous next before after window fork
  have separated := (List.nodup_append.mp (window ▸ path.simple)).2.2
  have earlierEmpty : (observedNodes before).find?
      (fun child => incomingEdge graph m path.nodes (.observed parent) child) = none := by
    apply List.find?_eq_none.mpr
    intro child member read
    have onBefore := (mem_observedNodes_iff before child).mp member
    have step := (Bool.and_eq_true_iff.mp read).1
    rw [stepOnPath_symm] at step
    rcases (stepOnPath_internal_window path.simple before after _ _ _ _ window).mp step with previousEq | nextEq
    · exact separated _ onBefore _ (List.mem_cons.mpr (Or.inl rfl)) previousEq
    · exact separated _ onBefore _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))) nextEq
  apply path.forkSuccessor_of_find distinct fork
  have candidates : path.forkHeadCandidates = observedNodes before ++ previous :: parent :: next :: observedNodes after := by
    unfold forkHeadCandidates
    rw [window, observedNodes_append]
    rfl
  rw [candidates, List.find?_append, earlierEmpty, Option.none_or, List.find?_cons_of_pos inputs.1]

/-- The actual internal neighbours are distinct.  The proof extracts the
stored path's nodup contract rather than assuming separate receiver rows. -/
theorem fork_internal_neighbors_distinct (parent previous next : Fin S.count)
    (before after : List (SeparationNode S))
    (window : path.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after) : previous ≠ next := by
  have unique := (List.nodup_cons.mp (List.nodup_append.mp (window ▸ path.simple)).2.1).1
  intro same
  apply unique
  rw [same]
  exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))

/-- The raw fork-parent mask has exactly these two observed receivers.
Incoming heads, ambient extra arrows and signature numbering cannot add a
third path input to this actual internal column. -/
theorem forkNodes_internal_input_iff (parent previous next child : Fin S.count)
    (before after : List (SeparationNode S))
    (window : path.nodes = before ++ .observed previous :: .observed parent :: .observed next :: after)
    (fork : path.forkNodes parent = true) :
    incomingEdge graph m path.nodes (.observed parent) child = true ↔ child = previous ∨ child = next := by
  constructor
  · intro read
    have step := (Bool.and_eq_true_iff.mp read).1
    rw [stepOnPath_symm] at step
    rcases (stepOnPath_internal_window path.simple before after _ _ _ _ window).mp step with previousEq | nextEq
    · exact Or.inl (SeparationNode.observed.inj previousEq)
    · exact Or.inr (SeparationNode.observed.inj nextEq)
  · intro neighbor
    have inputs := path.forkNodes_internal_inputs parent previous next before after window fork
    rcases neighbor with same | same
    · exact same ▸ inputs.1
    · exact same ▸ inputs.2

end PathSpecification.ActivePath

end Causality
end Thesis
