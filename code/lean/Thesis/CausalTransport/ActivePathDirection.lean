import Thesis.CausalTransport.ActivePathRootInputs

namespace Thesis
namespace Causality

universe u

open PathSpecification

/-!
# A conditioning-supported observed direction for an incoming active path

The direction sets the source and every internal observed collider to false,
every other observed path vertex to true, and every off-path vertex to false.
Its reserved inputs are installed separately in the signal layer.  The mask
uses the same actual collider scan as phase balance and activation selection.

Activity proves that this mask is zero on the supplied conditioning set:
a conditioned internal vertex must be a collider, while endpoints are open.
An actual incoming observed parent has a kept outgoing path arrow and hence
cannot be a collider.  If the first path arrow enters the source, that parent
cannot be the source either.  Consequently every actual incoming observed
input is true in this direction.  No parity, support or neighbour-readiness
flag is supplied by the caller; these are consequences of the stored path.
-/

variable {S : ObservedSignature.{u}}

namespace ActivePathInput

private instance : DecidableEq (SeparationNode S) := fun left right =>
  if same : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp same)
  else isFalse (fun equal => same ((SeparationNode.beq_eq_true_iff left right).mpr equal))

/-- The literal observed bits of the path direction.  The source is zero
even if it is added to the false conditioning cylinder later.  Actual path
colliders are zero, not assumed to have the same bit as their neighbours. -/
def nonColliderBits (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (source : Fin S.count) : NodeSet S :=
  fun child => nodes.any (fun node => SeparationNode.beq node (.observed child)) &&
    !(finBeq child source) && !(colliderRows graph m nodes child)

/-- The source coordinate is always false by construction. -/
theorem nonColliderBits_source (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (source : Fin S.count) :
    nonColliderBits graph m nodes source source = false := by
  unfold nonColliderBits
  have self : finBeq source source = true := (finBeq_eq_true_iff _ _).mpr rfl
  rw [self, Bool.not_true, Bool.and_false, Bool.false_and]

/-- Every listed observed non-source vertex has exactly the complement
of its actual collider bit.  This is the own-bit formula used in row parity. -/
theorem nonColliderBits_of_mem (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (source child : Fin S.count)
    (member : .observed child ∈ nodes) (different : child ≠ source) :
    nonColliderBits graph m nodes source child = !(colliderRows graph m nodes child) := by
  have listed := (any_beq_eq_true_iff nodes (.observed child)).mpr member
  have unequal : finBeq child source = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    exact different ((finBeq_eq_true_iff _ _).mp same)
  unfold nonColliderBits
  rw [listed, unequal, Bool.not_false, Bool.and_true, Bool.true_and]

/-- The other observed endpoint is true for distinct endpoints.  Endpoints
are not internal colliders, irrespective of the incident arrow direction. -/
theorem nonColliderBits_target {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target))
    (distinct : source ≠ target) : nonColliderBits graph m path.nodes source target = true := by
  rw [nonColliderBits_of_mem graph m path.nodes source target (List.mem_of_getLast? path.finishes) (Ne.symm distinct),
    colliderRows_target_false path]
  rfl

/-- A simple non-singleton observed-endpoint path has distinct endpoints.
The last vertex belongs to the nonempty tail, which cannot contain its
first vertex again.  Thus an incoming-path direction needs no extra
endpoint-distinction readiness premise beyond its actual first-pair shape. -/
theorem endpoints_ne_first_pair {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest) : source ≠ target := by
  have finishes := path.finishes
  rw [shape, List.getLast?_cons_cons] at finishes
  have member := List.mem_of_getLast? finishes
  have absent := (List.nodup_cons.mp (shape ▸ path.simple)).1
  intro equal
  exact absent (equal ▸ member)

/-- Every true observed direction bit occurs at an actual noncollider
path vertex different from the source.  The occurrence is not chosen data. -/
theorem nonColliderBits_eq_true_iff (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (source child : Fin S.count) :
    nonColliderBits graph m nodes source child = true ↔
      .observed child ∈ nodes ∧ child ≠ source ∧ colliderRows graph m nodes child = false := by
  unfold nonColliderBits
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff, any_beq_eq_true_iff,
    Bool.not_eq_true', Bool.not_eq_true']
  constructor
  · rintro ⟨⟨member, unequal⟩, colliderFalse⟩
    refine ⟨member, ?_, colliderFalse⟩
    intro equal
    subst child
    have self := (finBeq_eq_true_iff source source).mpr rfl
    exact Bool.false_ne_true (unequal.symm.trans self)
  · rintro ⟨member, different, colliderFalse⟩
    refine ⟨⟨member, ?_⟩, colliderFalse⟩
    apply Bool.eq_false_iff.mpr
    intro same
    exact different ((finBeq_eq_true_iff _ _).mp same)

/-- Activity forces this direction to vanish on every conditioned observed
coordinate.  Open endpoints cannot be conditioned; an internal conditioned
vertex cannot be the noncollider on which the direction is true. -/
theorem nonColliderBits_condition_false {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child : Fin S.count) (conditioned : given child = true) : nonColliderBits graph m path.nodes source child = false := by
  apply Bool.eq_false_iff.mpr
  intro positive
  have entries := (nonColliderBits_eq_true_iff graph m path.nodes source child).mp positive
  by_cases atTarget : child = target
  · subst child
    have openTarget : given target = false := path.target_open
    exact Bool.false_ne_true (openTarget.symm.trans conditioned)
  · rcases exists_internal_neighbors_of_mem path.starts path.finishes entries.1
      (fun same => entries.2.1 (SeparationNode.observed.inj same))
      (fun same => atTarget (SeparationNode.observed.inj same)) with
        ⟨before, previous, next, after, window⟩
    have active := InternalTriplesActive.triple_of_append before after previous (.observed child) next
      (window ▸ path.internal_active)
    rcases active with collider | openMiddle
    · have found := (colliderRows_eq_true_iff graph m child path.nodes).mpr
        ⟨before, after, previous, next, window, collider.1⟩
      exact Bool.false_ne_true (entries.2.2.symm.trans found)
    · have notConditioned : given child = false := openMiddle.2
      exact Bool.false_ne_true (notConditioned.symm.trans conditioned)

/-- An observed parent read by this path has a kept outgoing path arrow,
so it cannot be an internal path collider.  Strict DAG rank excludes the
opposite incoming arrow at either possible internal neighbour. -/
theorem incoming_observed_parent_not_collider {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (parent child : Fin S.count) (incoming : incomingEdge graph m path.nodes (.observed parent) child = true) :
    colliderRows graph m path.nodes parent = false := by
  apply Bool.eq_false_iff.mpr
  intro collider
  rcases (colliderRows_eq_true_iff graph m parent path.nodes).mp collider with
    ⟨before, after, previous, next, window, arrows⟩
  have entries := Bool.and_eq_true_iff.mp incoming
  have step : stepOnPath (.observed child) (.observed parent) path.nodes = true := by
    rw [stepOnPath_symm]
    exact entries.1
  rcases (stepOnPath_internal_window path.simple before after previous (.observed parent) next (.observed child) window).mp step
    with first | second
  · have reverse := first ▸ entries.2
    exact Nat.lt_asymm (graph.expandedMutilatedEdge_rank_lt m reverse)
      (graph.expandedMutilatedEdge_rank_lt m arrows.1)
  · have reverse := second ▸ entries.2
    exact Nat.lt_asymm (graph.expandedMutilatedEdge_rank_lt m reverse)
      (graph.expandedMutilatedEdge_rank_lt m arrows.2)

/-- When the first edge enters the source, no observed incoming path input
can be that source.  Simplicity fixes its only neighbour, and strict DAG
rank forbids the two opposite arrows.  This is the genuine back-door
orientation hypothesis, not an independently supplied parity Boolean. -/
theorem incoming_observed_parent_ne_source {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (parent child : Fin S.count) (incoming : incomingEdge graph m path.nodes (.observed parent) child = true) : parent ≠ source := by
  intro equal
  subst parent
  have entries := Bool.and_eq_true_iff.mp incoming
  have step : stepOnPath (.observed child) (.observed source) (.observed source :: first :: rest) = true := by
    rw [stepOnPath_symm]
    exact shape ▸ entries.1
  have childIsFirst := (stepOnPath_first_pair (.observed source) first (.observed child) rest (shape ▸ path.simple)).mp step
  have opposite : graph.expandedMutilatedEdge m (.observed source) first = true := childIsFirst ▸ entries.2
  exact Nat.lt_asymm (graph.expandedMutilatedEdge_rank_lt m opposite)
    (graph.expandedMutilatedEdge_rank_lt m firstIncoming)

/-- Every actual incoming observed input is true in the constructed
direction.  Its occurrence, noncollider status and source inequality are
all derived from the incoming path entry and first-edge orientation. -/
theorem nonColliderBits_incoming_parent {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (parent child : Fin S.count) (incoming : incomingEdge graph m path.nodes (.observed parent) child = true) :
    nonColliderBits graph m path.nodes source parent = true := by
  apply (nonColliderBits_eq_true_iff graph m path.nodes source parent).mpr
  exact ⟨(stepOnPath_members (Bool.and_eq_true_iff.mp incoming).1).1,
    incoming_observed_parent_ne_source path first rest shape firstIncoming parent child incoming,
    incoming_observed_parent_not_collider path parent child incoming⟩

end ActivePathInput

end Causality
end Thesis
