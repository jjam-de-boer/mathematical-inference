import Thesis.CausalTransport.HedgeChannelEnvironmentCoefficients
import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability FiniteBooleanInteraction

/-!
# Finite incidence transport on the actual installed cube

The local column theorems identify supported coordinate directions with two
selected receiving rows.  This module turns those actual columns into an
executable finite graph, and a successful bounded reachability test into a
direction whose only selected-row changes are its two endpoints.

An edge is not a proposed sparse matrix entry.  Its finite test inspects every
original selected row of the supplied signal at a literal original cube
basis.  It also checks that the coordinate fixes the complete conditioning
cylinder and leaves the supplied outcome character even.  Reserved roots
and observed coordinates share their unchanged original cube enumeration.

At each step two finite scans compute a continuing row and a realizing
coordinate.  The resulting basis directions are XORed along the walk.
Repeated rows or coordinates are permitted: the internal endpoint cancels
by Boolean algebra, so no choice of a simple path is necessary.  All search
data live in `Type`; propositional existence proofs are never selected into
data.  The zero-length route is included.

Finally an actual odd singleton starting direction can be combined with this
transport.  Only the reached row then remains odd.  In a conditional failure
application that row must be in Small, leaving every outside-Small selected
row even.  The graph theorem that the actual outcome component reaches Small
is still required: this construction consumes a true finite reachability
test and does not manufacture universal connectivity or countermodels.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

namespace LinearSignal

/-- Read the actual phase only at a selected row.  In particular an omitted
fork's raw own bit must not become an extra incidence in the finite graph. -/
def selectedRowValue (data : LinearSignal G) (selected : NodeSet S)
    (row : Fin S.count) (point : Cube G) : Bool :=
  if selected row then (data.rowPhase row).value point else false

/-- Guarding a literal two-row column preserves precisely its two entries
when both receiving rows are selected.  All other raw zero entries remain
zero; selection is not assumed for the entire observed signature. -/
theorem selectedRowValue_pair_of_rows (data : LinearSignal G) (selected : NodeSet S)
    (left right : Fin S.count) (point : Cube G)
    (leftSelected : selected left = true) (rightSelected : selected right = true)
    (column : forall row, (data.rowPhase row).value point =
      Bool.xor (decide (row = left)) (decide (row = right))) (row : Fin S.count) :
    data.selectedRowValue selected row point = Bool.xor (decide (row = left)) (decide (row = right)) := by
  unfold selectedRowValue
  rw [column row]
  cases chosen : selected row with
  | true => simp only [if_true]
  | false =>
      have notLeft : row ≠ left := by
        intro same
        subst row
        exact Bool.false_ne_true (chosen.symm.trans leftSelected)
      have notRight : row ≠ right := by
        intro same
        subst row
        exact Bool.false_ne_true (chosen.symm.trans rightSelected)
      simp only [Bool.false_eq_true, if_false, decide_eq_false notLeft, decide_eq_false notRight]
      rfl

/-- Test one original coordinate for a supported, outcome-even two-row
column.  The complete selected-row enumeration is checked, not just the
two desired endpoints or a previously supplied list of nonzero entries. -/
def pairCoordinateTest (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (left right : Fin S.count)
    (coordinate : Fin (pairRootCount G.binary + S.count)) : Bool :=
  !fixed coordinate && !outcome coordinate &&
    (NodeSet.enumerated S).all (fun row => decide
      (data.selectedRowValue selected row (basisAssignment _ coordinate) =
        Bool.xor (decide (row = left)) (decide (row = right))))

/-- A literal supported pair column is recognized by the finite test.
This interface lets graph-specific column proofs supply edges without
evaluating an opaque path-normalization or exponentially many cube points. -/
theorem pairCoordinateTest_of_column (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (left right : Fin S.count)
    (coordinate : Fin (pairRootCount G.binary + S.count))
    (free : fixed coordinate = false) (even : outcome coordinate = false)
    (column : forall row, data.selectedRowValue selected row (basisAssignment _ coordinate) =
      Bool.xor (decide (row = left)) (decide (row = right))) :
    data.pairCoordinateTest selected fixed outcome left right coordinate = true := by
  simp only [pairCoordinateTest, free, even, Bool.not_false, Bool.true_and]
  exact List.all_eq_true.mpr (fun row _listed => decide_eq_true (column row))

/-- Actual pair columns have no preferred direction.  Exchanging the
receiving endpoints does not change the coordinate test or its free and
outcome-even guards. -/
theorem pairCoordinateTest_swap (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (left right : Fin S.count)
    (coordinate : Fin (pairRootCount G.binary + S.count)) :
    data.pairCoordinateTest selected fixed outcome left right coordinate =
      data.pairCoordinateTest selected fixed outcome right left coordinate := by
  unfold pairCoordinateTest
  have tests : (fun row : Fin S.count => decide
      (data.selectedRowValue selected row (basisAssignment _ coordinate) =
        Bool.xor (decide (row = left)) (decide (row = right)))) =
      (fun row : Fin S.count => decide
      (data.selectedRowValue selected row (basisAssignment _ coordinate) =
        Bool.xor (decide (row = right)) (decide (row = left)))) := by
    funext row
    rw [Bool.xor_comm (decide (row = left)) (decide (row = right))]
  rw [tests]

private theorem pairCoordinateTest_spec (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (left right : Fin S.count)
    (coordinate : Fin (pairRootCount G.binary + S.count))
    (tested : data.pairCoordinateTest selected fixed outcome left right coordinate = true) :
    fixed coordinate = false ∧ outcome coordinate = false ∧
      forall row, data.selectedRowValue selected row (basisAssignment _ coordinate) =
        Bool.xor (decide (row = left)) (decide (row = right)) := by
  have parts := Bool.and_eq_true_iff.mp tested
  have masks := Bool.and_eq_true_iff.mp parts.1
  have free : fixed coordinate = false := by simpa only [Bool.not_eq_true'] using masks.1
  have even : outcome coordinate = false := by simpa only [Bool.not_eq_true'] using masks.2
  refine ⟨free, even, ?_⟩
  intro row
  exact of_decide_eq_true (List.all_eq_true.mp parts.2 row (NodeSet.mem_enumerated S row))

/-- The executable incidence graph on original selected rows.  Each edge
must have a genuinely free outcome-even original coordinate realizing its
entire guarded column.  Distinctness excludes the zero column as an edge. -/
def pairIncidence (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (left right : Fin S.count) : Bool :=
  selected left && selected right && !finBeq left right &&
    (List.finRange (pairRootCount G.binary + S.count)).any
      (data.pairCoordinateTest selected fixed outcome left right)

/-- The actual tested pair graph is symmetric, even though the causal
arrows which supplied its columns are directed.  Incidence walks may
therefore move toward a Small source against its genuine approach arrows. -/
theorem pairIncidence_swap (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (left right : Fin S.count) :
    data.pairIncidence selected fixed outcome left right =
      data.pairIncidence selected fixed outcome right left := by
  unfold pairIncidence
  have tests : data.pairCoordinateTest selected fixed outcome left right =
      data.pairCoordinateTest selected fixed outcome right left := by
    funext coordinate
    exact data.pairCoordinateTest_swap selected fixed outcome left right coordinate
  have same : finBeq left right = finBeq right left := by
    cases forward : finBeq left right <;> cases backward : finBeq right left
    · rfl
    · have equal := (finBeq_eq_true_iff right left).mp backward
      exact False.elim (Bool.false_ne_true (forward.symm.trans ((finBeq_eq_true_iff left right).mpr equal.symm)))
    · have equal := (finBeq_eq_true_iff left right).mp forward
      exact False.elim (Bool.false_ne_true (backward.symm.trans ((finBeq_eq_true_iff right left).mpr equal.symm)))
    · rfl
  rw [tests, same, Bool.and_comm (selected left) (selected right)]

/-- Reverse an incidence connection using its actual symmetric relation.
Only a propositional walk is transported; executable direction construction
still uses the independent successful finite scans in `ofReachability`. -/
theorem pairIncidence_reachable_swap (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) {source target : Fin S.count}
    (reachable : FiniteReachability.Reachable (data.pairIncidence selected fixed outcome) source target) :
    FiniteReachability.Reachable (data.pairIncidence selected fixed outcome) target source := by
  rcases reachable with ⟨length, ⟨walk⟩⟩
  apply FiniteReachability.Reachable.of_consecutive _ walk.nodes.reverse
    (by simpa only [List.head?_reverse] using walk.nodes_getLast)
    (by simpa only [List.getLast?_reverse] using walk.nodes_head)
  exact PathSpecification.Consecutive.reverse (fun left right edge =>
    (data.pairIncidence_swap selected fixed outcome right left).trans edge) _ walk.nodes_consecutive

/-- A literal consecutive incidence list connects its displayed source
to every listed row.  This proof-level adapter is shared by mandatory
approaches and merged activation traces; it selects no subpath into data. -/
theorem pairIncidence_reaches_member (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (nodes : List (Fin S.count)) (source : Fin S.count)
    (starts : nodes.head? = some source)
    (consecutive : PathSpecification.Consecutive
      (fun parent child => data.pairIncidence selected fixed outcome parent child = true) nodes)
    (target : Fin S.count) (member : target ∈ nodes) :
    FiniteReachability.Reachable (data.pairIncidence selected fixed outcome) source target := by
  induction nodes generalizing source with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      have same : head = source := Option.some.inj starts
      subst head
      rcases List.mem_cons.mp member with equal | later
      · subst target
        exact FiniteReachability.Reachable.refl _ source
      · cases tail with
        | nil => cases later
        | cons next rest =>
            exact FiniteReachability.Reachable.prepend consecutive.1
              (inductionHypothesis next rfl consecutive.2 later)

/-- Join proof-level actual incidence connections without choosing their
walks into a direction.  The final finite search independently computes the
route data after the joined connection has been constructively bounded. -/
theorem pairIncidence_reachable_trans (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) {source middle target : Fin S.count}
    (first : FiniteReachability.Reachable (data.pairIncidence selected fixed outcome) source middle)
    (second : FiniteReachability.Reachable (data.pairIncidence selected fixed outcome) middle target) :
    FiniteReachability.Reachable (data.pairIncidence selected fixed outcome) source target := by
  rcases first with ⟨firstLength, ⟨firstWalk⟩⟩
  rcases second with ⟨secondLength, ⟨secondWalk⟩⟩
  exact ⟨firstLength + secondLength, ⟨firstWalk.append secondWalk⟩⟩

/-- Every actual incidence connection fits the original observed finite
bound.  The existing constructive walk-shortening theorem supplies this
bound; no longer fuel or selected simple-path representative is assumed. -/
theorem pairIncidence_within_of_reachable (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) {source target : Fin S.count}
    (reachable : FiniteReachability.Reachable (data.pairIncidence selected fixed outcome) source target) :
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (data.pairIncidence selected fixed outcome) S.count source target = true := by
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
    (data.pairIncidence selected fixed outcome) finBeq_eq_true_iff (NodeSet.mem_enumerated S) reachable
  rw [NodeSet.length_enumerated] at bounded
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
    (data.pairIncidence selected fixed outcome) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded

/-- A proved actual pair column yields a real edge of the finite graph.
Its endpoints must both be selected and distinct; neither fact is inferred
from a guessed row coverage or ignored in the edge test. -/
theorem pairIncidence_of_column (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (left right : Fin S.count)
    (coordinate : Fin (pairRootCount G.binary + S.count))
    (leftSelected : selected left = true) (rightSelected : selected right = true)
    (different : left ≠ right) (free : fixed coordinate = false) (even : outcome coordinate = false)
    (column : forall row, data.selectedRowValue selected row (basisAssignment _ coordinate) =
      Bool.xor (decide (row = left)) (decide (row = right))) :
    data.pairIncidence selected fixed outcome left right = true := by
  have distinct : finBeq left right = false := Bool.eq_false_iff.mpr
    (fun same => different ((finBeq_eq_true_iff left right).mp same))
  simp only [pairIncidence, leftSelected, rightSelected, distinct, Bool.not_false, Bool.true_and]
  exact List.any_eq_true.mpr ⟨coordinate, List.mem_finRange coordinate,
    data.pairCoordinateTest_of_column selected fixed outcome left right coordinate free even column⟩

private theorem selectedRowValue_xor (data : LinearSignal G) (selected : NodeSet S)
    (row : Fin S.count) (first second : Cube G) :
    data.selectedRowValue selected row (FiniteProduct.xorAssignment _ first second) =
      Bool.xor (data.selectedRowValue selected row first) (data.selectedRowValue selected row second) := by
  cases chosen : selected row with
  | false => simp only [selectedRowValue, chosen, Bool.false_eq_true, if_false]; rfl
  | true => simp only [selectedRowValue, chosen, if_true]; exact (data.rowPhase row).xor_additive first second

private theorem cylinder_xor_closed (fixed first second : Cube G)
    (firstSupported : first ∈ FiniteProduct.falseCylinderEnumeration _ fixed)
    (secondSupported : second ∈ FiniteProduct.falseCylinderEnumeration _ fixed) :
    FiniteProduct.xorAssignment _ first second ∈ FiniteProduct.falseCylinderEnumeration _ fixed := by
  apply (FiniteProduct.falseCylinderEnumeration_member_iff _ fixed _).mpr
  intro coordinate chosen
  change Bool.xor (first coordinate) (second coordinate) = false
  rw [(FiniteProduct.falseCylinderEnumeration_member_iff _ fixed first).mp firstSupported coordinate chosen,
    (FiniteProduct.falseCylinderEnumeration_member_iff _ fixed second).mp secondSupported coordinate chosen]
  rfl

private theorem xor_pair_cancel (first middle last : Bool) :
    Bool.xor (Bool.xor first middle) (Bool.xor middle last) = Bool.xor first last := by
  cases first <;> cases middle <;> cases last <;> rfl

/-- A supported, outcome-even direction with exactly the displayed two
selected-row incidences.  This certificate describes the actual phases on
the original cube, rather than storing an independent proposed coefficient. -/
structure IncidenceTransport (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (source target : Fin S.count) where
  direction : Cube G
  supported : direction ∈ FiniteProduct.falseCylinderEnumeration _ fixed
  outcome_even : (maskPhase _ outcome).value direction = false
  rows_eq_pair : forall row, data.selectedRowValue selected row direction =
    Bool.xor (decide (row = source)) (decide (row = target))

namespace IncidenceTransport

/-- The zero direction realizes the empty route, including when no free
coordinate exists.  Its equal endpoint indicators cancel literally. -/
def refl (data : LinearSignal G) (selected : NodeSet S) (fixed outcome : Cube G)
    (source : Fin S.count) : IncidenceTransport data selected fixed outcome source source where
  direction := fun _ => false
  supported := (FiniteProduct.falseCylinderEnumeration_member_iff _ fixed _).mpr (fun _ _ => rfl)
  outcome_even := (maskPhase _ outcome).at_zero
  rows_eq_pair := by
    intro row
    cases chosen : selected row <;>
      simp only [selectedRowValue, chosen, Bool.false_eq_true, if_false, if_true,
        HomogeneousPhase.at_zero, Bool.xor_self]

/-- Select the first successful original coordinate by the finite scan.
The edge proof rules out search failure; it does not choose a witness from
a propositional existential.  The actual tested column supplies the rows. -/
def ofEdge (data : LinearSignal G) (selected : NodeSet S) (fixed outcome : Cube G)
    (source target : Fin S.count)
    (edge : data.pairIncidence selected fixed outcome source target = true) :
    IncidenceTransport data selected fixed outcome source target := by
  have found := (Bool.and_eq_true_iff.mp edge).2
  let coordinates := List.finRange (pairRootCount G.binary + S.count)
  let test := data.pairCoordinateTest selected fixed outcome source target
  let coordinate := listFirstAny coordinates test found
  have checked := data.pairCoordinateTest_spec selected fixed outcome source target coordinate
    (listFirstAny_pred coordinates test found)
  refine ⟨basisAssignment _ coordinate, (basisAssignment_member_iff _ fixed coordinate).mpr checked.1, ?_, checked.2.2⟩
  rw [maskPhase_basis]
  exact checked.2.1

/-- Concatenate actual transports by XOR.  The shared selected row cancels
even if the walk revisits other rows or reuses a reserved-root coordinate. -/
def trans {data : LinearSignal G} {selected : NodeSet S} {fixed outcome : Cube G}
    {source middle target : Fin S.count}
    (first : IncidenceTransport data selected fixed outcome source middle)
    (second : IncidenceTransport data selected fixed outcome middle target) :
    IncidenceTransport data selected fixed outcome source target where
  direction := FiniteProduct.xorAssignment _ first.direction second.direction
  supported := cylinder_xor_closed fixed first.direction second.direction first.supported second.supported
  outcome_even := by rw [(maskPhase _ outcome).xor_additive, first.outcome_even, second.outcome_even]; rfl
  rows_eq_pair := by
    intro row
    rw [selectedRowValue_xor, first.rows_eq_pair, second.rows_eq_pair]
    exact xor_pair_cancel _ _ _

/-- Construct the entire transport from actual bounded Boolean
reachability.  Both successor and coordinate selection are finite scans;
the recursive fuel decreases without unpacking an existential walk into
data.  No graph-specific connectivity assumption is proved here. -/
def ofReachability (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (target : Fin S.count) :
    (fuel : Nat) -> (source : Fin S.count) ->
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (data.pairIncidence selected fixed outcome) fuel source target = true ->
      IncidenceTransport data selected fixed outcome source target
  | 0, source, reachable => by
      have same : source = target := (finBeq_eq_true_iff source target).mp (by
        simpa only [FiniteReachability.within, FiniteReachability.closure,
          FiniteReachability.contains, List.any_cons, List.any_nil, Bool.or_false] using reachable)
      subst target
      exact refl data selected fixed outcome source
  | fuel + 1, source, reachable => by
      by_cases same : finBeq source target = true
      · have equal := (finBeq_eq_true_iff source target).mp same
        subst target
        exact refl data selected fixed outcome source
      · let nodes := NodeSet.enumerated S
        let edge := data.pairIncidence selected fixed outcome
        let continues := fun node => edge source node &&
          FiniteReachability.within finBeq nodes edge fuel node target
        have found : nodes.any continues = true := finiteWithin_successor_any
          finBeq nodes edge finBeq_eq_true_iff (NodeSet.mem_enumerated S) reachable (Bool.eq_false_iff.mpr same)
        let next := listFirstAny nodes continues found
        have parts := Bool.and_eq_true_iff.mp (listFirstAny_pred nodes continues found)
        exact (ofEdge data selected fixed outcome source next parts.1).trans
          (ofReachability data selected fixed outcome target fuel next parts.2)

end IncidenceTransport

/-- A supported odd-outcome direction with a single actual selected-row
incidence.  This is the final linear obligation before the existing positive
conditional interaction constructor, when its target is a Small row. -/
structure IncidenceReadoutDirection (data : LinearSignal G) (selected : NodeSet S)
    (fixed outcome : Cube G) (target : Fin S.count) where
  direction : Cube G
  supported : direction ∈ FiniteProduct.falseCylinderEnumeration _ fixed
  outcome_odd : (maskPhase _ outcome).value direction = true
  rows_eq_single : forall row, data.selectedRowValue selected row direction = decide (row = target)

/-- Cancel the true starting incidence with a constructed transport.  The
starting direction is checked on the same full cylinder and actual selected
rows.  Outcome oddness survives because every route edge was outcome-even. -/
def IncidenceTransport.finish {data : LinearSignal G} {selected : NodeSet S} {fixed outcome : Cube G}
    {source target : Fin S.count} (route : IncidenceTransport data selected fixed outcome source target)
    (start : Cube G) (supported : start ∈ FiniteProduct.falseCylinderEnumeration _ fixed)
    (odd : (maskPhase _ outcome).value start = true)
    (single : forall row, data.selectedRowValue selected row start = decide (row = source)) :
    IncidenceReadoutDirection data selected fixed outcome target where
  direction := FiniteProduct.xorAssignment _ start route.direction
  supported := cylinder_xor_closed fixed start route.direction supported route.supported
  outcome_odd := by rw [(maskPhase _ outcome).xor_additive, odd, route.outcome_even]; rfl
  rows_eq_single := by
    intro row
    rw [selectedRowValue_xor, single, route.rows_eq_pair]
    cases decide (row = source) <;> cases decide (row = target) <;> rfl

/-- Every other actually selected row is even in the finished direction.
No statement about an unselected raw own bit is smuggled into this result. -/
theorem IncidenceReadoutDirection.other_row_even {data : LinearSignal G} {selected : NodeSet S}
    {fixed outcome : Cube G} {target : Fin S.count}
    (readout : IncidenceReadoutDirection data selected fixed outcome target)
    (row : Fin S.count) (chosen : selected row = true) (different : row ≠ target) :
    (data.rowPhase row).value readout.direction = false := by
  have actual := readout.rows_eq_single row
  simpa only [selectedRowValue, chosen, if_true, decide_eq_false different] using actual

end LinearSignal
end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
