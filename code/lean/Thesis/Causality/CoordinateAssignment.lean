import Thesis.Causality.SelectedAssignment
import Thesis.Causality.Identification
import Thesis.Probability.FiniteProductConditionals

namespace Thesis
namespace Causality

open Probability

/-!
# Compact dependent coordinates for a selected observed assignment

`ObservedSignature.SelectedAssignment` gives canonical full assignments off
a selected set.  The complementary presentation here uses one coordinate
per member of that set, in its already supplied finite topological order.
It is useful for full-coordinate conditional comparison: omitted observed
nodes must not become impossible extra cells of the selected product space.

Both presentations are explicit.  Restriction reads the listed nodes;
extension looks up a selected node in that very list and retains a supplied
background elsewhere.  Lookup correctness follows from finite decidable
membership and the list's proved duplicate-freeness.  No representative or
index is chosen from a propositional existence statement.  Empty selections
and different finite value types at different nodes are retained.
-/

namespace NodeSet

variable {S : ObservedSignature}

-- Keep list lookup on the supplied decidable finite equality.  The generic
-- ordered-type route to `EquivBEq` can import classical order infrastructure;
-- this local instance proves only the three literal equality laws needed by
-- lookup, and does not change instance selection in importing modules.
local instance nodeEquivBEq : EquivBEq (Fin S.count) where
  rfl := beq_iff_eq.mpr rfl
  symm := fun equal => beq_iff_eq.mpr (beq_iff_eq.mp equal).symm
  trans := fun first second => beq_iff_eq.mpr ((beq_iff_eq.mp first).trans (beq_iff_eq.mp second))

abbrev CoordinateValue (nodes : NodeSet S) (index : Fin nodes.members.length) : Type _ :=
  S.Value (nodes.members.get index)

abbrev CoordinateAssignment (nodes : NodeSet S) :=
  FiniteProduct.Assignment nodes.members.length (CoordinateValue nodes)

instance coordinateValuesDecidableEq (nodes : NodeSet S) :
    (index : Fin nodes.members.length) -> DecidableEq (CoordinateValue nodes index) :=
  fun index => S.valueDecidableEq (nodes.members.get index)

instance coordinateAssignmentDecidableEq (nodes : NodeSet S) : DecidableEq (CoordinateAssignment nodes) :=
  FiniteProduct.assignmentDecidableEq nodes.members.length (CoordinateValue nodes)
    (coordinateValuesDecidableEq nodes)

/-- Read exactly the enumerated selected coordinates; all old latent and
observed data remain in their own spaces until this explicit relabelling. -/
def selectCoordinates (nodes : NodeSet S) (assignment : S.Assignment) : CoordinateAssignment nodes :=
  fun index => assignment (nodes.members.get index)

private theorem get_idxOf_eq (nodes : NodeSet S) (node : Fin S.count) (member : node ∈ nodes.members) :
    nodes.members.get ⟨nodes.members.idxOf node, List.idxOf_lt_length_of_mem member⟩ = node := by
  apply beq_iff_eq.mp
  change (nodes.members.get ⟨nodes.members.idxOf node, List.idxOf_lt_length_of_mem member⟩ == node) = true
  simpa only [List.get_eq_getElem, List.idxOf] using
    (List.findIdx_getElem (p := fun value => value == node) (xs := nodes.members)
      (w := List.idxOf_lt_length_of_mem member))

/-- Extend the literal selected values while retaining the supplied reference
off the set.  In intervention arguments the background carries the original
action values, which must not change while conditioning values are scanned. -/
def extendCoordinates (nodes : NodeSet S) (values : CoordinateAssignment nodes)
    (reference : S.Assignment) : S.Assignment :=
  fun node => if member : node ∈ nodes.members then
    cast (congrArg S.Value (get_idxOf_eq nodes node member))
      (values ⟨nodes.members.idxOf node, List.idxOf_lt_length_of_mem member⟩)
  else reference node

/-- The explicit lookup of any listed coordinate recovers its supplied value. -/
theorem extendCoordinates_get (nodes : NodeSet S) (values : CoordinateAssignment nodes)
    (reference : S.Assignment) (index : Fin nodes.members.length) :
    extendCoordinates nodes values reference (nodes.members.get index) = values index := by
  unfold extendCoordinates
  rw [dif_pos (List.get_mem nodes.members index)]
  have lookup :
      (⟨nodes.members.idxOf (nodes.members.get index),
        List.idxOf_lt_length_of_mem (List.get_mem nodes.members index)⟩ : Fin nodes.members.length) = index :=
    Fin.ext (idxOf_get_of_nodup nodes.members (nodup_members nodes) index)
  have transport (other : Fin nodes.members.length) (same : other = index)
      (equalTypes : CoordinateValue nodes other = CoordinateValue nodes index) :
      cast equalTypes (values other) = values index := by
    cases same
    rfl
  exact transport _ lookup _

theorem extendCoordinates_of_false (nodes : NodeSet S) (values : CoordinateAssignment nodes)
    (reference : S.Assignment) (node : Fin S.count) (away : nodes node = false) :
    extendCoordinates nodes values reference node = reference node := by
  have missing : node ∉ nodes.members := by
    intro member
    have selected := (mem_members_iff nodes node).mp member
    rw [away] at selected
    cases selected
  exact dif_neg missing

/-- Restricting after extending is an exact function equality.  The discarded
background does not enter any of the selected coordinate values. -/
theorem selectCoordinates_extend (nodes : NodeSet S) (values : CoordinateAssignment nodes)
    (reference : S.Assignment) :
    selectCoordinates nodes (extendCoordinates nodes values reference) = values := by
  funext index
  exact extendCoordinates_get nodes values reference index

/-- Extension of an already restricted assignment agrees on every selected
node, even when its off-set background is different. -/
theorem extendCoordinates_select_of_true (nodes : NodeSet S) (assignment reference : S.Assignment)
    (node : Fin S.count) (selected : nodes node = true) :
    extendCoordinates nodes (selectCoordinates nodes assignment) reference node = assignment node := by
  have member := (mem_members_iff nodes node).mpr selected
  let index : Fin nodes.members.length := ⟨nodes.members.idxOf node, List.idxOf_lt_length_of_mem member⟩
  have same : nodes.members.get index = node := get_idxOf_eq nodes node member
  have recovered := extendCoordinates_get nodes (selectCoordinates nodes assignment) reference index
  change extendCoordinates nodes (selectCoordinates nodes assignment) reference (nodes.members.get index) =
    assignment (nodes.members.get index) at recovered
  rw [same] at recovered
  exact recovered

/-- A singleton of the compact coordinates is exactly the ordinary observed
agreement cylinder.  This connects finite probability cells to actual SCM
events, rather than merely comparing cardinalities of two presentations. -/
theorem singleton_selectCoordinates (nodes : NodeSet S) (reference sample : S.Assignment) :
    FiniteProbRecord.singletonEvent (selectCoordinates nodes reference) (selectCoordinates nodes sample) =
      Kernel.agreesOn nodes reference sample := by
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteProbRecord.singletonEvent, decide_eq_true_eq, Kernel.agreesOn, finAll_eq_true_iff]
  constructor
  · intro equal node
    cases selected : nodes node with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
        simp only [if_true]
        have member := (mem_members_iff nodes node).mpr selected
        let index : Fin nodes.members.length := ⟨nodes.members.idxOf node, List.idxOf_lt_length_of_mem member⟩
        have same : nodes.members.get index = node := get_idxOf_eq nodes node member
        have atNode := congrFun equal index
        change sample (nodes.members.get index) = reference (nodes.members.get index) at atNode
        rw [same] at atNode
        exact decide_eq_true atNode
  · intro same
    funext index
    have atNode := same (nodes.members.get index)
    have selected := (mem_members_iff nodes _).mp (List.get_mem nodes.members index)
    simpa only [selected, if_true, decide_eq_true_eq] using atNode

/-- Complete, duplicate-free coordinates computed directly from the selected
alphabets.  Unlike a full observed enumeration, its size does not multiply
by the alphabets of nodes outside the selection. -/
def coordinateAssignmentEnumeration (nodes : NodeSet S) : List (CoordinateAssignment nodes) :=
  deduplicate (FiniteProduct.enumeration nodes.members.length (CoordinateValue nodes)
    (fun index => S.valueEnumeration (nodes.members.get index)))

theorem coordinateAssignmentEnumeration_complete (nodes : NodeSet S) (values : CoordinateAssignment nodes) :
    values ∈ coordinateAssignmentEnumeration nodes := by
  rw [coordinateAssignmentEnumeration, mem_deduplicate]
  exact FiniteProduct.enumeration_complete nodes.members.length (CoordinateValue nodes)
    (fun index => S.valueEnumeration (nodes.members.get index))
    (fun index value => S.value_complete (nodes.members.get index) value) values

theorem coordinateAssignmentEnumeration_nodup (nodes : NodeSet S) :
    (coordinateAssignmentEnumeration nodes).Nodup := deduplicate_nodup _

/-! ## Coordinate conditionals are actual observed cylinders -/

/-- Omitting one compact coordinate is exactly omitting its observed node
from the selected cylinder.  Both directions use the supplied list lookup,
not a chosen inverse of the restriction map. -/
theorem context_selectCoordinates (nodes : NodeSet S) (pivot : Fin nodes.members.length)
    (reference sample : S.Assignment) :
    FiniteProductConditionals.context pivot (selectCoordinates nodes reference) (selectCoordinates nodes sample) =
      Kernel.agreesOn (diff nodes (singleton (nodes.members.get pivot))) reference sample := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro agreed
    apply (finAll_eq_true_iff _).mpr
    intro node
    cases selected : (diff nodes (singleton (nodes.members.get pivot))) node with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
        simp only [if_true]
        have parts := Bool.and_eq_true_iff.mp selected
        have member := (mem_members_iff nodes node).mpr parts.1
        have notPivot : node ≠ nodes.members.get pivot := by
          intro same
          have hit : (singleton (nodes.members.get pivot)) node = true := decide_eq_true same
          rw [hit] at parts
          cases parts.2
        let index : Fin nodes.members.length := ⟨nodes.members.idxOf node, List.idxOf_lt_length_of_mem member⟩
        have lookup : nodes.members.get index = node := get_idxOf_eq nodes node member
        have different : index ≠ pivot := by
          intro same
          apply notPivot
          exact lookup.symm.trans (congrArg (fun i => nodes.members.get i) same)
        have atNode := (finAll_eq_true_iff _).mp agreed index
        have equal : sample (nodes.members.get index) = reference (nodes.members.get index) := by
          simpa only [different, if_false, selectCoordinates, decide_eq_true_eq] using atNode
        rw [lookup] at equal
        exact decide_eq_true equal
  · intro agreed
    apply (finAll_eq_true_iff _).mpr
    intro index
    by_cases same : index = pivot
    · simp only [same, if_true]
    · simp only [same, if_false]
      have nodeDifferent : nodes.members.get index ≠ nodes.members.get pivot := by
        intro equal
        have lookup := congrArg (fun node => nodes.members.idxOf node) equal
        change nodes.members.idxOf (nodes.members.get index) = nodes.members.idxOf (nodes.members.get pivot) at lookup
        rw [idxOf_get_of_nodup nodes.members (nodup_members nodes) index,
          idxOf_get_of_nodup nodes.members (nodup_members nodes) pivot] at lookup
        exact same (Fin.ext lookup)
      have inNodes := (mem_members_iff nodes _).mp (List.get_mem nodes.members index)
      have selected : (diff nodes (singleton (nodes.members.get pivot))) (nodes.members.get index) = true := by
        simp only [diff, singleton, inNodes, nodeDifferent, decide_false, Bool.not_false, Bool.true_and]
      have atNode := (finAll_eq_true_iff _).mp agreed (nodes.members.get index)
      simpa only [selected, if_true] using atNode

/-- The observed context used by a compact coordinate conditional is
supported in the same original record. -/
theorem coordinateContext_positive (nodes : NodeSet S) (record : FiniteProbRecord S.Assignment)
    (supported : FiniteProductConditionals.FullSupport (record.map (selectCoordinates nodes)))
    (pivot : Fin nodes.members.length) (reference : S.Assignment) :
    record.EventPositive (Kernel.agreesOn (diff nodes (singleton (nodes.members.get pivot))) reference) := by
  have positive := FiniteProductConditionals.context_positive (record.map (selectCoordinates nodes)) supported
    pivot (selectCoordinates nodes reference)
  change 0 < FiniteProbRecord.eventMass (record.map (selectCoordinates nodes)).atoms _ at positive
  rw [FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] at positive
  have same := FiniteProbRecord.eventMass_congr record.atoms _ _ (context_selectCoordinates nodes pivot reference)
  exact Nat.lt_of_lt_of_eq positive same

/-- The finite product conditional is exactly the original record's
coordinate-label probability given the other selected observed coordinates.
This equality retains the actual denominator of that very source record. -/
theorem conditionalAt_probVal (nodes : NodeSet S) (record : FiniteProbRecord S.Assignment)
    (supported : FiniteProductConditionals.FullSupport (record.map (selectCoordinates nodes)))
    (pivot : Fin nodes.members.length) (reference : S.Assignment) :
    QProb.Equiv
      (FiniteProductConditionals.conditionalAt (record.map (selectCoordinates nodes)) supported
        pivot (selectCoordinates nodes reference))
      ((record.conditionOn (Kernel.agreesOn (diff nodes (singleton (nodes.members.get pivot))) reference)
        (coordinateContext_positive nodes record supported pivot reference)).probVal
          (fun sample => decide (sample (nodes.members.get pivot) = reference (nodes.members.get pivot)))) := by
  have sameContext :
      (fun sample => FiniteProductConditionals.context pivot (selectCoordinates nodes reference) (selectCoordinates nodes sample)) =
        Kernel.agreesOn (diff nodes (singleton (nodes.members.get pivot))) reference := by
    funext sample
    exact context_selectCoordinates nodes pivot reference sample
  have sameJoint :
      (fun sample => FiniteProductConditionals.context pivot (selectCoordinates nodes reference) (selectCoordinates nodes sample) &&
        FiniteProductConditionals.coordinateEvent pivot (selectCoordinates nodes reference) (selectCoordinates nodes sample)) =
      (fun sample => Kernel.agreesOn (diff nodes (singleton (nodes.members.get pivot))) reference sample &&
        decide (sample (nodes.members.get pivot) = reference (nodes.members.get pivot))) := by
    funext sample
    rw [context_selectCoordinates]
    rfl
  simp only [FiniteProductConditionals.conditionalAt, FiniteProbRecord.conditionOn, FiniteProbRecord.map,
    FiniteProbRecord.probVal, FiniteProbRecord.eventMass_filter_event, FiniteProbRecord.eventMass_map_labels, QProb.Equiv]
  rw [sameContext, sameJoint]

end NodeSet

namespace FiniteLatentSCM

variable {S : ObservedSignature}

/-- The selected finite coordinate law of the model's real intervention. -/
def interventionalCoordinateLaw (model : ExactModel S)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (nodes : NodeSet S) :
    FiniteProbRecord nodes.CoordinateAssignment :=
  (model.interventionalDist intervention).map (nodes.selectCoordinates)

/-- Strict observational positivity supplies every cell of an action-free
selected coordinate law at a fixed intervention reference.  The proof keeps
the original action values in the extension before applying SCM consistency;
it does not falsely demand positivity of complete intervened assignments. -/
theorem interventionalCoordinateLaw_fullSupport (model : ExactModel S)
    (positive : ObservationallyPositive model) (action nodes : NodeSet S)
    (disjoint : NodeSet.Disjoint action nodes) (reference : S.Assignment) :
    FiniteProductConditionals.FullSupport
      (model.interventionalCoordinateLaw ((Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference) nodes) := by
  intro values
  let extended := nodes.extendCoordinates values reference
  let target := (Kernel.mk NodeSet.empty action NodeSet.empty).intervention reference
  have probability := QProb.equiv_trans ((model.interventionalDist target).map_probVal (nodes.selectCoordinates)
    (FiniteProbRecord.singletonEvent values))
    ((model.interventionalDist target).probVal_congr _ (Kernel.agreesOn nodes extended) (fun sample => by
      have same := NodeSet.singleton_selectCoordinates nodes extended sample
      rw [NodeSet.selectCoordinates_extend] at same
      exact same))
  apply (QProb.equiv_num_pos_iff probability).mpr
  apply positive.interventional_cylinder_positive
  intro node value fixed
  cases selected : action node with
  | false => simp only [target, Kernel.intervention, selected, Bool.false_eq_true, if_false] at fixed; cases fixed
  | true =>
      have equal : reference node = value := by
        simpa only [target, Kernel.intervention, selected, if_true, Option.some.injEq] using fixed
      exact (nodes.extendCoordinates_of_false values reference node (disjoint node selected)).trans equal

end FiniteLatentSCM
end Causality
end Thesis
