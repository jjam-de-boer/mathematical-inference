import Thesis.Probability.FiniteBooleanInteraction
import Thesis.Probability.FiniteBooleanBlocks

namespace Thesis
namespace Probability
namespace FiniteBooleanInteraction

open FiniteProduct

/-!
# Canonical coordinate tests for actual homogeneous Boolean phases

The conditional interaction criterion requires equality of two actual phases
on an entire false-valued conditioning cylinder.  Checking that identity by
enumerating every assignment would hide the graph conservation argument and
can be needlessly expensive.  Homogeneity gives a smaller exact criterion:
the two phases must agree on each *free* coordinate direction.

The directions below are explicit singleton assignments, not a basis selected
from an existence theorem.  Coordinate induction proves that their values
determine every supported phase value.  Fixed coordinates contribute nothing,
and the empty and fully fixed cubes are included.  The theorem retains actual
phase functions and their supplied zero/additivity proofs; it does not replace
nonlinear signals by a proposed linear representation.

For graph applications this turns whole-cylinder matching into finite local
coefficient checks.  It does not prove that an arbitrary active path supplies
matching masks, an odd direction, or a positive interaction selection.  Those
remain the graph-facing construction obligations.
-/

/-- The explicit direction which toggles exactly one supplied coordinate.
Finite coordinate equality makes this data constructive for every dimension. -/
def basisAssignment (count : Nat) (coordinate : Fin count) : Fin count -> Bool :=
  fun index => decide (index = coordinate)

/-- The designated coordinate of its own direction is true. -/
theorem basisAssignment_self (count : Nat) (coordinate : Fin count) :
    basisAssignment count coordinate coordinate = true := by
  simp only [basisAssignment, decide_true]

/-- Every other coordinate of the explicit direction is false. -/
theorem basisAssignment_eq_false_of_ne (count : Nat) (coordinate index : Fin count)
    (different : index ≠ coordinate) : basisAssignment count coordinate index = false := by
  simp only [basisAssignment, different, decide_false]

/-- A coordinate direction belongs to a false cylinder exactly when that
coordinate is free.  No other coordinate or supported assignment is removed. -/
theorem basisAssignment_member_iff (count : Nat) (fixed : Fin count -> Bool) (coordinate : Fin count) :
    basisAssignment count coordinate ∈ falseCylinderEnumeration count fixed ↔ fixed coordinate = false := by
  rw [falseCylinderEnumeration_member_iff]
  constructor
  · intro consistent
    cases selected : fixed coordinate with
    | false => rfl
    | true =>
        have impossible := consistent coordinate selected
        rw [basisAssignment_self] at impossible
        cases impossible
  · intro free index selected
    by_cases same : index = coordinate
    · subst index
      exact False.elim (Bool.false_ne_true (free.symm.trans selected))
    · exact basisAssignment_eq_false_of_ne count coordinate index same

/-! ## Directions at the actual two-block coordinate embeddings -/

/-- A first-block direction reads as exactly that local first-block basis
assignment.  Proof fields of the finite embeddings do not change its bit. -/
theorem leftBlock_basis_left (left right : Nat) (coordinate : Fin left) :
    BooleanBlocks.leftBlock left right (basisAssignment (left + right) (coordinate.castAdd right)) =
      basisAssignment left coordinate := by
  funext index
  change decide (index.castAdd right = coordinate.castAdd right) = decide (index = coordinate)
  have same : index.castAdd right = coordinate.castAdd right ↔ index = coordinate :=
    ⟨fun equal => Fin.ext (congrArg (fun embedded : Fin (left + right) => embedded.val) equal),
      fun equal => congrArg (fun index => index.castAdd right) equal⟩
  simp only [same]

/-- A first-block direction is zero at every second-block coordinate.
The proof uses their disjoint numeric offsets, not an independence premise. -/
theorem rightBlock_basis_left (left right : Nat) (coordinate : Fin left) :
    BooleanBlocks.rightBlock left right (basisAssignment (left + right) (coordinate.castAdd right)) = (fun _ => false) := by
  funext index
  apply basisAssignment_eq_false_of_ne
  intro equal
  have values := congrArg Fin.val equal
  change left + index.val = coordinate.val at values
  have bound := coordinate.isLt
  omega

/-- A second-block direction is zero at every first-block coordinate,
including when one of the actual blocks has no coordinates. -/
theorem leftBlock_basis_right (left right : Nat) (coordinate : Fin right) :
    BooleanBlocks.leftBlock left right (basisAssignment (left + right) (Fin.natAdd left coordinate)) = (fun _ => false) := by
  funext index
  apply basisAssignment_eq_false_of_ne
  intro equal
  have values := congrArg Fin.val equal
  change index.val = left + coordinate.val at values
  have bound := index.isLt
  omega

/-- The actual offset read of a second-block direction restores exactly
its local basis assignment, retaining the first block's literal size. -/
theorem rightBlock_basis_right (left right : Nat) (coordinate : Fin right) :
    BooleanBlocks.rightBlock left right (basisAssignment (left + right) (Fin.natAdd left coordinate)) =
      basisAssignment right coordinate := by
  funext index
  change decide (Fin.natAdd left index = Fin.natAdd left coordinate) = decide (index = coordinate)
  have same : Fin.natAdd left index = Fin.natAdd left coordinate ↔ index = coordinate := by
    constructor
    · intro equal
      apply Fin.ext
      have values := congrArg Fin.val equal
      change left + index.val = left + coordinate.val at values
      omega
    · intro equal
      exact congrArg (Fin.natAdd left) equal
  simp only [same]

/-- A first-block basis direction is the explicit join of its local
direction and a zero second block.  No inverse is selected from existence. -/
theorem basisAssignment_eq_join_left (left right : Nat) (coordinate : Fin left) :
    basisAssignment (left + right) (coordinate.castAdd right) =
      BooleanBlocks.join left right (basisAssignment left coordinate) (fun _ => false) := by
  have rebuilt := (BooleanBlocks.join_split left right
    (basisAssignment (left + right) (coordinate.castAdd right))).symm
  rw [leftBlock_basis_left, rightBlock_basis_left] at rebuilt
  exact rebuilt

/-- A second-block direction joins a zero first block with its unchanged
local basis.  This connects local observed tests to full-cube coefficients. -/
theorem basisAssignment_eq_join_right (left right : Nat) (coordinate : Fin right) :
    basisAssignment (left + right) (Fin.natAdd left coordinate) =
      BooleanBlocks.join left right (fun _ => false) (basisAssignment right coordinate) := by
  have rebuilt := (BooleanBlocks.join_split left right
    (basisAssignment (left + right) (Fin.natAdd left coordinate))).symm
  rw [leftBlock_basis_right, rightBlock_basis_right] at rebuilt
  exact rebuilt

/-! ## Symbolic coordinate induction for homogeneous phases -/

private theorem extend_zero (count : Nat) :
    extend (Value := fun _ : Fin (count + 1) => Bool) false (fun _ => false) = (fun _ => false) := by
  funext index
  refine snocCases (motive := fun index =>
    extend (Value := fun _ : Fin (count + 1) => Bool) false (fun _ => false) index = false)
    ?_ (fun earlier => ?_) index
  · exact extend_last _ _
  · exact extend_castSucc _ _ earlier

private theorem extend_xor (count : Nat) (left right : Fin count -> Bool) :
    extend (Value := fun _ : Fin (count + 1) => Bool) false (xorAssignment count left right) =
      xorAssignment (count + 1) (extend false left) (extend false right) := by
  funext index
  refine snocCases (motive := fun index =>
    extend (Value := fun _ : Fin (count + 1) => Bool) false (xorAssignment count left right) index =
      xorAssignment (count + 1) (extend false left) (extend false right) index)
    ?_ (fun earlier => ?_) index
  · simp only [extend_last, xorAssignment]; rfl
  · simp only [extend_castSucc, xorAssignment]

private theorem extend_basis (count : Nat) (coordinate : Fin count) :
    extend (Value := fun _ : Fin (count + 1) => Bool) false (basisAssignment count coordinate) =
      basisAssignment (count + 1) coordinate.castSucc := by
  funext index
  refine snocCases (motive := fun index =>
    extend (Value := fun _ : Fin (count + 1) => Bool) false (basisAssignment count coordinate) index =
      basisAssignment (count + 1) coordinate.castSucc index)
    ?_ (fun earlier => ?_) index
  · change extend (Value := fun _ : Fin (count + 1) => Bool) false (basisAssignment count coordinate) (Fin.last count) = _
    rw [extend_last]
    exact (basisAssignment_eq_false_of_ne (count + 1) coordinate.castSucc (Fin.last count)
      (fun same => castSucc_ne_last coordinate same.symm)).symm
  · simp only [extend_castSucc, basisAssignment, Fin.castSucc_inj]

namespace HomogeneousPhase

/-- Restrict the actual phase by fixing its final coordinate to false.
Its homogeneity is inherited by an explicit extension, not assumed afresh. -/
def initial {count : Nat} (phase : HomogeneousPhase (count + 1)) : HomogeneousPhase count where
  value := fun sample => phase.value (extend false sample)
  at_zero := by rw [extend_zero]; exact phase.at_zero
  xor_additive := by
    intro left right
    rw [extend_xor]
    exact phase.xor_additive _ _

private theorem value_split {count : Nat} (phase : HomogeneousPhase (count + 1)) (sample : Fin (count + 1) -> Bool) :
    phase.value sample = Bool.xor (phase.initial.value (fun index => sample index.castSucc))
      (if sample (Fin.last count) then phase.value (basisAssignment (count + 1) (Fin.last count)) else false) := by
  cases lastBit : sample (Fin.last count) with
  | false =>
      have rebuilt : sample = extend false (fun index => sample index.castSucc) := by
        funext index
        refine snocCases (motive := fun index => sample index =
          extend (Value := fun _ : Fin (count + 1) => Bool) false (fun earlier => sample earlier.castSucc) index)
          ?_ (fun earlier => ?_) index
        · change sample (Fin.last count) =
            extend (Value := fun _ : Fin (count + 1) => Bool) false (fun earlier => sample earlier.castSucc) (Fin.last count)
          rw [extend_last, lastBit]
        · change sample earlier.castSucc =
            extend (Value := fun _ : Fin (count + 1) => Bool) false (fun earlier => sample earlier.castSucc) earlier.castSucc
          exact (extend_castSucc (Value := fun _ : Fin (count + 1) => Bool) false
            (fun index => sample index.castSucc) earlier).symm
      simp only [Bool.false_eq_true, if_false, Bool.xor_false, initial]
      rw [← rebuilt]
  | true =>
      have rebuilt : sample = xorAssignment (count + 1)
          (extend false (fun index => sample index.castSucc)) (basisAssignment (count + 1) (Fin.last count)) := by
        funext index
        refine snocCases (motive := fun index => sample index = xorAssignment (count + 1)
          (extend false (fun earlier => sample earlier.castSucc)) (basisAssignment (count + 1) (Fin.last count)) index)
          ?_ (fun earlier => ?_) index
        · simp only [xorAssignment, extend_last, basisAssignment_self, lastBit]; rfl
        · change sample earlier.castSucc = Bool.xor
            (extend (Value := fun _ : Fin (count + 1) => Bool) false (fun index => sample index.castSucc) earlier.castSucc)
            (basisAssignment (count + 1) (Fin.last count) earlier.castSucc)
          rw [extend_castSucc,
            basisAssignment_eq_false_of_ne (count + 1) (Fin.last count) earlier.castSucc (castSucc_ne_last earlier),
            Bool.xor_false]
      simp only [if_true, initial]
      exact (congrArg phase.value rebuilt).trans (phase.xor_additive _ _)

/-- Values on free coordinate directions determine the actual phase at
every assignment satisfying the original fixed-coordinate constraints.
This is a symbolic dimension induction; it never enumerates a concrete cube. -/
theorem value_eq_of_basis {count : Nat} (left right : HomogeneousPhase count) (fixed : Fin count -> Bool)
    (basis_agrees : forall coordinate, fixed coordinate = false ->
      left.value (basisAssignment count coordinate) = right.value (basisAssignment count coordinate))
    (sample : Fin count -> Bool) (consistent : forall coordinate, fixed coordinate = true -> sample coordinate = false) :
    left.value sample = right.value sample := by
  induction count with
  | zero =>
      have zero : sample = (fun _ => false) := funext (fun index => Fin.elim0 index)
      rw [zero, left.at_zero, right.at_zero]
  | succ count inductionHypothesis =>
      have earlierBasis : forall coordinate : Fin count, fixed coordinate.castSucc = false ->
          left.initial.value (basisAssignment count coordinate) = right.initial.value (basisAssignment count coordinate) := by
        intro coordinate free
        change left.value (extend false (basisAssignment count coordinate)) =
          right.value (extend false (basisAssignment count coordinate))
        rw [extend_basis]
        exact basis_agrees coordinate.castSucc free
      have earlierConsistent : forall coordinate : Fin count, fixed coordinate.castSucc = true ->
          sample coordinate.castSucc = false := fun coordinate selected => consistent coordinate.castSucc selected
      have earlier := inductionHypothesis left.initial right.initial (fun coordinate => fixed coordinate.castSucc)
        earlierBasis (fun coordinate => sample coordinate.castSucc) earlierConsistent
      rw [value_split left, value_split right, earlier]
      cases lastBit : sample (Fin.last count) with
      | false => rfl
      | true =>
          have free : fixed (Fin.last count) = false := by
            cases selected : fixed (Fin.last count) with
            | false => rfl
            | true =>
                have impossible := consistent (Fin.last count) selected
                rw [lastBit] at impossible
                cases impossible
          rw [basis_agrees (Fin.last count) free]

/-- Equality on every free direction is equivalent to equality on the
complete literal false-cylinder support.  The reverse implication checks
the explicit supported directions, so both sides concern the same functions. -/
theorem agree_on_falseCylinder_iff_basis {count : Nat} (left right : HomogeneousPhase count) (fixed : Fin count -> Bool) :
    (forall sample, sample ∈ falseCylinderEnumeration count fixed -> left.value sample = right.value sample) ↔
      (forall coordinate, fixed coordinate = false ->
        left.value (basisAssignment count coordinate) = right.value (basisAssignment count coordinate)) := by
  constructor
  · intro agreement coordinate free
    exact agreement _ ((basisAssignment_member_iff count fixed coordinate).mpr free)
  · intro agreement sample listed
    exact value_eq_of_basis left right fixed agreement sample
      ((falseCylinderEnumeration_member_iff count fixed sample).mp listed)

end HomogeneousPhase

private theorem singleton_xor_fold {α : Type} [DecidableEq α] (coordinate : α) (bit : Bool)
    (values : List α) (distinct : values.Nodup) (seed : Bool) :
    values.foldl (fun total index => if index = coordinate then Bool.xor total bit else total) seed =
      if coordinate ∈ values then Bool.xor seed bit else seed := by
  induction values generalizing seed with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, if_false]
  | cons head tail inductionHypothesis =>
      have tailDistinct := (List.nodup_cons.mp distinct).2
      by_cases atHead : head = coordinate
      · subst head
        have absent := (List.nodup_cons.mp distinct).1
        rw [List.foldl_cons, if_pos rfl, inductionHypothesis tailDistinct, if_neg absent,
          if_pos List.mem_cons_self]
      · have different : coordinate ≠ head := Ne.symm atHead
        rw [List.foldl_cons, if_neg atHead, inductionHypothesis tailDistinct]
        simp only [List.mem_cons, different, false_or]

-- Keep the small finite-list fact in this probability layer: using causal
-- fold utilities here would reverse the library's dependency direction.
private theorem basis_finRange_nodup (count : Nat) : (List.finRange count).Nodup := by
  induction count with
  | zero => rw [List.finRange_zero]; exact List.nodup_nil
  | succ count inductionHypothesis =>
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_map.mp member with ⟨index, _listed, equal⟩
        exact Fin.succ_ne_zero index equal
      · exact List.Pairwise.map Fin.succ
          (fun first second different equal => different (Fin.ext (Nat.succ.inj (congrArg Fin.val equal)))) inductionHypothesis

/-- A masked XOR of one explicit basis direction is exactly the mask at
that coordinate.  Each finite index occurs once, and the empty dimension is
handled by the coordinate's empty type; no causal lemma is imported here. -/
theorem basisAssignment_masked_foldl (count : Nat) (coordinate : Fin count) (mask : Fin count -> Bool) :
    (List.finRange count).foldl (fun total index => Bool.xor total
      (if mask index then basisAssignment count coordinate index else false)) false = mask coordinate := by
  have same : (fun total index => Bool.xor total (if mask index then basisAssignment count coordinate index else false)) =
      (fun total index => if index = coordinate then Bool.xor total (mask coordinate) else total) := by
    funext total index
    by_cases atCoordinate : index = coordinate
    · subst index
      rw [basisAssignment_self, if_pos rfl]
      cases mask coordinate <;> rfl
    · rw [basisAssignment_eq_false_of_ne count coordinate index atCoordinate, if_neg atCoordinate]
      simp only [ite_self, Bool.xor_false]
  rw [same, singleton_xor_fold coordinate (mask coordinate) (List.finRange count) (basis_finRange_nodup count),
    if_pos (List.mem_finRange coordinate), Bool.false_xor]

/-- The terminal-coordinate interaction selection is exactly its ascending
finite XOR fold.  Every omitted phase contributes false and every selected
phase occurs once; no assignment support or integer product is enumerated. -/
theorem selectedPhase_value_eq_foldl (count factors : Nat) (selected : Fin factors -> Bool)
    (phases : Fin factors -> HomogeneousPhase count) (sample : Fin count -> Bool) :
    (selectedPhase count factors selected phases).value sample =
      (List.finRange factors).foldl (fun total index => Bool.xor total
        (if selected index then (phases index).value sample else false)) false := by
  induction factors with
  | zero => rfl
  | succ factors inductionHypothesis =>
      rw [selectedPhase, List.finRange_succ_last]
      simp only [HomogeneousPhase.xor, List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil]
      rw [inductionHypothesis (fun index => selected index.castSucc) (fun index => phases index.castSucc)]
      cases selected (Fin.last factors) <;> rfl

/-- A selected interaction phase is even at a supplied direction when
each selected actual row is even there.  This finite fold identity supplies
the combined parity used by the strict covariance witness. -/
theorem selectedPhase_value_eq_false_of_even (count factors : Nat) (selected : Fin factors -> Bool)
    (phases : Fin factors -> HomogeneousPhase count) (sample : Fin count -> Bool)
    (even : forall index, selected index = true -> (phases index).value sample = false) :
    (selectedPhase count factors selected phases).value sample = false := by
  induction factors with
  | zero => rfl
  | succ factors inductionHypothesis =>
      change Bool.xor ((selectedPhase count factors (fun index => selected index.castSucc)
        (fun index => phases index.castSucc)).value sample)
        ((if selected (Fin.last factors) then phases (Fin.last factors) else HomogeneousPhase.unit count).value sample) = false
      rw [inductionHypothesis (fun index => selected index.castSucc) (fun index => phases index.castSucc)
        (fun index chosen => even index.castSucc chosen), Bool.false_xor]
      cases chosen : selected (Fin.last factors) with
      | false => simp only [Bool.false_eq_true, if_false, HomogeneousPhase.unit]
      | true => simp only [if_true]; exact even (Fin.last factors) chosen

end FiniteBooleanInteraction
end Probability
end Thesis
