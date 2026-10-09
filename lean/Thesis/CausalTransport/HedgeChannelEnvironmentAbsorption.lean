import Thesis.CausalTransport.HedgeChannelEnvironmentRouting

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability PathSpecification HedgeChannelInstallation FiniteBooleanInteraction

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

/-!
# Absorb mandatory forest rows without duplicating an interaction row

An active-path interaction need not contain every Small vertex.  Additional
mandatory rows can be routed into its selected rows by a certified forest.
At a receiving interaction row, however, XORing two complete row phases
would delete its own observed bit.  That is not the phase of an installed
mechanism: its own bit must remain present exactly once.

The construction below combines only the incoming-parent masks at a selected
interaction row.  At a new forest row it uses the actual successor signal.
Reserved-root masks are retained only at original interaction rows.  Every
read remains behind the actual directed-edge or pair-root incidence guard.

The forest stops at interaction rows, and every forest sink is one of those
rows.  Whole-flow conservation then proves that the complete union's actual
phase is exactly the original interaction phase.  This permits arbitrary
Small/interaction overlap and merging forest branches; receiving rows are
not installed twice.  If the forest's outside-interaction bits are zero at
an actual direction, every new row is even and every original row retains
its phase at that direction.

These are proved installation and conservation operations, not an assertion
that every irreducible conditional terminal already has such an interaction
and absorbing forest.  The remaining graph construction must still supply
them, including the direction's behavior at unselected path forks.
-/

namespace LinearSignal

/-- Add forest inputs at an existing interaction row, retaining its own bit
once.  Elsewhere install only the actual forest inputs.  Combining parent
masks by XOR also handles an input already present in the original signal. -/
def absorbSuccessor (data : LinearSignal G) (interaction : NodeSet S) (successor : ForestChild S) : LinearSignal G where
  parentMask := fun child parent => if interaction child then
    Bool.xor (data.parentMask child parent) (decide (successor parent = some child))
    else decide (successor parent = some child)
  rootMask := fun child root => if interaction child then data.rootMask child root else false

/-- Outside the original interaction, this is literally the legal forest
row.  It has its own bit, not an independently XORed copy of that bit. -/
theorem absorbSuccessor_rowPhase_outside (data : LinearSignal G) (interaction : NodeSet S)
    (successor : ForestChild S) (child : Fin S.count) (outside : interaction child = false) (point : Cube G) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value point =
      ((ofSuccessor (G := G) successor).rowPhase child).value point := by
  simp only [rowPhase_value, absorbSuccessor, ofSuccessor, outside, Bool.false_eq_true, if_false]

/-- At an original row, the forest's incoming contribution is added but
its own-bit contribution is removed from that *addition*.  The original
installed row therefore still contains its own observed bit exactly once. -/
theorem absorbSuccessor_rowPhase_inside (data : LinearSignal G) (interaction : NodeSet S)
    (successor : ForestChild S) (child : Fin S.count) (inside : interaction child = true) (point : Cube G) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value point =
      Bool.xor ((data.rowPhase child).value point)
        (Bool.xor (((ofSuccessor (G := G) successor).rowPhase child).value point) (cubeSample G point child)) := by
  let originalParent := fun parent => if S.directed parent child = true then
    if data.parentMask child parent then cubeSample G point parent else false else false
  let forestParent := fun parent => if S.directed parent child = true then
    if decide (successor parent = some child) then cubeSample G point parent else false else false
  let roots := (List.finRange (pairRootCount G.binary)).foldl (fun total root => Bool.xor total
    (if pairRootIncident G.binary root child = true then
      if data.rootMask child root then cubeEnvironment G point root else false else false)) false
  have parents : (List.finRange S.count).foldl (fun total parent => Bool.xor total
      (if S.directed parent child = true then
        if Bool.xor (data.parentMask child parent) (decide (successor parent = some child)) then
          cubeSample G point parent else false else false)) false =
      Bool.xor ((List.finRange S.count).foldl (fun total parent => Bool.xor total (originalParent parent)) false)
        ((List.finRange S.count).foldl (fun total parent => Bool.xor total (forestParent parent)) false) := by
    calc
      _ = (List.finRange S.count).foldl (fun total parent => Bool.xor total
          (Bool.xor (originalParent parent) (forestParent parent))) false := by
        apply foldl_congr
        intro total parent
        apply congrArg (Bool.xor total)
        dsimp only [originalParent, forestParent]
        cases S.directed parent child <;> cases data.parentMask child parent <;>
          cases decide (successor parent = some child) <;> cases cubeSample G point parent <;> rfl
      _ = _ := foldl_xor_pointwise originalParent forestParent (List.finRange S.count)
  have forestRoots : (List.finRange (pairRootCount G.binary)).foldl (fun total root => Bool.xor total
      (if pairRootIncident G.binary root child = true then if false then cubeEnvironment G point root else false else false))
      false = false := by
    apply foldl_unchanged
    intro total root
    simp only [Bool.false_eq_true, if_false, ite_self, Bool.xor_false]
  simp only [rowPhase_value, absorbSuccessor, inside, if_true, ofSuccessor]
  rw [parents, forestRoots, Bool.xor_false]
  change Bool.xor (cubeSample G point child) (Bool.xor
    (Bool.xor ((List.finRange S.count).foldl (fun total parent => Bool.xor total (originalParent parent)) false)
      ((List.finRange S.count).foldl (fun total parent => Bool.xor total (forestParent parent)) false)) roots) =
    Bool.xor (Bool.xor (cubeSample G point child)
      (Bool.xor ((List.finRange S.count).foldl (fun total parent => Bool.xor total (originalParent parent)) false) roots))
      (Bool.xor (Bool.xor (cubeSample G point child)
        ((List.finRange S.count).foldl (fun total parent => Bool.xor total (forestParent parent)) false)) (cubeSample G point child))
  generalize cubeSample G point child = own
  generalize (List.finRange S.count).foldl (fun total parent => Bool.xor total (originalParent parent)) false = original
  generalize (List.finRange S.count).foldl (fun total parent => Bool.xor total (forestParent parent)) false = forest
  generalize roots = reserved
  cases own <;> cases original <;> cases forest <;> cases reserved <;> rfl

/-! ## Extending the certified domain does not invent an outgoing edge -/

/-- Include every interaction row in the forest domain.  Old off-domain
vertices have no successor, so the same map remains well formed on the union. -/
theorem successor_wellFormed_union (interaction domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) :
    childWellFormedBool (NodeSet.union interaction domain) successor = true := by
  apply List.all_eq_true.mpr
  intro parent member
  cases next : successor parent with
  | none => cases NodeSet.union interaction domain parent <;> rfl
  | some child =>
      have parts := childWellFormed_edge domain successor wellFormed next
      have parentIn : NodeSet.union interaction domain parent = true := NodeSet.subset_union_right _ _ parent parts.1
      have childIn : NodeSet.union interaction domain child = true := NodeSet.subset_union_right _ _ child parts.2.1
      simp only [parentIn, childIn, parts.2.2, Bool.and_self]

/-- The enlarged forest's sinks are exactly the receiving interaction rows.
The two premises are graph certificates: it stops there, and no old sink is
left elsewhere.  There is no premise about a likelihood or a parity gap. -/
theorem keptSinks_union_eq_interaction (interaction domain : NodeSet S) (successor : ForestChild S)
    (stops : forall child, interaction child = true -> successor child = none)
    (sinksInside : NodeSet.Subset (keptSinks domain successor) interaction) :
    keptSinks (NodeSet.union interaction domain) successor = interaction := by
  funext child
  cases selected : interaction child with
  | true =>
      exact (keptSinks_iff _ _ child).mpr ⟨NodeSet.subset_union_left _ _ child selected, stops child selected⟩
  | false =>
      cases sink : keptSinks (NodeSet.union interaction domain) successor child with
      | false => rfl
      | true =>
          have parts := (keptSinks_iff _ _ child).mp sink
          have oldIn : domain child = true := by
            simpa only [NodeSet.union, selected, Bool.false_or] using parts.1
          have oldSink := (keptSinks_iff domain successor child).mpr ⟨oldIn, parts.2⟩
          have impossible := sinksInside child oldSink
          rw [selected] at impossible
          cases impossible

/-! ## Conservation at arbitrary overlaps and merges -/

private theorem absorbSuccessor_interactionPhase (data : LinearSignal G) (interaction : NodeSet S)
    (successor : ForestChild S) (point : Cube G) :
    ((data.absorbSuccessor interaction successor).forestPhase interaction).value point =
      Bool.xor ((data.forestPhase interaction).value point)
        (Bool.xor (((ofSuccessor (G := G) successor).forestPhase interaction).value point)
          (hedgeNodeXor interaction (cubeSample G point))) := by
  rw [forestPhase_value, forestPhase_value, forestPhase_value]
  calc
    _ = (NodeSet.members interaction).foldl (fun total child => Bool.xor total
        (Bool.xor ((data.rowPhase child).value point)
          (Bool.xor (((ofSuccessor (G := G) successor).rowPhase child).value point) (cubeSample G point child)))) false := by
      apply foldl_congr_of_mem
      intro total child member
      exact congrArg (Bool.xor total)
        (data.absorbSuccessor_rowPhase_inside interaction successor child ((NodeSet.mem_members_iff _ _).mp member) point)
    _ = _ := by rw [foldl_xor_pointwise, foldl_xor_pointwise]; rfl

/-- The actual complete union phase is preserved exactly, at every cube
point.  Absorber own-bits cancel only in the proof-level correction term,
never by deleting the own-bit of a mechanism installed at an overlap. -/
theorem absorbSuccessor_forestPhase (data : LinearSignal G) (interaction domain : NodeSet S)
    (successor : ForestChild S) (wellFormed : childWellFormedBool domain successor = true)
    (stops : forall child, interaction child = true -> successor child = none)
    (sinksInside : NodeSet.Subset (keptSinks domain successor) interaction) (point : Cube G) :
    ((data.absorbSuccessor interaction successor).forestPhase (NodeSet.union interaction domain)).value point =
      (data.forestPhase interaction).value point := by
  let tails := NodeSet.diff domain interaction
  have split : NodeSet.union interaction tails = NodeSet.union interaction domain := by
    funext child
    change (interaction child || (domain child && Bool.not (interaction child))) = (interaction child || domain child)
    cases interaction child <;> cases domain child <;> rfl
  have disjoint : NodeSet.Disjoint interaction tails := NodeSet.disjoint_diff domain interaction
  have tailPhase : ((data.absorbSuccessor interaction successor).forestPhase tails).value point =
      ((ofSuccessor (G := G) successor).forestPhase tails).value point := by
    rw [forestPhase_value, forestPhase_value]
    apply foldl_congr_of_mem
    intro total child member
    have selected := (NodeSet.mem_members_iff tails child).mp member
    have outside : interaction child = false := by
      simpa only [tails, NodeSet.diff, Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp selected).2
    exact congrArg (Bool.xor total) (data.absorbSuccessor_rowPhase_outside interaction successor child outside point)
  have routed := ofSuccessor_forestPhase (G := G) (NodeSet.union interaction domain) successor
    (successor_wellFormed_union interaction domain successor wellFormed) point
  rw [keptSinks_union_eq_interaction interaction domain successor stops sinksInside] at routed
  have flowSplit := forestPhase_union_of_disjoint (ofSuccessor (G := G) successor) interaction tails disjoint point
  rw [split, routed] at flowSplit
  rw [← split, forestPhase_union_of_disjoint _ _ _ disjoint, absorbSuccessor_interactionPhase, tailPhase]
  generalize (data.forestPhase interaction).value point = original
  generalize ((ofSuccessor (G := G) successor).forestPhase interaction).value point = received at *
  generalize ((ofSuccessor (G := G) successor).forestPhase tails).value point = sent at *
  generalize hedgeNodeXor interaction (cubeSample G point) = own at *
  cases original <;> cases received <;> cases sent <;> cases own <;> cases flowSplit <;> rfl

/-! ## Retain the actual direction, including at receiving Small rows -/

private theorem absorbingIncoming_zero (interaction domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true)
    (stops : forall child, interaction child = true -> successor child = none)
    (point : Cube G)
    (tailsZero : forall parent, domain parent = true -> interaction parent = false -> cubeSample G point parent = false)
    (child : Fin S.count) : hedgeRoutingIncomingBits successor (cubeSample G point) child = false := by
  unfold hedgeRoutingIncomingBits hedgeRoutingParentEntry
  apply foldl_unchanged
  intro total parent
  by_cases next : successor parent = some child
  · have parts := childWellFormed_edge domain successor wellFormed next
    have outside : interaction parent = false := by
      cases selected : interaction parent with
      | false => rfl
      | true => have stopped := stops parent selected; rw [stopped] at next; cases next
    rw [if_pos next, tailsZero parent parts.1 outside, Bool.xor_false]
  · rw [if_neg next, Bool.xor_false]

/-- At every original interaction row the installed phase at this direction
is unchanged.  Forest transmitters are outside the receiving set and zero,
even if the receiving row itself has a nonzero observed or reserved bit. -/
theorem absorbSuccessor_rowPhase_direction_inside (data : LinearSignal G) (interaction domain : NodeSet S)
    (successor : ForestChild S) (wellFormed : childWellFormedBool domain successor = true)
    (stops : forall child, interaction child = true -> successor child = none)
    (point : Cube G)
    (tailsZero : forall parent, domain parent = true -> interaction parent = false -> cubeSample G point parent = false)
    (child : Fin S.count) (inside : interaction child = true) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value point = (data.rowPhase child).value point := by
  rw [absorbSuccessor_rowPhase_inside data interaction successor child inside point,
    ofSuccessor_rowPhase domain successor wellFormed]
  unfold hedgeRoutingLocalSource
  rw [absorbingIncoming_zero interaction domain successor wellFormed stops point tailsZero,
    Bool.xor_false, Bool.xor_self, Bool.xor_false]

/-- Every added forest row is even at the actual direction, including
merge rows with several incoming transmitters.  This is proved from the
tail bits and certified map, not supplied as a separate row-parity flag. -/
theorem absorbSuccessor_rowPhase_direction_outside (data : LinearSignal G) (interaction domain : NodeSet S)
    (successor : ForestChild S) (wellFormed : childWellFormedBool domain successor = true)
    (stops : forall child, interaction child = true -> successor child = none)
    (point : Cube G)
    (tailsZero : forall parent, domain parent = true -> interaction parent = false -> cubeSample G point parent = false)
    (child : Fin S.count) (inDomain : domain child = true) (outside : interaction child = false) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value point = false := by
  rw [absorbSuccessor_rowPhase_outside data interaction successor child outside point,
    ofSuccessor_rowPhase domain successor wellFormed]
  unfold hedgeRoutingLocalSource
  rw [tailsZero child inDomain outside, absorbingIncoming_zero interaction domain successor wellFormed stops point tailsZero]
  rfl

end LinearSignal

/-! ## Install all mandatory Small rows in the conserved interaction -/

/-- Extend a supplied conserved interaction to all mandatory Small rows.
The installed signal, row partition, new even rows and full Small-phase
oddness are constructed here.  The interaction's phase identity and original
even rows remain explicit graph-to-interaction obligations: this adapter
does not assume them as theorems of arbitrary irreducible terminals. -/
def ConditionalParityWitness.ofAbsorbedInteraction {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (data : LinearSignal G)
    (interaction domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true)
    (stops : forall child, interaction child = true -> successor child = none)
    (sinksInside : NodeSet.Subset (keptSinks domain successor) interaction)
    (containsSmall : NodeSet.Subset w.small (NodeSet.union interaction domain))
    (actionFree : forall child, NodeSet.union interaction domain child = true -> query.action child = false)
    (outcomeMask : Cube G)
    (outcomeMember : outcomeMask ∈ outcomeMasks (pairRootCount G.binary + S.count) (cubeMask G query.outcome))
    (direction : Cube G)
    (directionMember : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)))
    (outcomeOdd : (maskPhase _ outcomeMask).value direction = true)
    (interactionEven : forall child, interaction child = true -> w.small child = false ->
      (data.rowPhase child).value direction = false)
    (tailsZero : forall child, domain child = true -> interaction child = false -> cubeSample G direction child = false)
    (interactionMatches : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)) ->
      (data.forestPhase interaction).value point = (maskPhase _ outcomeMask).value point) :
    ConditionalParityWitness w (data.absorbSuccessor interaction successor) (data.absorbSuccessor interaction successor) := by
  let installed := data.absorbSuccessor interaction successor
  let selected := NodeSet.diff (NodeSet.union interaction domain) w.small
  have outsideSmall : forall child, selected child = true -> w.small child = false := by
    intro child chosen
    simpa only [selected, NodeSet.diff, Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp chosen).2
  have even : forall child, selected child = true -> (installed.rowPhase child).value direction = false := by
    intro child chosen
    cases inside : interaction child with
    | true =>
        rw [LinearSignal.absorbSuccessor_rowPhase_direction_inside data interaction domain successor wellFormed
          stops direction tailsZero child inside]
        exact interactionEven child inside (outsideSmall child chosen)
    | false =>
        have inDomain : domain child = true := by
          simpa only [NodeSet.union, inside, Bool.false_or] using (Bool.and_eq_true_iff.mp chosen).1
        exact data.absorbSuccessor_rowPhase_direction_outside interaction domain successor wellFormed stops
          direction tailsZero child inDomain inside
  have whole : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)) ->
      Bool.xor ((installed.forestPhase w.small).value point)
        ((selectedPhase _ S.count selected installed.rowPhase).value point) = (maskPhase _ outcomeMask).value point := by
    intro point member
    rw [LinearSignal.selectedPhase_value_eq_forestPhase,
      ← LinearSignal.forestPhase_union_of_disjoint installed w.small selected
        (NodeSet.disjoint_diff (NodeSet.union interaction domain) w.small), NodeSet.union_diff_eq containsSmall,
      LinearSignal.absorbSuccessor_forestPhase data interaction domain successor wellFormed stops sinksInside]
    exact interactionMatches point member
  have matching : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)) ->
      ((installed.forestPhase w.small).xor (maskPhase _ outcomeMask)).value point =
        (selectedPhase _ S.count selected installed.rowPhase).value point := by
    intro point member
    have conserved := whole point member
    change Bool.xor ((installed.forestPhase w.small).value point) ((maskPhase _ outcomeMask).value point) = _
    rw [← conserved]
    generalize (installed.forestPhase w.small).value point = smallBit
    generalize (selectedPhase _ S.count selected installed.rowPhase).value point = backgroundBit
    cases smallBit <;> cases backgroundBit <;> rfl
  have smallOdd : (installed.forestPhase w.small).value direction = true := by
    have conserved := whole direction directionMember
    rw [outcomeOdd, selectedPhase_value_eq_false_of_even _ _ selected installed.rowPhase direction even,
      Bool.xor_false] at conserved
    exact conserved
  exact {
    outcomeMask := outcomeMask
    outcomeMask_member := outcomeMember
    direction := direction
    direction_member := directionMember
    small_odd := smallOdd
    outcome_odd := outcomeOdd
    selected := selected
    selected_outside_small := outsideSmall
    selected_avoids_action := fun child chosen => actionFree child (Bool.and_eq_true_iff.mp chosen).1
    selected_even := even
    matching := matching
  }

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
