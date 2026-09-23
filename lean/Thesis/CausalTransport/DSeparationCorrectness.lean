import Thesis.CausalTransport.DSeparation

namespace Thesis
namespace Causality

/-!
Constructive correctness lemmas for the finite graph searches used by
`ObservedGraph.dSeparated`.  This file begins with the representation and
enumeration facts needed by both directed ancestry and moral reachability.
-/

namespace FiniteReachability

/-- A directed walk using exactly the displayed number of edges. -/
inductive ExactWalk (edge : α -> α -> Bool) : Nat -> α -> α -> Type
  | refl (node) : ExactWalk edge 0 node node
  | step {length source middle target} :
      edge source middle = true ->
      ExactWalk edge length middle target ->
      ExactWalk edge (length + 1) source target

/-- A directed walk using at most `fuel` edges. -/
def BoundedWalk (edge : α -> α -> Bool) (fuel : Nat)
    (source target : α) : Prop :=
  Exists fun length => length <= fuel /\
    Nonempty (ExactWalk edge length source target)

/-- A finite directed walk, with no a priori length bound. -/
def Reachable (edge : α -> α -> Bool) (source target : α) : Prop :=
  Exists fun length => Nonempty (ExactWalk edge length source target)

theorem BoundedWalk.refl (edge : α -> α -> Bool) (fuel : Nat) (node : α) :
    BoundedWalk edge fuel node node :=
  ⟨0, Nat.zero_le _, ⟨.refl node⟩⟩

theorem BoundedWalk.prepend {edge : α -> α -> Bool}
    {fuel : Nat} {source middle target : α}
    (first : edge source middle = true)
    (rest : BoundedWalk edge fuel middle target) :
    BoundedWalk edge (fuel + 1) source target := by
  rcases rest with ⟨length, bound, walk⟩
  rcases walk with ⟨walk⟩
  exact ⟨length + 1, Nat.add_le_add_right bound 1, ⟨.step first walk⟩⟩

theorem BoundedWalk.mono {edge : α -> α -> Bool}
    {smaller larger : Nat} {source target : α}
    (bound : smaller <= larger)
    (walk : BoundedWalk edge smaller source target) :
    BoundedWalk edge larger source target := by
  rcases walk with ⟨length, lengthBound, exactWalk⟩
  exact ⟨length, Nat.le_trans lengthBound bound, exactWalk⟩

theorem Reachable.refl (edge : α -> α -> Bool) (node : α) :
    Reachable edge node node :=
  ⟨0, ⟨.refl node⟩⟩

theorem Reachable.of_bounded {edge : α -> α -> Bool}
    {fuel : Nat} {source target : α}
    (walk : BoundedWalk edge fuel source target) :
    Reachable edge source target := by
  rcases walk with ⟨length, _bound, exactWalk⟩
  exact ⟨length, exactWalk⟩

theorem Reachable.prepend {edge : α -> α -> Bool}
    {source middle target : α}
    (first : edge source middle = true)
    (rest : Reachable edge middle target) :
    Reachable edge source target := by
  rcases rest with ⟨length, rest⟩
  rcases rest with ⟨rest⟩
  exact ⟨length + 1, ⟨.step first rest⟩⟩

theorem ExactWalk.eq_of_length_zero {edge : α -> α -> Bool}
    {source target : α} (walk : ExactWalk edge 0 source target) :
    source = target := by
  cases walk
  rfl

namespace ExactWalk

/-- The vertex list carried by an exact walk. -/
def nodes {edge : α -> α -> Bool} {length : Nat} {source target : α} :
    ExactWalk edge length source target -> List α
  | .refl node => [node]
  | .step _ rest => source :: nodes rest

@[simp] theorem nodes_refl (edge : α -> α -> Bool) (node : α) :
    nodes (.refl (edge := edge) node) = [node] := rfl

@[simp] theorem nodes_step {edge : α -> α -> Bool}
    {length : Nat} {source middle target : α}
    (first : edge source middle = true)
    (rest : ExactWalk edge length middle target) :
    nodes (.step first rest) = source :: nodes rest := rfl

theorem nodes_head {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) :
    walk.nodes.head? = some source := by
  cases walk <;> rfl

theorem nodes_headD {edge : α -> α -> Bool}
    {length : Nat} {source target default : α}
    (walk : ExactWalk edge length source target) :
    walk.nodes.headD default = source := by
  have h := walk.nodes_head
  cases hnodes : walk.nodes with
  | nil =>
      simp [hnodes] at h
  | cons head tail =>
      simp [hnodes] at h
      subst head
      simp

theorem nodes_getLast {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) :
    walk.nodes.getLast? = some target := by
  induction walk with
  | refl => rfl
  | step first rest ih =>
      cases rest with
      | refl => rfl
      | step second tail =>
          simpa [nodes] using ih

theorem mem_source {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) :
    source ∈ walk.nodes := by
  cases walk with
  | refl =>
      simp [nodes]
  | step =>
      simp [nodes]

theorem mem_target {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) :
    target ∈ walk.nodes := by
  induction walk with
  | refl =>
      simp [nodes]
  | step first rest ih =>
      simp [nodes, ih]

theorem nodes_length {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) :
    walk.nodes.length = length + 1 := by
  induction walk with
  | refl => rfl
  | step first rest ih =>
      simp [nodes, ih, Nat.add_assoc]

theorem nodes_consecutive {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) :
    PathSpecification.Consecutive
      (fun left right => edge left right = true) walk.nodes := by
  induction walk with
  | refl => exact .intro
  | @step length source middle target first rest ih =>
      cases rest with
      | refl => exact ⟨first, by simp [PathSpecification.Consecutive]⟩
      | @step restLength _ next _ second tail =>
          exact ⟨first, by simpa [nodes] using ih⟩

/-- Every occurrence in a walk is reached by a prefix walk from the source. -/
theorem prefix_of_mem {edge : α -> α -> Bool}
    {length : Nat} {source target node : α}
    (walk : ExactWalk edge length source target)
    (member : node ∈ walk.nodes) :
    Exists fun prefixLength => prefixLength <= length /\
      Nonempty (ExactWalk edge prefixLength source node) := by
  induction walk with
  | refl endpoint =>
      simp only [nodes, List.mem_singleton] at member
      subst node
      exact ⟨0, Nat.zero_le _, ⟨.refl endpoint⟩⟩
  | @step length source middle target first rest ih =>
      simp only [nodes, List.mem_cons] at member
      rcases member with same | later
      · subst node
        exact ⟨0, Nat.zero_le _, ⟨.refl source⟩⟩
      · rcases ih later with ⟨prefixLength, bound, prefixWalk⟩
        rcases prefixWalk with ⟨prefixWalk⟩
        exact ⟨prefixLength + 1, Nat.add_le_add_right bound 1,
          ⟨.step first prefixWalk⟩⟩

/-- The prefix walk supplied by membership is a list-prefix of the original
walk. -/
theorem exists_prefix_with_subset {edge : α -> α -> Bool}
    {length : Nat} {source target node : α}
    (walk : ExactWalk edge length source target)
    (member : node ∈ walk.nodes) :
    Exists fun prefixLength =>
      Exists fun preWalk : ExactWalk edge prefixLength source node =>
        prefixLength <= length /\
          (forall m, m ∈ preWalk.nodes -> m ∈ walk.nodes) /\
            Exists fun rest => walk.nodes = preWalk.nodes ++ rest := by
  induction walk with
  | refl endpoint =>
      simp only [nodes, List.mem_singleton] at member
      subst node
      exact ⟨0, .refl endpoint, Nat.zero_le _, fun m hm => by
        simpa [nodes, List.mem_singleton] using hm,
        [], by simp [nodes]⟩
  | @step length source middle target first rest ih =>
      simp only [nodes, List.mem_cons] at member
      rcases member with same | later
      · subst node
        refine ⟨0, .refl source, Nat.zero_le _, ?_, rest.nodes, ?_⟩
        · intro m hm
          simp only [nodes, List.mem_singleton] at hm
          subst m
          simp [nodes]
        · simp [nodes]
      · rcases ih later with
          ⟨prefixLength, prefixWalk, bound, subset, tail, hsplit⟩
        refine ⟨prefixLength + 1, .step first prefixWalk,
          Nat.add_le_add_right bound 1, ?_, tail, ?_⟩
        · intro m hm
          simp only [nodes, List.mem_cons] at hm ⊢
          rcases hm with same | later'
          · exact Or.inl same
          · exact Or.inr (subset m later')
        · simp [nodes, hsplit]

/-- A vertex other than the walk's target is reached by a strictly shorter
prefix.  Set-minimal ancestry uses this to keep internals out of the target
family. -/
theorem exists_shorter_prefix_of_internal {edge : α -> α -> Bool}
    {length : Nat} {source target node : α}
    (walk : ExactWalk edge length source target)
    (member : node ∈ walk.nodes) (different : node ≠ target) :
    Exists fun prefixLength => prefixLength < length /\
      Nonempty (ExactWalk edge prefixLength source node) := by
  induction walk with
  | refl endpoint =>
      simp only [nodes, List.mem_singleton] at member
      subst node
      exact (different rfl).elim
  | @step length source middle target first rest ih =>
      simp only [nodes, List.mem_cons] at member
      rcases member with same | later
      · subst node
        exact ⟨0, Nat.succ_pos _, ⟨.refl source⟩⟩
      · rcases ih later different with ⟨prefixLength, bound, prefixWalk⟩
        rcases prefixWalk with ⟨prefixWalk⟩
        exact ⟨prefixLength + 1, Nat.succ_lt_succ bound,
          ⟨.step first prefixWalk⟩⟩

/-- Set-minimal walks cannot pass through an earlier target vertex. -/
theorem not_mem_targets_of_minimal_internal {edge : α -> α -> Bool}
    {length : Nat} {source target node : α} {targets : α -> Bool}
    (walk : ExactWalk edge length source target)
    (minimal : forall target' alternative,
      targets target' = true ->
        Nonempty (ExactWalk edge alternative source target') ->
          length <= alternative)
    (member : node ∈ walk.nodes) (different : node ≠ target) :
    targets node = false := by
  cases hsel : targets node with
  | false =>
      rfl
  | true =>
      rcases exists_shorter_prefix_of_internal walk member different with
        ⟨prefixLength, bound, prefixWalk⟩
      have tooLong := minimal node prefixLength hsel prefixWalk
      exact (Nat.not_le_of_gt bound tooLong).elim

/-- A positive-length set-minimal walk cannot start inside the target family. -/
theorem source_not_mem_targets_of_minimal_pos {edge : α -> α -> Bool}
    {length : Nat} {source target : α} {targets : α -> Bool}
    (_walk : ExactWalk edge length source target)
    (positive : 0 < length)
    (minimal : forall target' alternative,
      targets target' = true ->
        Nonempty (ExactWalk edge alternative source target') ->
          length <= alternative) :
    targets source = false := by
  cases hsel : targets source with
  | false =>
      rfl
  | true =>
      have tooLong := minimal source 0 hsel ⟨.refl source⟩
      exact (Nat.not_le_of_gt positive tooLong).elim

/-- Every occurrence in a walk starts a suffix walk to the same target. -/
theorem suffix_of_mem {edge : α -> α -> Bool}
    {length : Nat} {source target node : α}
    (walk : ExactWalk edge length source target)
    (member : node ∈ walk.nodes) :
    Exists fun suffixLength => suffixLength <= length /\
      Nonempty (ExactWalk edge suffixLength node target) := by
  induction walk with
  | refl endpoint =>
      simp only [nodes, List.mem_singleton] at member
      subst node
      exact ⟨0, Nat.zero_le _, ⟨.refl endpoint⟩⟩
      | @step length source middle target first rest ih =>
      simp only [nodes, List.mem_cons] at member
      rcases member with same | later
      · subst node
        exact ⟨length + 1, Nat.le_refl _, ⟨.step first rest⟩⟩
      · rcases ih later with ⟨suffixLength, bound, suffix⟩
        exact ⟨suffixLength, Nat.le_trans bound (Nat.le_succ _), suffix⟩

/-- The suffix walk supplied by membership is a list-suffix of the original
walk, and it remains simple.  First-shared forks recover the complementary
prefix so that shared vertices after the meet lie on one side of the
reversed trail. -/
theorem exists_simple_suffix_of_mem {edge : α -> α -> Bool}
    {length : Nat} {source target node : α}
    (walk : ExactWalk edge length source target)
    (simple : walk.nodes.Nodup)
    (member : node ∈ walk.nodes) :
    Exists fun suffixLength =>
      Exists fun suffix : ExactWalk edge suffixLength node target =>
        suffix.nodes.Nodup /\
          Exists fun pre => walk.nodes = pre ++ suffix.nodes := by
  induction walk with
  | refl endpoint =>
      simp only [nodes, List.mem_singleton] at member
      subst node
      exact ⟨0, .refl endpoint, by simp [nodes], [], by simp [nodes]⟩
  | @step length source middle target first rest ih =>
      have parts := List.nodup_cons.mp (by simpa [nodes] using simple)
      simp only [nodes, List.mem_cons] at member
      rcases member with same | later
      · subst node
        exact ⟨length + 1, .step first rest, by simpa [nodes] using simple,
          [], by simp [nodes]⟩
      · rcases ih parts.2 later with
          ⟨suffixLength, suffix, suffixSimple, pre, hpre⟩
        exact ⟨suffixLength, suffix, suffixSimple, source :: pre, by
          simp [nodes, hpre]⟩

/-- Computational suffix from membership, for Type-valued path constructors.
Equality of vertices is decided, so the construction never cases on `Exists`. -/
def suffixFrom [DecidableEq α] {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) (node : α)
    (member : node ∈ walk.nodes) :
    Σ' (suffixLength : Nat),
      Σ' (suffix : ExactWalk edge suffixLength node target),
        Σ' (pre : List α), PLift (walk.nodes = pre ++ suffix.nodes) :=
  match walk with
  | refl endpoint => by
      simp only [nodes, List.mem_singleton] at member
      subst node
      exact ⟨0, .refl endpoint, [], ⟨by simp [nodes]⟩⟩
  | @ExactWalk.step _ _ len src mid tgt first rest =>
      if h : node = src then
        ⟨len + 1, h.symm ▸ ExactWalk.step first rest, [], ⟨by
          cases h
          rfl⟩⟩
      else by
        have later : node ∈ rest.nodes := by
          simp only [nodes, List.mem_cons] at member
          rcases member with same | later
          · exact (h same).elim
          · exact later
        rcases suffixFrom rest node later with
          ⟨suffixLength, suffix, pre, ⟨hpre⟩⟩
        exact ⟨suffixLength, suffix, src :: pre, ⟨by simp [nodes, hpre]⟩⟩

/-- A shortest exact walk cannot repeat a vertex. -/
theorem nodes_nodup_of_minimal {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target)
    (minimal : forall alternative,
      Nonempty (ExactWalk edge alternative source target) ->
        length <= alternative) :
    walk.nodes.Nodup := by
  induction walk with
  | refl => simp [nodes]
  | @step length source middle target first rest ih =>
      rw [nodes, List.nodup_cons]
      constructor
      · intro repeated
        rcases rest.suffix_of_mem repeated with
          ⟨suffixLength, suffixBound, suffix⟩
        have minimum := minimal suffixLength suffix
        omega
      · apply ih
        intro alternative alternativeWalk
        rcases alternativeWalk with ⟨alternativeWalk⟩
        have extended : Nonempty
            (ExactWalk edge (alternative + 1) source target) :=
          ⟨.step first alternativeWalk⟩
        have minimum := minimal (alternative + 1) extended
        omega

/-- Append one edge to an exact walk. -/
def snoc {edge : α -> α -> Bool} {length : Nat}
    {source middle target : α}
    (walk : ExactWalk edge length source middle)
    (last : edge middle target = true) :
    ExactWalk edge (length + 1) source target :=
  match walk with
  | .refl _ => .step last (.refl target)
  | .step first rest => .step first (rest.snoc last)

/-- Reverse an exact walk along a symmetric edge relation. -/
def reverse {edge : α -> α -> Bool}
    (symmetric : forall left right,
      edge left right = true -> edge right left = true)
    {length : Nat} {source target : α} :
    ExactWalk edge length source target ->
    ExactWalk edge length target source
  | .refl node => .refl node
  | .step first rest =>
      (reverse symmetric rest).snoc (symmetric _ _ first)

/-- Reinterpret an exact walk along a coarser edge relation. -/
def mapEdge {e1 e2 : α -> α -> Bool}
    (included : forall left right, e1 left right = true -> e2 left right = true)
    {length : Nat} {source target : α} :
    ExactWalk e1 length source target -> ExactWalk e2 length source target
  | .refl node => .refl node
  | .step first rest => .step (included _ _ first) (mapEdge included rest)

@[simp] theorem mapEdge_nodes {e1 e2 : α -> α -> Bool}
    (included : forall left right, e1 left right = true -> e2 left right = true)
    {length : Nat} {source target : α}
    (walk : ExactWalk e1 length source target) :
    (mapEdge included walk).nodes = walk.nodes := by
  induction walk with
  | refl node =>
      simp [mapEdge, nodes]
  | step first rest ih =>
      simp [mapEdge, nodes, ih]

theorem nodes_ne_nil {edge : α -> α -> Bool} {length : Nat}
    {source target : α} (walk : ExactWalk edge length source target) :
    walk.nodes ≠ [] := by
  cases walk <;> simp [nodes]

/-- Concatenate two exact walks that meet at a common vertex. -/
def append {edge : α -> α -> Bool}
    {leftLength rightLength : Nat} {source middle target : α}
    (leftWalk : ExactWalk edge leftLength source middle)
    (rightWalk : ExactWalk edge rightLength middle target) :
    ExactWalk edge (leftLength + rightLength) source target :=
  match leftWalk with
  | .refl _ => Eq.symm (Nat.zero_add rightLength) ▸ rightWalk
  | .step first tail =>
      (Eq.symm (Nat.add_right_comm _ 1 rightLength)) ▸
        .step first (append tail rightWalk)

/-- Rebuild an exact walk from a consecutive vertex list. -/
def ofConsecutive {edge : α -> α -> Bool}
    {source target : α} (nodes : List α)
    (starts : nodes.head? = some source)
    (finishes : nodes.getLast? = some target)
    (consecutive : PathSpecification.Consecutive
      (fun left right => edge left right = true) nodes) :
    ExactWalk edge (nodes.length - 1) source target := by
  match nodes with
  | [] =>
      simp at starts
  | [node] =>
      simp only [List.head?_cons, Option.some.injEq] at starts
      simp only [List.getLast?_singleton, Option.some.injEq] at finishes
      subst source
      subst target
      exact ExactWalk.refl (edge := edge) node
  | left :: right :: rest =>
      simp only [List.head?_cons, Option.some.injEq] at starts
      subst source
      have tailFinishes : (right :: rest).getLast? = some target := by
        simpa using finishes
      have tailWalk :=
        ofConsecutive (right :: rest) rfl tailFinishes consecutive.2
      have lengthEq :
          (left :: right :: rest).length - 1 =
            ((right :: rest).length - 1) + 1 := by
        simp [List.length_cons]
      exact lengthEq ▸ ExactWalk.step consecutive.1 tailWalk

end ExactWalk

/-- Concatenate two bounded walks; the bound adds. -/
theorem BoundedWalk.trans {edge : α -> α -> Bool}
    {fuel fuel' : Nat} {source middle target : α}
    (left : BoundedWalk edge fuel source middle)
    (right : BoundedWalk edge fuel' middle target) :
    BoundedWalk edge (fuel + fuel') source target := by
  rcases left with ⟨leftLen, leftBound, leftWalk⟩
  rcases right with ⟨rightLen, rightBound, rightWalk⟩
  rcases leftWalk with ⟨leftExact⟩
  rcases rightWalk with ⟨rightExact⟩
  exact ⟨leftLen + rightLen, Nat.add_le_add leftBound rightBound,
    ⟨ExactWalk.append leftExact rightExact⟩⟩

private theorem mem_step_iff
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (reached : List α) (target : α) :
    target ∈ step same nodes edge reached <->
      target ∈ nodes /\ Exists fun source =>
        source ∈ reached /\ (source = target \/ edge source target = true) := by
  simp [step, same_iff, Bool.or_eq_true]

/--
The iterated Boolean search is sound and complete for bounded walks when its
node list enumerates the carrier and its equality test is exact.
-/
theorem mem_closure_iff_boundedWalk
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (complete : forall node, node ∈ nodes) (fuel : Nat)
    (reached : List α) (target : α) :
    target ∈ closure same nodes edge fuel reached <->
      Exists fun source => source ∈ reached /\
        BoundedWalk edge fuel source target := by
  induction fuel generalizing reached target with
  | zero =>
      constructor
      · intro member
        exact ⟨target, member, BoundedWalk.refl edge 0 target⟩
      · rintro ⟨source, member, length, bound, walk⟩
        have lengthZero : length = 0 := Nat.eq_zero_of_le_zero bound
        subst length
        rcases walk with ⟨walk⟩
        cases walk
        exact member
  | succ fuel ih =>
      rw [closure]
      constructor
      · intro member
        rcases (ih (step same nodes edge reached) target).mp member with
          ⟨middle, middleReached, rest⟩
        rcases (mem_step_iff same nodes edge same_iff reached middle).mp
            middleReached with ⟨_, source, sourceReached, sameOrEdge⟩
        refine ⟨source, sourceReached, ?_⟩
        rcases sameOrEdge with sameNode | firstEdge
        · subst middle
          exact rest.mono (Nat.le_succ fuel)
        · exact rest.prepend firstEdge
      · rintro ⟨source, sourceReached, length, bound, walk⟩
        rcases walk with ⟨walk⟩
        cases length with
        | zero =>
            have sameTarget : source = target := walk.eq_of_length_zero
            subst target
            apply (ih (step same nodes edge reached) source).mpr
            refine ⟨source, ?_, BoundedWalk.refl edge fuel source⟩
            exact (mem_step_iff same nodes edge same_iff reached source).mpr
              ⟨complete source, source, sourceReached, Or.inl rfl⟩
        | succ length =>
            cases walk with
            | @step _ _ middle _ firstEdge rest =>
                have restBound : length <= fuel := by omega
                apply (ih (step same nodes edge reached) target).mpr
                refine ⟨middle, ?_, ⟨length, restBound, ⟨rest⟩⟩⟩
                exact (mem_step_iff same nodes edge same_iff reached middle).mpr
                  ⟨complete middle, source, sourceReached, Or.inr firstEdge⟩

theorem within_eq_true_iff_boundedWalk
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (complete : forall node, node ∈ nodes) (fuel : Nat)
    (source target : α) :
    within same nodes edge fuel source target = true <->
      BoundedWalk edge fuel source target := by
  rw [within]
  simp only [contains, List.any_eq_true]
  constructor
  · rintro ⟨found, foundMember, sameTarget⟩
    have foundEq : found = target := (same_iff found target).mp sameTarget
    subst found
    rcases (mem_closure_iff_boundedWalk same nodes edge same_iff complete fuel
      [source] target).mp foundMember with ⟨start, startMember, walk⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at startMember
    subst start
    exact walk
  · intro walk
    refine ⟨target, ?_, (same_iff target target).mpr rfl⟩
    exact (mem_closure_iff_boundedWalk same nodes edge same_iff complete fuel
      [source] target).mpr ⟨source, by simp, walk⟩

/-- A bounded walk contains a shortest exact walk, found by decreasing fuel. -/
theorem exists_minimal_exactWalk_of_boundedWalk
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (complete : forall node, node ∈ nodes)
    {fuel : Nat} {source target : α}
    (bounded : BoundedWalk edge fuel source target) :
    Exists fun length => length <= fuel /\
      Nonempty (ExactWalk edge length source target) /\
        forall alternative,
          Nonempty (ExactWalk edge alternative source target) ->
            length <= alternative := by
  induction fuel with
  | zero =>
      rcases bounded with ⟨length, bound, walk⟩
      have lengthZero : length = 0 := Nat.eq_zero_of_le_zero bound
      subst length
      exact ⟨0, Nat.zero_le _, walk, fun _ _ => Nat.zero_le _⟩
  | succ fuel ih =>
      cases earlier : within same nodes edge fuel source target with
      | true =>
          have earlierBounded : BoundedWalk edge fuel source target :=
            (within_eq_true_iff_boundedWalk same nodes edge same_iff complete
              fuel source target).mp earlier
          rcases ih earlierBounded with
            ⟨length, lengthBound, walk, minimal⟩
          exact ⟨length, Nat.le_trans lengthBound (Nat.le_succ fuel),
            walk, minimal⟩
      | false =>
          rcases bounded with ⟨length, bound, walk⟩
          have notEarlier : Not (length <= fuel) := by
            intro lengthBound
            have found : within same nodes edge fuel source target = true :=
              (within_eq_true_iff_boundedWalk same nodes edge same_iff complete
                fuel source target).mpr ⟨length, lengthBound, walk⟩
            rw [earlier] at found
            contradiction
          have exactLength : length = fuel + 1 := by omega
          subst length
          refine ⟨fuel + 1, Nat.le_refl _, walk, ?_⟩
          intro alternative alternativeWalk
          cases alternativeBound : decide (alternative <= fuel) with
          | true =>
              have leFuel : alternative <= fuel := of_decide_eq_true alternativeBound
              have found : within same nodes edge fuel source target = true :=
                (within_eq_true_iff_boundedWalk same nodes edge same_iff complete
                  fuel source target).mpr
                    ⟨alternative, leFuel, alternativeWalk⟩
              rw [earlier] at found
              contradiction
          | false =>
              have notLe : Not (alternative <= fuel) := by
                exact of_decide_eq_false alternativeBound
              omega

/-- A bounded walk into a displayed family contains a shortest exact walk
into that family, not merely into one chosen member. -/
theorem exists_minimal_exactWalk_to_set
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (complete : forall node, node ∈ nodes)
    {fuel : Nat} {source : α} {targets : α -> Bool}
    (reached : Exists fun target =>
      targets target = true /\ BoundedWalk edge fuel source target) :
    Exists fun target =>
      targets target = true /\
        Exists fun length =>
          Nonempty (ExactWalk edge length source target) /\
            (forall target' alternative,
              targets target' = true ->
                Nonempty (ExactWalk edge alternative source target') ->
                  length <= alternative) := by
  induction fuel with
  | zero =>
      rcases reached with ⟨target, selected, ⟨length, bound, walk⟩⟩
      have lengthZero : length = 0 := Nat.eq_zero_of_le_zero bound
      subst length
      exact ⟨target, selected, 0, walk, fun _ _ _ _ => Nat.zero_le _⟩
  | succ fuel ih =>
      cases earlier : nodes.any (fun candidate =>
          targets candidate &&
            within same nodes edge fuel source candidate) with
      | true =>
          have earlierReached : Exists fun target =>
              targets target = true /\ BoundedWalk edge fuel source target := by
            rcases List.any_eq_true.mp earlier with
              ⟨target, _member, holds⟩
            have parts := Bool.and_eq_true_iff.mp holds
            exact ⟨target, parts.1,
              (within_eq_true_iff_boundedWalk same nodes edge same_iff complete
                fuel source target).mp parts.2⟩
          exact ih earlierReached
      | false =>
          rcases reached with ⟨target, selected, ⟨length, bound, walk⟩⟩
          have notEarlier : Not (length <= fuel) := by
            intro lengthBound
            have found : within same nodes edge fuel source target = true :=
              (within_eq_true_iff_boundedWalk same nodes edge same_iff complete
                fuel source target).mpr ⟨length, lengthBound, walk⟩
            have anyFound :
                nodes.any (fun candidate =>
                  targets candidate &&
                    within same nodes edge fuel source candidate) = true :=
              List.any_eq_true.mpr
                ⟨target, complete target,
                  Bool.and_eq_true_iff.mpr ⟨selected, found⟩⟩
            rw [earlier] at anyFound
            contradiction
          have exactLength : length = fuel + 1 := by omega
          subst length
          refine ⟨target, selected, fuel + 1, walk, ?_⟩
          intro target' alternative selected' alternativeWalk
          cases alternativeBound : decide (alternative <= fuel) with
          | true =>
              have leFuel : alternative <= fuel :=
                of_decide_eq_true alternativeBound
              have found : within same nodes edge fuel source target' = true :=
                (within_eq_true_iff_boundedWalk same nodes edge same_iff
                  complete fuel source target').mpr
                    ⟨alternative, leFuel, alternativeWalk⟩
              have anyFound :
                  nodes.any (fun candidate =>
                    targets candidate &&
                      within same nodes edge fuel source candidate) = true :=
                List.any_eq_true.mpr
                  ⟨target', complete target',
                    Bool.and_eq_true_iff.mpr ⟨selected', found⟩⟩
              rw [earlier] at anyFound
              contradiction
          | false =>
              have notLe : Not (alternative <= fuel) :=
                of_decide_eq_false alternativeBound
              omega

/-- An exact walk together with the proof that its vertex list is simple. -/
structure SimpleWalk (edge : α -> α -> Bool) (source target : α) : Type where
  length : Nat
  walk : ExactWalk edge length source target
  simple : walk.nodes.Nodup

theorem nonempty_simpleWalk_of_boundedWalk
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (complete : forall node, node ∈ nodes)
    {fuel : Nat} {source target : α}
    (bounded : BoundedWalk edge fuel source target) :
    Nonempty (SimpleWalk edge source target) := by
  rcases exists_minimal_exactWalk_of_boundedWalk same nodes edge same_iff
      complete bounded with ⟨length, _bound, walk, minimal⟩
  rcases walk with ⟨walk⟩
  exact ⟨⟨length, walk, walk.nodes_nodup_of_minimal minimal⟩⟩

end FiniteReachability

private theorem bool_not_any_eq_true_iff
    (values : List α) (predicate : α -> Bool) :
    Bool.not (values.any predicate) = true <->
      Not (Exists fun value => value ∈ values /\ predicate value = true) := by
  constructor
  · intro none witness
    rcases witness with ⟨value, member, holds⟩
    have found : values.any predicate = true :=
      List.any_eq_true.mpr ⟨value, member, holds⟩
    rw [found] at none
    contradiction
  · intro none
    cases found : values.any predicate with
    | false => rfl
    | true =>
        exact (none (List.any_eq_true.mp found)).elim

private theorem filter_not_same_length_lt_of_mem
    (same : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (target : α) : forall nodes : List α,
      target ∈ nodes ->
        (nodes.filter (fun node => Bool.not (same node target))).length <
          nodes.length
  | [], member => by simp at member
  | head :: tail, member => by
      simp only [List.mem_cons] at member
      cases equalValue : same head target with
      | true =>
          simp [List.filter, equalValue]
          exact Nat.lt_succ_of_le (List.length_filter_le
            (fun node => Bool.not (same node target)) tail)
      | false =>
          have tailMember : target ∈ tail := by
            rcases member with sameNode | later
            · subst head
              have equalTrue := (same_iff target target).mpr rfl
              rw [equalValue] at equalTrue
              contradiction
            · exact later
          simp only [List.filter, equalValue, Bool.not_false, List.length_cons]
          exact Nat.succ_lt_succ
            (filter_not_same_length_lt_of_mem same same_iff target tail
              tailMember)

theorem nodup_length_le_of_subset
    (same : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (path ambient : List α) (simple : path.Nodup)
    (contained : forall node, node ∈ path -> node ∈ ambient) :
    path.length <= ambient.length := by
  induction path generalizing ambient with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
      rw [List.nodup_cons] at simple
      have headMember : head ∈ ambient := contained head (by simp)
      have tailContained : forall node, node ∈ tail ->
          node ∈ ambient.filter (fun candidate =>
            Bool.not (same candidate head)) := by
        intro node nodeMember
        have different : node ≠ head := by
          intro same
          subst node
          exact simple.1 nodeMember
        apply List.mem_filter.mpr
        refine ⟨contained node (by simp [nodeMember]), ?_⟩
        cases equalValue : same node head with
        | false => rfl
        | true =>
            exact (different ((same_iff node head).mp equalValue)).elim
      have tailBound := ih
        (ambient.filter (fun candidate => Bool.not (same candidate head)))
        simple.2 tailContained
      have filteredShorter := filter_not_same_length_lt_of_mem
        same same_iff head ambient headMember
      simp only [List.length_cons]
      omega

/-- A constructive maximum principle for the false entries of a Boolean
predicate on a finite list. -/
theorem exists_rank_maximal_false (rank : α -> Nat) (good : α -> Bool) :
    forall nodes : List α,
      (Exists fun node => node ∈ nodes /\ good node = false) ->
        Exists fun best => best ∈ nodes /\ good best = false /\
          forall node, node ∈ nodes -> good node = false ->
            rank node <= rank best
  | [], witness => by
      rcases witness with ⟨node, member, _bad⟩
      simp at member
  | head :: tail, witness => by
      cases headGood : good head with
      | true =>
          have tailWitness : Exists fun node =>
              node ∈ tail /\ good node = false := by
            rcases witness with ⟨node, member, bad⟩
            simp only [List.mem_cons] at member
            rcases member with same | later
            · subst node
              rw [headGood] at bad
              contradiction
            · exact ⟨node, later, bad⟩
          rcases exists_rank_maximal_false rank good tail tailWitness with
            ⟨best, bestMember, bestBad, maximal⟩
          exact ⟨best, by simp [bestMember], bestBad, fun node member bad => by
            simp only [List.mem_cons] at member
            rcases member with same | later
            · subst node
              rw [headGood] at bad
              contradiction
            · exact maximal node later bad⟩
      | false =>
          cases tailHasBad : tail.any (fun node => !(good node)) with
          | false =>
              refine ⟨head, by simp, headGood, ?_⟩
              intro node member bad
              simp only [List.mem_cons] at member
              rcases member with same | later
              · subst node
                exact Nat.le_refl _
              · have found : tail.any (fun candidate => !(good candidate)) =
                    true := List.any_eq_true.mpr ⟨node, later, by simp [bad]⟩
                rw [tailHasBad] at found
                contradiction
          | true =>
              rcases List.any_eq_true.mp tailHasBad with
                ⟨node, nodeMember, nodeBad⟩
              have nodeFalse : good node = false := by
                cases value : good node with
                | false => rfl
                | true => simp [value] at nodeBad
              rcases exists_rank_maximal_false rank good tail
                  ⟨node, nodeMember, nodeFalse⟩ with
                ⟨best, bestMember, bestBad, maximal⟩
              rcases Nat.le_total (rank head) (rank best) with
                headLe | bestLe
              · refine ⟨best, by simp [bestMember], bestBad, ?_⟩
                intro other member bad
                simp only [List.mem_cons] at member
                rcases member with same | later
                · subst other
                  exact headLe
                · exact maximal other later bad
              · refine ⟨head, by simp, headGood, ?_⟩
                intro other member bad
                simp only [List.mem_cons] at member
                rcases member with same | later
                · subst other
                  exact Nat.le_refl _
                · exact Nat.le_trans (maximal other later bad) bestLe

/-- A non-endpoint occurrence in a finite list has immediate neighbours. -/
theorem exists_internal_neighbors_of_mem
    {source target node : α} {nodes : List α}
    (starts : nodes.head? = some source)
    (finishes : nodes.getLast? = some target)
    (member : node ∈ nodes) (notSource : node ≠ source)
    (notTarget : node ≠ target) :
    Exists fun beforePrefix => Exists fun previous => Exists fun next =>
      Exists fun suffix =>
        nodes = beforePrefix ++ previous :: node :: next :: suffix := by
  rcases List.mem_iff_append.mp member with ⟨before, after, split⟩
  have beforeNonempty : before ≠ [] := by
    intro empty
    subst before
    simp only [List.nil_append] at split
    subst nodes
    simp only [List.head?_cons, Option.some.injEq] at starts
    exact notSource starts
  have afterNonempty : after ≠ [] := by
    intro empty
    subst after
    subst nodes
    have lastNode : (before ++ [node]).getLast? = some node :=
      List.getLast?_concat
    rw [finishes] at lastNode
    exact notTarget (Option.some.inj lastNode).symm
  rcases List.exists_cons_of_ne_nil afterNonempty with
    ⟨next, suffix, afterSplit⟩
  let previous := before.getLast beforeNonempty
  refine ⟨before.dropLast, previous, next, suffix, ?_⟩
  rw [split, afterSplit]
  have beforeSplit := List.dropLast_concat_getLast beforeNonempty
  rw [← beforeSplit]
  simp [previous, List.append_assoc]

/-- Dropping a left summand of known length is definitional once the list is
written as an append.  Oxford overlap glue uses this to recover the suffix
after the first shared vertex. -/
theorem drop_append_length {α} (xs ys : List α) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil => simp
  | cons _ rest ih =>
      simp [ih]

/-- Dropping the last cell of a snoc-list recovers the prefix. -/
theorem dropLast_snoc {α} (pre : List α) (a : α) :
    (pre ++ [a]).dropLast = pre := by
  induction pre with
  | nil =>
      simp
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp [List.dropLast]
      | cons y ys =>
          simp [List.cons_append, List.dropLast]

/-- The first success of a Boolean `find?` splits the list into earlier
failures, the witness, and the unexamined suffix.  The construction is by
induction on the list, so it does not invoke choice. -/
theorem find?_eq_some_split {α} (p : α -> Bool) :
    forall (xs : List α) (a : α), xs.find? p = some a ->
      Exists fun before => Exists fun after =>
        xs = before ++ a :: after /\
          (forall x, x ∈ before -> p x = false) /\ p a = true
  | [], a, h => by simp at h
  | x :: xs, a, h => by
      cases hp : p x with
      | true =>
          simp [List.find?, hp] at h
          subst a
          refine ⟨[], xs, rfl, ?_, hp⟩
          intro _y mem
          exact (List.not_mem_nil mem).elim
      | false =>
          simp [List.find?, hp] at h
          rcases find?_eq_some_split p xs a h with
            ⟨before, after, split, noneBefore, pa⟩
          refine ⟨x :: before, after, by simp [split], ?_, pa⟩
          intro y mem
          simp only [List.mem_cons] at mem
          rcases mem with same | later
          · subst y
            exact hp
          · exact noneBefore y later

/-- Computational splitter for Boolean `find?`, used by Type-valued
path constructors that cannot case on `Exists`. -/
def find?Split {α} (p : α -> Bool) : List α -> Option (List α × α × List α)
  | [] => none
  | x :: xs =>
      if p x then
        some ([], x, xs)
      else
        match find?Split p xs with
        | none => none
        | some (before, a, after) => some (x :: before, a, after)

theorem find?_eq_none_of_find?Split {α} (p : α -> Bool) :
    forall (xs : List α), find?Split p xs = none -> xs.find? p = none
  | [], _h => rfl
  | x :: xs, h => by
      cases hp : p x with
      | true =>
          simp [find?Split, hp] at h
      | false =>
          cases hsplit : find?Split p xs with
          | none =>
              have htail := find?_eq_none_of_find?Split p xs hsplit
              simpa [List.find?, hp] using htail
          | some _triple =>
              simp [find?Split, hp, hsplit] at h

theorem find?Split_eq_none_of_find? {α} (p : α -> Bool) :
    forall (xs : List α), xs.find? p = none -> find?Split p xs = none
  | [], _h => rfl
  | x :: xs, h => by
      cases hp : p x with
      | true =>
          simp [List.find?, hp] at h
      | false =>
          have htail : xs.find? p = none := by
            simpa [List.find?, hp] using h
          simp [find?Split, hp, find?Split_eq_none_of_find? p xs htail]

theorem find?Split_spec {α} (p : α -> Bool) (xs : List α) :
    forall (before : List α) (a : α) (after : List α),
      find?Split p xs = some (before, a, after) ->
        xs = before ++ a :: after ∧
          (forall x, x ∈ before -> p x = false) ∧ p a = true := by
  induction xs with
  | nil =>
      intro before a after h
      simp [find?Split] at h
  | cons x xs ih =>
      intro before a after h
      cases hp : p x with
      | true =>
          simp [find?Split, hp] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, fun y hy => (List.not_mem_nil hy).elim, hp⟩
      | false =>
          cases hsplit : find?Split p xs with
          | none =>
              simp [find?Split, hp, hsplit] at h
          | some val =>
              rcases val with ⟨b, a', af⟩
              simp [find?Split, hp, hsplit] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              have nested := ih b a' af hsplit
              refine ⟨by simp [nested.1], ?_, nested.2.2⟩
              intro y mem
              simp only [List.mem_cons] at mem
              rcases mem with same | later
              · subst y
                exact hp
              · exact nested.2.1 y later

theorem find?_eq_some_of_find?Split {α} (p : α -> Bool) (xs : List α) :
    forall (before : List α) (a : α) (after : List α),
      find?Split p xs = some (before, a, after) ->
        xs.find? p = some a := by
  induction xs with
  | nil =>
      intro before a after h
      simp [find?Split] at h
  | cons x xs ih =>
      intro before a after h
      cases hp : p x with
      | true =>
          simp [find?Split, hp] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          simp [List.find?, hp]
      | false =>
          cases hsplit : find?Split p xs with
          | none =>
              simp [find?Split, hp, hsplit] at h
          | some val =>
              rcases val with ⟨b, a', af⟩
              simp [find?Split, hp, hsplit] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              have nested := ih b a' af hsplit
              simpa [List.find?, hp] using nested

theorem eq_false_of_find?_eq_none {α} {p : α -> Bool} {xs : List α} {x : α}
    (h : xs.find? p = none) (hx : x ∈ xs) : p x = false := by
  have hx' := List.find?_eq_none.mp h x hx
  cases hp : p x with
  | false =>
      rfl
  | true =>
      rw [hp] at hx'
      exact (hx' rfl).elim

/-- A successful `find?` on a prefix remains the first success after any
suffix is appended. -/
theorem find?_append_left {α} (p : α -> Bool)
    (xs ys : List α) {a : α}
    (h : xs.find? p = some a) :
    (xs ++ ys).find? p = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      cases hp : p x with
      | true =>
          simp only [List.cons_append, List.find?, hp] at h ⊢
          exact h
      | false =>
          have htail : xs.find? p = some a := by
            simpa [List.find?, hp] using h
          simpa [List.cons_append, List.find?, hp] using ih htail

/-- If a prefix has no success, the first success of the concatenated list
is the displayed head of the remainder. -/
theorem find?_eq_none_append_cons {α} (p : α -> Bool)
    (xs : List α) (y : α) (ys : List α)
    (hnone : xs.find? p = none) (hy : p y = true) :
    (xs ++ y :: ys).find? p = some y := by
  induction xs with
  | nil =>
      simp [hy]
  | cons x xs ih =>
      have hx : p x = false :=
        eq_false_of_find?_eq_none hnone (List.mem_cons.mpr (Or.inl rfl))
      have hnone_tail : xs.find? p = none :=
        List.find?_eq_none.mpr (fun a ha => by
          have hf := eq_false_of_find?_eq_none hnone
            (List.mem_cons.mpr (Or.inr ha))
          rw [hf]
          exact Bool.false_ne_true)
      simpa [List.cons_append, List.find?, hx] using ih hnone_tail

/-- Two decompositions at the same excluded middle cell agree. -/
theorem append_cons_inj_of_not_mem {α}
    {xs ys xs' ys' : List α} {a : α}
    (h : xs ++ a :: ys = xs' ++ a :: ys')
    (nxs : a ∉ xs) (nxs' : a ∉ xs') :
    xs = xs' ∧ ys = ys' := by
  induction xs generalizing xs' with
  | nil =>
      cases xs' with
      | nil =>
          simp at h
          exact ⟨rfl, h⟩
      | cons x xs' =>
          simp [List.cons_append] at h
          rcases h with ⟨hax, _hrest⟩
          subst x
          exact (nxs' (List.mem_cons.mpr (Or.inl rfl))).elim
  | cons x xs ih =>
      cases xs' with
      | nil =>
          simp [List.cons_append] at h
          rcases h with ⟨_hxa, _hrest⟩
          subst x
          exact (nxs (List.mem_cons.mpr (Or.inl rfl))).elim
      | cons x' xs' =>
          simp [List.cons_append] at h
          rcases h with ⟨hxx, hrest⟩
          subst x'
          have nxs_tail : a ∉ xs :=
            fun ha => nxs (List.mem_cons.mpr (Or.inr ha))
          have nxs'_tail : a ∉ xs' :=
            fun ha => nxs' (List.mem_cons.mpr (Or.inr ha))
          rcases ih hrest nxs_tail nxs'_tail with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩

/-- Concatenating two simple lists that share no vertex remains simple. -/
theorem nodup_append_of_disjoint {α} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (disj : forall a, a ∈ xs -> a ∈ ys -> False) :
    (xs ++ ys).Nodup := by
  induction xs with
  | nil => simpa using hy
  | cons x rest ih =>
      have parts := List.nodup_cons.mp hx
      refine List.nodup_cons.mpr ⟨?_, ih parts.2 (fun a haRest haYs =>
        disj a (List.mem_cons.mpr (Or.inr haRest)) haYs)⟩
      intro mem
      rcases List.mem_append.mp mem with inRest | inYs
      · exact parts.1 inRest
      · exact disj x (by simp) inYs

/-- Reversing a simple list remains simple.  The proof is by induction and
the disjoint-append lemma, so it does not depend on a library `Iff` form
of `List.nodup_reverse`. -/
theorem nodup_reverse_of {α} {xs : List α} (h : xs.Nodup) :
    xs.reverse.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.reverse_cons]
      have parts := List.nodup_cons.mp h
      have ih' := ih parts.2
      refine nodup_append_of_disjoint ih' (by simp) ?_
      intro a haRev haSingleton
      have same : a = x := List.mem_singleton.mp haSingleton
      subst a
      exact parts.1 (List.mem_reverse.mp haRev)

/-- The head of a reversed list is the original last vertex. -/
theorem head?_reverse_eq_getLast? {α} (xs : List α) :
    xs.reverse.head? = xs.getLast? := by
  have h := List.getLast?_reverse (l := xs.reverse)
  rw [List.reverse_reverse] at h
  exact h.symm

/-- Splitting a simple list at a displayed vertex yields two simple sides
that do not contain the vertex, and that share no vertex with each other. -/
theorem nodup_of_split {α} {before : List α} {node : α} {after : List α}
    (simple : (before ++ node :: after).Nodup) :
    before.Nodup /\ node ∉ before /\ node ∉ after /\ after.Nodup /\
      (forall x, x ∈ before -> x ∈ after -> False) := by
  induction before with
  | nil =>
      have parts := List.nodup_cons.mp (by simpa using simple)
      exact ⟨List.nodup_nil, fun mem => List.not_mem_nil mem, parts.1, parts.2,
        fun _x mem => (List.not_mem_nil mem).elim⟩
  | cons head tail ih =>
      rw [List.cons_append] at simple
      have parts := List.nodup_cons.mp simple
      have rest := ih parts.2
      refine ⟨List.nodup_cons.mpr ⟨?_, rest.1⟩, ?_, rest.2.2.1, rest.2.2.2.1,
        ?_⟩
      · intro mem
        apply parts.1
        exact List.mem_append.mpr (Or.inl mem)
      · intro mem
        simp only [List.mem_cons] at mem
        rcases mem with same | later
        · subst node
          apply parts.1
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        · exact rest.2.1 later
      · intro x memHeadOrTail memAfter
        simp only [List.mem_cons] at memHeadOrTail
        rcases memHeadOrTail with same | later
        · subst x
          apply parts.1
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr memAfter)))
        · exact rest.2.2.2.2 x later memAfter

/-- Cutting two simple lists at a shared vertex and concatenating the
left prefix of the first with the right suffix of the second remains
simple, provided no vertex of that left prefix appears anywhere in the
second list.  That disjointness is exactly the first-success property of
`firstSharedSeparation?`. -/
theorem nodup_overlap_glue {α} {front back : List α} {v : α}
    {frontBefore frontAfter backBefore backAfter : List α}
    (frontSimple : front.Nodup) (backSimple : back.Nodup)
    (frontSplit : front = frontBefore ++ v :: frontAfter)
    (backSplit : back = backBefore ++ v :: backAfter)
    (beforeDisjoint : forall x, x ∈ frontBefore -> x ∈ back -> False) :
    (frontBefore ++ v :: backAfter).Nodup := by
  have frontParts := nodup_of_split (by simpa [frontSplit] using frontSimple)
  have backParts := nodup_of_split (by simpa [backSplit] using backSimple)
  have tailSimple : (v :: backAfter).Nodup :=
    List.nodup_cons.mpr ⟨backParts.2.2.1, backParts.2.2.2.1⟩
  refine nodup_append_of_disjoint frontParts.1 tailSimple ?_
  intro a haBefore haTail
  simp only [List.mem_cons] at haTail
  rcases haTail with same | later
  · subst a
    exact frontParts.2.1 haBefore
  · exact beforeDisjoint a haBefore (by
      rw [backSplit]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr later))))

namespace PathSpecification

theorem InternalTriplesActive.tail
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S} {nodes : List (SeparationNode S)}
    (active : InternalTriplesActive G mutilation conditioned nodes) :
    InternalTriplesActive G mutilation conditioned nodes.tail := by
  cases active with
  | nil => exact .nil
  | singleton node => exact .nil
  | pair left right => exact .singleton right
  | step triple rest => exact rest

theorem InternalTriplesActive.triple_of_append
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S}
    (beforePrefix suffix : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (active : InternalTriplesActive G mutilation conditioned
      (beforePrefix ++ previous :: middle :: next :: suffix)) :
    TripleActive G mutilation conditioned previous middle next := by
  induction beforePrefix with
  | nil =>
      cases active with
      | step triple _rest => exact triple
  | cons head tail ih =>
      apply ih
      exact active.tail

theorem Consecutive.pair_of_append {relation : α -> α -> Prop}
    (beforePrefix suffix : List α) (left right : α)
    (consecutive : Consecutive relation
      (beforePrefix ++ left :: right :: suffix)) :
    relation left right := by
  induction beforePrefix with
  | nil => exact consecutive.1
  | cons head tail ih =>
      cases tail with
      | nil => exact consecutive.2.1
      | cons second rest => exact ih consecutive.2

theorem Consecutive.prefix_append {relation : α -> α -> Prop}
    (before : List α) (node : α) (after : List α)
    (consecutive : Consecutive relation (before ++ node :: after)) :
    Consecutive relation (before ++ [node]) := by
  induction before with
  | nil => simp [Consecutive]
  | cons head tail ih =>
      cases tail with
      | nil => exact ⟨consecutive.1, by simp [Consecutive]⟩
      | cons second rest => exact ⟨consecutive.1, ih consecutive.2⟩

theorem Consecutive.snoc {relation : α -> α -> Prop}
    {nodes : List α} {last : α}
    (consecutive : Consecutive relation nodes)
    (linked : forall previous, nodes.getLast? = some previous ->
      relation previous last) :
    Consecutive relation (nodes ++ [last]) := by
  cases nodes with
  | nil => simp [Consecutive]
  | cons first tail =>
      cases tail with
      | nil =>
          exact ⟨linked first rfl, by simp [Consecutive]⟩
      | cons second rest =>
          exact ⟨consecutive.1,
            Consecutive.snoc (nodes := second :: rest) consecutive.2
              (fun previous hprev => linked previous (by
                simpa [List.getLast?_cons_cons] using hprev))⟩

theorem Consecutive.drop {relation : α -> α -> Prop} :
    forall (count : Nat) (nodes : List α),
      Consecutive relation nodes -> Consecutive relation (nodes.drop count)
  | 0, nodes, consecutive => by simpa using consecutive
  | _ + 1, [], _consecutive => by simp [Consecutive]
  | count + 1, _ :: tail, consecutive =>
      Consecutive.drop count tail (by
        cases tail with
        | nil => simp [Consecutive]
        | cons _ _ => exact consecutive.2)

theorem Consecutive.append {relation : α -> α -> Prop} :
    forall (left right : List α),
      Consecutive relation left ->
        Consecutive relation right ->
          (forall previous next,
            left.getLast? = some previous ->
              right.head? = some next -> relation previous next) ->
            Consecutive relation (left ++ right)
  | [], right, _leftCons, rightCons, _join => by simpa using rightCons
  | [previous], right, _leftCons, rightCons, join => by
      cases right with
      | nil => simp [Consecutive]
      | cons next rest =>
          exact ⟨join previous next rfl rfl, rightCons⟩
  | previous :: middle :: rest, right, leftCons, rightCons, join =>
      ⟨leftCons.1, Consecutive.append (middle :: rest) right leftCons.2 rightCons
        (fun older newer olderLast newerHead =>
          join older newer (by simpa using olderLast) newerHead)⟩

theorem Consecutive.reverse {relation : α -> α -> Prop}
    (symmetric : forall left right, relation left right -> relation right left) :
    forall nodes : List α,
      Consecutive relation nodes -> Consecutive relation nodes.reverse
  | [], _consecutive => by simp [Consecutive]
  | [_], _consecutive => by simp [Consecutive]
  | previous :: next :: rest, consecutive => by
      have tailReverse :=
        Consecutive.reverse symmetric (next :: rest) consecutive.2
      have reverseEq :
          (previous :: next :: rest).reverse =
            (next :: rest).reverse ++ [previous] := by
        simp [List.reverse_cons]
      rw [reverseEq]
      apply Consecutive.snoc tailReverse
      intro older olderLast
      have lastEq : (next :: rest).reverse.getLast? = some next := by
        simp [List.getLast?_reverse]
      rw [lastEq] at olderLast
      cases olderLast
      exact symmetric previous next consecutive.1

theorem Consecutive.mono {r s : α -> α -> Prop}
    (included : forall left right, r left right -> s left right) :
    forall nodes : List α,
      Consecutive r nodes -> Consecutive s nodes
  | [] => fun _ => by simp [Consecutive]
  | [_] => fun _ => by simp [Consecutive]
  | left :: right :: rest => fun consecutive =>
      ⟨included left right consecutive.1,
        Consecutive.mono included (right :: rest) consecutive.2⟩

/-- Drop an internal vertex whose two neighbours are already related.
Oxford uses this when a blocked non-collider sits between two DAG-adjacent
vertices: the shorter walk remains a consecutive adjacency trail. -/
theorem Consecutive.delete_middle {relation : α -> α -> Prop} :
    forall (before : List α) (previous middle next : α) (after : List α),
      Consecutive relation
          (before ++ previous :: middle :: next :: after) ->
        relation previous next ->
          Consecutive relation (before ++ previous :: next :: after)
  | [], _previous, _middle, _next, _after, consecutive, bridge =>
      ⟨bridge, consecutive.2.2⟩
  | [_head], _previous, _middle, _next, _after, consecutive, bridge =>
      ⟨consecutive.1, ⟨bridge, consecutive.2.2.2⟩⟩
  | _head :: second :: rest, previous, middle, next, after, consecutive,
      bridge =>
      ⟨consecutive.1,
        Consecutive.delete_middle (second :: rest) previous middle next after
          consecutive.2 bridge⟩

theorem Adjacent.symm {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {left right : SeparationNode S}
    (adjacent : Adjacent G mutilation left right) :
    Adjacent G mutilation right left :=
  Or.symm adjacent

theorem IsCollider.symm {G : ObservedGraph S}
    {mutilation : GraphMutilation S}
    {previous middle next : SeparationNode S}
    (collider : IsCollider G mutilation previous middle next) :
    IsCollider G mutilation next middle previous :=
  ⟨collider.2, collider.1⟩

theorem TripleActive.symm {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {previous middle next : SeparationNode S}
    (active : TripleActive G mutilation conditioned previous middle next) :
    TripleActive G mutilation conditioned next middle previous := by
  rcases active with colliderAndActivated | nonColliderAndOpen
  · exact Or.inl ⟨colliderAndActivated.1.symm, colliderAndActivated.2⟩
  · exact Or.inr ⟨fun collider => nonColliderAndOpen.1 collider.symm,
      nonColliderAndOpen.2⟩

theorem InternalTriplesActive.take {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {nodes : List (SeparationNode S)}
    (active : InternalTriplesActive G mutilation conditioned nodes)
    (count : Nat) :
    InternalTriplesActive G mutilation conditioned (nodes.take count) := by
  induction active generalizing count with
  | nil =>
      simp
      exact InternalTriplesActive.nil
  | singleton node =>
      cases count with
      | zero =>
          simp [List.take]
          exact InternalTriplesActive.nil
      | succ _ =>
          simp [List.take]
          exact InternalTriplesActive.singleton node
  | pair left right =>
      cases count with
      | zero =>
          simp [List.take]
          exact InternalTriplesActive.nil
      | succ rest =>
          cases rest with
          | zero =>
              simp [List.take]
              exact InternalTriplesActive.singleton left
          | succ _ =>
              simp [List.take]
              exact InternalTriplesActive.pair left right
  | @step previous middle next restNodes triple rest ih =>
      cases count with
      | zero =>
          simp [List.take]
          exact InternalTriplesActive.nil
      | succ restCount =>
          cases restCount with
          | zero =>
              simp [List.take]
              exact InternalTriplesActive.singleton previous
          | succ restCount' =>
              cases restCount' with
              | zero =>
                  simp [List.take]
                  exact InternalTriplesActive.pair previous middle
              | succ remaining =>
                  simp [List.take]
                  exact InternalTriplesActive.step triple (ih (remaining + 2))

def adjacentBool (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right : SeparationNode S) : Bool :=
  G.expandedMutilatedEdge mutilation left right ||
    G.expandedMutilatedEdge mutilation right left

theorem Adjacent_iff_adjacentBool (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right : SeparationNode S) :
    Adjacent G mutilation left right <->
      adjacentBool G mutilation left right = true := by
  simp [Adjacent, adjacentBool, Bool.or_eq_true]

theorem adjacentBool_symm (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right : SeparationNode S) :
    adjacentBool G mutilation left right =
      adjacentBool G mutilation right left := by
  simp [adjacentBool, Bool.or_comm]

def isColliderBool (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (previous middle next : SeparationNode S) : Bool :=
  G.expandedMutilatedEdge mutilation previous middle &&
    G.expandedMutilatedEdge mutilation next middle

theorem IsCollider_iff_isColliderBool (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    (previous middle next : SeparationNode S) :
    IsCollider G mutilation previous middle next <->
      isColliderBool G mutilation previous middle next = true := by
  simp [IsCollider, isColliderBool, Bool.and_eq_true]

def tripleActiveBool (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (conditioned : NodeSet S)
    (previous middle next : SeparationNode S) : Bool :=
  if isColliderBool G mutilation previous middle next then
    G.ancestorOf mutilation conditioned middle
  else
    Bool.not (ObservedGraph.blockedBy conditioned middle)

theorem TripleActive_iff_tripleActiveBool (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (previous middle next : SeparationNode S) :
    TripleActive G mutilation conditioned previous middle next <->
      tripleActiveBool G mutilation conditioned previous middle next = true := by
  unfold TripleActive tripleActiveBool ColliderActivated NonColliderOpen
  cases colliderValue : isColliderBool G mutilation previous middle next with
  | true =>
      have collider :=
        (IsCollider_iff_isColliderBool G mutilation previous middle next).mpr
          colliderValue
      simp
      constructor
      · intro active
        rcases active with colliderAndActivated | nonColliderAndOpen
        · exact colliderAndActivated.2
        · exact (nonColliderAndOpen.1 collider).elim
      · intro activated
        exact Or.inl ⟨collider, activated⟩
  | false =>
      have notCollider :
          Not (IsCollider G mutilation previous middle next) := by
        intro collider
        have colliderTrue :=
          (IsCollider_iff_isColliderBool G mutilation previous middle next).mp
            collider
        rw [colliderValue] at colliderTrue
        contradiction
      simp
      constructor
      · intro active
        rcases active with colliderAndActivated | nonColliderAndOpen
        · exact (notCollider colliderAndActivated.1).elim
        · exact nonColliderAndOpen.2
      · intro openMiddle
        exact Or.inr ⟨notCollider, openMiddle⟩

/-- Count undirected DAG non-adjacencies along a moral walk. -/
def marriedCount (G : ObservedGraph S) (mutilation : GraphMutilation S) :
    List (SeparationNode S) -> Nat
  | [] => 0
  | [_] => 0
  | left :: right :: rest =>
      (if adjacentBool G mutilation left right then 0 else 1) +
        marriedCount G mutilation (right :: rest)

/-- Count internally inactive triples along a candidate active path. -/
def inactiveColliderCount (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S) :
    List (SeparationNode S) -> Nat
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | previous :: middle :: next :: rest =>
      (if tripleActiveBool G mutilation conditioned previous middle next then
        0 else 1) +
        inactiveColliderCount G mutilation conditioned
          (middle :: next :: rest)

/-- Zero married count means every consecutive pair is already a DAG
adjacency.  The Boolean count is computed from `adjacentBool` alone. -/
theorem Consecutive.adjacent_of_marriedCount_zero
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {nodes : List (SeparationNode S)}
    (married : marriedCount G mutilation nodes = 0) :
    Consecutive (Adjacent G mutilation) nodes := by
  match nodes with
  | [] => simp [Consecutive]
  | [_] => simp [Consecutive]
  | left :: right :: rest =>
      simp [marriedCount] at married
      cases adjacentValue :
          adjacentBool G mutilation left right with
      | false =>
          simp [adjacentValue] at married
      | true =>
          simp [adjacentValue] at married
          exact ⟨(Adjacent_iff_adjacentBool G mutilation left right).mpr
              adjacentValue,
            Consecutive.adjacent_of_marriedCount_zero married⟩

theorem InternalTriplesActive.of_inactiveColliderCount_zero
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S} :
    forall nodes : List (SeparationNode S),
      inactiveColliderCount G mutilation conditioned nodes = 0 ->
        InternalTriplesActive G mutilation conditioned nodes
  | [] => fun _ => InternalTriplesActive.nil
  | [_] => fun _ => InternalTriplesActive.singleton _
  | [_, _] => fun _ => InternalTriplesActive.pair _ _
  | previous :: middle :: next :: rest => by
      intro inactive
      simp [inactiveColliderCount] at inactive
      cases activeValue :
          tripleActiveBool G mutilation conditioned previous middle next with
      | false =>
          simp [activeValue] at inactive
      | true =>
          simp [activeValue] at inactive
          exact InternalTriplesActive.step
            ((TripleActive_iff_tripleActiveBool G mutilation conditioned
              previous middle next).mpr activeValue)
            (InternalTriplesActive.of_inactiveColliderCount_zero
              (middle :: next :: rest) inactive)

theorem marriedCount_cons_adjacent {G : ObservedGraph S}
    {mutilation : GraphMutilation S}
    {left right : SeparationNode S} {rest : List (SeparationNode S)}
    (adjacent : adjacentBool G mutilation left right = true) :
    marriedCount G mutilation (left :: right :: rest) =
      marriedCount G mutilation (right :: rest) := by
  simp [marriedCount, adjacent]

theorem marriedCount_cons_married {G : ObservedGraph S}
    {mutilation : GraphMutilation S}
    {left right : SeparationNode S} {rest : List (SeparationNode S)}
    (notAdjacent : adjacentBool G mutilation left right = false) :
    marriedCount G mutilation (left :: right :: rest) =
      marriedCount G mutilation (right :: rest) + 1 := by
  simp [marriedCount, notAdjacent]
  exact Nat.add_comm _ _

theorem inactiveColliderCount_cons_active {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {previous middle next : SeparationNode S}
    {rest : List (SeparationNode S)}
    (active : tripleActiveBool G mutilation conditioned previous middle next =
      true) :
    inactiveColliderCount G mutilation conditioned
        (previous :: middle :: next :: rest) =
      inactiveColliderCount G mutilation conditioned
        (middle :: next :: rest) := by
  simp [inactiveColliderCount, active]

theorem inactiveColliderCount_cons_inactive {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {previous middle next : SeparationNode S}
    {rest : List (SeparationNode S)}
    (inactive : tripleActiveBool G mutilation conditioned previous middle next =
      false) :
    inactiveColliderCount G mutilation conditioned
        (previous :: middle :: next :: rest) =
      inactiveColliderCount G mutilation conditioned
        (middle :: next :: rest) + 1 := by
  simp [inactiveColliderCount, inactive]
  exact Nat.add_comm _ _


/-- An internally active trail has inactive-count zero. -/
theorem inactiveColliderCount_eq_zero_of_internal_active
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S} :
    forall (nodes : List (SeparationNode S)),
      InternalTriplesActive G mutilation conditioned nodes ->
        inactiveColliderCount G mutilation conditioned nodes = 0
  | _, InternalTriplesActive.nil => rfl
  | _, InternalTriplesActive.singleton _ => rfl
  | _, InternalTriplesActive.pair _ _ => rfl
  | _, InternalTriplesActive.step triple rest => by
      have tripleTrue :=
        (TripleActive_iff_tripleActiveBool G mutilation conditioned
          _ _ _).mp triple
      simp [inactiveColliderCount, tripleTrue]
      exact inactiveColliderCount_eq_zero_of_internal_active _ rest

theorem take_append_two {α} (xs : List α) (a b : α) (cs : List α) :
    (xs ++ a :: b :: cs).take (xs.length + 2) = xs ++ [a, b] := by
  induction xs with
  | nil => simp [List.take]
  | cons x xs ih =>
      simp [List.length_cons]
      exact ih

/-- The first inactive triple, together with the proof that every earlier
window is active. -/
theorem exists_inactive_split
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S} :
    forall nodes : List (SeparationNode S),
      0 < inactiveColliderCount G mutilation conditioned nodes ->
        Exists fun before => Exists fun previous => Exists fun middle =>
          Exists fun next => Exists fun after =>
            nodes = before ++ previous :: middle :: next :: after /\
              tripleActiveBool G mutilation conditioned previous middle next =
                false /\
                inactiveColliderCount G mutilation conditioned
                  (before ++ previous :: [middle]) = 0
  | [] => fun inactive => by simp [inactiveColliderCount] at inactive
  | [_] => fun inactive => by simp [inactiveColliderCount] at inactive
  | [_, _] => fun inactive => by simp [inactiveColliderCount] at inactive
  | previous :: middle :: next :: rest => fun inactive => by
      cases activeValue :
          tripleActiveBool G mutilation conditioned previous middle next with
      | false =>
          exact ⟨[], previous, middle, next, rest, rfl, activeValue, by
            simp [inactiveColliderCount]⟩
      | true =>
          have restInactive :
              0 < inactiveColliderCount G mutilation conditioned
                (middle :: next :: rest) := by
            rw [inactiveColliderCount_cons_active activeValue] at inactive
            exact inactive
          rcases exists_inactive_split (middle :: next :: rest) restInactive with
            ⟨before, laterPrev, laterMid, laterNext, after, split,
              inactiveTriple, prefixZero⟩
          refine ⟨previous :: before, laterPrev, laterMid, laterNext, after,
            by simp [split], inactiveTriple, ?_⟩
          cases hbefore : before with
          | nil =>
              have splitEq :
                  middle :: next :: rest =
                    laterPrev :: laterMid :: laterNext :: after := by
                simpa [hbefore] using split
              injection splitEq with eq1 rest1
              subst laterPrev
              injection rest1 with eq2 rest2
              subst laterMid
              simp [inactiveColliderCount, activeValue]
          | cons head tail =>
              have split' :
                  middle :: next :: rest =
                    head :: (tail ++ laterPrev :: laterMid ::
                      laterNext :: after) := by
                simpa [hbefore, List.cons_append] using split
              injection split' with headEq restEq
              subst head
              have takeTwo :=
                take_append_two tail laterPrev laterMid
                  (laterNext :: after)
              rw [← restEq] at takeTwo
              have unfold :
                  (next :: rest).take (tail.length + 2) =
                    next :: rest.take (tail.length + 1) := by
                change (next :: rest).take (Nat.succ (tail.length + 1)) = _
                rfl
              have takeEq :
                  tail ++ [laterPrev, laterMid] =
                    next :: rest.take (tail.length + 1) :=
                takeTwo.symm.trans unfold
              have nest :
                  previous :: middle :: tail ++ [laterPrev, laterMid] =
                    previous :: middle :: (tail ++ [laterPrev, laterMid]) := by
                rw [List.cons_append, List.cons_append]
              rw [nest, takeEq, inactiveColliderCount_cons_active activeValue]
              have prefixZero' :
                  inactiveColliderCount G mutilation conditioned
                    (middle :: (tail ++ [laterPrev, laterMid])) = 0 := by
                simpa [hbefore, List.cons_append] using prefixZero
              simpa [takeEq] using prefixZero'

/--
Every consecutive window is either a collider or has an open middle.
Expansions of moral walks satisfy this because original moral vertices are
open and inserted common children appear exactly as collider middles.
Cycle deletion preserves the property along DAG-adjacent trails: copied
windows are original, and a splice at a blocked vertex reuses both
original incoming parents.
-/
def TripleOpenOrCollider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S) :
    List (SeparationNode S) -> Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | previous :: middle :: next :: rest =>
      (isColliderBool G mutilation previous middle next = true ∨
        ObservedGraph.blockedBy conditioned middle = false) ∧
      TripleOpenOrCollider G mutilation conditioned (middle :: next :: rest)

theorem TripleOpenOrCollider.of_every_window {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S} :
    forall nodes : List (SeparationNode S),
      (forall (before : List (SeparationNode S))
        (previous middle next : SeparationNode S)
        (after : List (SeparationNode S)),
        nodes = before ++ previous :: middle :: next :: after ->
          isColliderBool G mutilation previous middle next = true ∨
            ObservedGraph.blockedBy conditioned middle = false) ->
        TripleOpenOrCollider G mutilation conditioned nodes
  | [], _every => trivial
  | [_], _every => trivial
  | [_, _], _every => trivial
  | previous :: middle :: next :: rest, every =>
      ⟨every [] previous middle next rest rfl,
        TripleOpenOrCollider.of_every_window (middle :: next :: rest)
          (fun before p m n after eq =>
            every (previous :: before) p m n after (by
              rw [eq, List.cons_append]))⟩

theorem TripleOpenOrCollider.of_append {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S} :
    forall (before : List (SeparationNode S))
      (previous middle next : SeparationNode S)
      (after : List (SeparationNode S)),
      TripleOpenOrCollider G mutilation conditioned
          (before ++ previous :: middle :: next :: after) ->
        isColliderBool G mutilation previous middle next = true ∨
          ObservedGraph.blockedBy conditioned middle = false
  | [], previous, middle, next, after, h => h.1
  | head :: tail, previous, middle, next, after, h => by
      have hcons : TripleOpenOrCollider G mutilation conditioned
          (head :: (tail ++ previous :: middle :: next :: after)) := by
        simpa [List.cons_append] using h
      have three :
          Exists fun m => Exists fun n => Exists fun more =>
            tail ++ previous :: middle :: next :: after = m :: n :: more := by
        cases tail with
        | nil => exact ⟨previous, middle, next :: after, rfl⟩
        | cons a as =>
            cases as with
            | nil =>
                exact ⟨a, previous, middle :: next :: after, rfl⟩
            | cons b bs =>
                exact ⟨a, b, bs ++ previous :: middle :: next :: after, by
                  simp [List.cons_append]⟩
      rcases three with ⟨m, n, more, eq⟩
      have h3 : TripleOpenOrCollider G mutilation conditioned
          (head :: m :: n :: more) := by
        simpa [eq] using hcons
      exact TripleOpenOrCollider.of_append tail previous middle next after
        (by simpa [eq] using h3.2)

theorem TripleOpenOrCollider.tail {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {head : SeparationNode S} {nodes : List (SeparationNode S)}
    (h : TripleOpenOrCollider G mutilation conditioned (head :: nodes)) :
    TripleOpenOrCollider G mutilation conditioned nodes := by
  cases nodes with
  | nil => trivial
  | cons _m rest =>
      cases rest with
      | nil => trivial
      | cons _n _more => exact h.2

theorem TripleOpenOrCollider.suffix_of_append {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S} :
    forall (before : List (SeparationNode S)) (node : SeparationNode S)
      (after : List (SeparationNode S)),
      TripleOpenOrCollider G mutilation conditioned
          (before ++ node :: after) ->
        TripleOpenOrCollider G mutilation conditioned (node :: after)
  | [], node, after, h => by simpa using h
  | head :: tail, node, after, h =>
      TripleOpenOrCollider.suffix_of_append tail node after
        (TripleOpenOrCollider.tail (by simpa [List.cons_append] using h))

/-- Concatenate two internally active trails that share the displayed
join triple `(previous, middle, next)`.  Induction on `before` avoids
matching `InternalTriplesActive` against an unreduced `++`. -/
theorem InternalTriplesActive.append_triple
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S}
    (before : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (left : InternalTriplesActive G mutilation conditioned
      (before ++ previous :: [middle]))
    (join : TripleActive G mutilation conditioned previous middle next)
    (right : InternalTriplesActive G mutilation conditioned
      (middle :: next :: after)) :
    InternalTriplesActive G mutilation conditioned
      (before ++ previous :: middle :: next :: after) := by
  induction before with
  | nil =>
      exact InternalTriplesActive.step join right
  | cons head tail ih =>
      have leftTail :
          InternalTriplesActive G mutilation conditioned
            (tail ++ previous :: [middle]) :=
        InternalTriplesActive.tail (by
          simpa [List.cons_append] using left)
      have recActive := ih leftTail
      cases hsplit : tail ++ previous :: [middle] with
      | nil =>
          have hlen := congrArg List.length hsplit
          simp [List.length_append] at hlen
      | cons second restNodes =>
          have restLen : 0 < restNodes.length := by
            have hlen := congrArg List.length hsplit
            simp [List.length_append] at hlen
            omega
          cases hrest : restNodes with
          | nil =>
              simp [hrest] at restLen
          | cons third more =>
              have left3 :
                  InternalTriplesActive G mutilation conditioned
                    (head :: second :: third :: more) := by
                have eq :
                    head :: tail ++ previous :: [middle] =
                      head :: second :: third :: more := by
                  rw [List.cons_append, hsplit, hrest]
                simpa [eq] using left
              have first :=
                InternalTriplesActive.triple_of_append [] more head second
                  third left3
              have full_tail :
                  tail ++ previous :: middle :: next :: after =
                    second :: third :: more ++ next :: after := by
                have assoc :
                    (tail ++ previous :: [middle]) ++ (next :: after) =
                      tail ++ (previous :: [middle] ++ next :: after) :=
                  List.append_assoc _ _ _
                have inner :
                    previous :: [middle] ++ next :: after =
                      previous :: middle :: next :: after := rfl
                calc
                  tail ++ previous :: middle :: next :: after =
                      tail ++ (previous :: middle :: next :: after) := rfl
                  _ = tail ++ (previous :: [middle] ++ next :: after) := by
                    rw [inner]
                  _ = (tail ++ previous :: [middle]) ++ next :: after :=
                    assoc.symm
                  _ = second :: third :: more ++ next :: after := by
                    rw [hsplit, hrest]
              have rec' :
                  InternalTriplesActive G mutilation conditioned
                    (second :: third :: (more ++ next :: after)) := by
                have eq :
                    tail ++ previous :: middle :: next :: after =
                      second :: third :: (more ++ next :: after) := by
                  rw [full_tail, List.cons_append, List.cons_append]
                simpa [eq] using recActive
              have goalEq :
                  head :: tail ++ previous :: middle :: next :: after =
                    head :: second :: third :: (more ++ next :: after) := by
                rw [List.cons_append, full_tail, List.cons_append,
                  List.cons_append]
              rw [goalEq]
              exact InternalTriplesActive.step first rec'

theorem InternalTriplesActive.reverse {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S} :
    forall nodes : List (SeparationNode S),
      InternalTriplesActive G mutilation conditioned nodes ->
        InternalTriplesActive G mutilation conditioned nodes.reverse
  | [], _active => by
      rw [List.reverse_nil]
      exact InternalTriplesActive.nil
  | [node], active => by
      cases active
      rw [List.reverse_cons, List.reverse_nil]
      exact InternalTriplesActive.singleton node
  | [leftNode, rightNode], active => by
      cases active
      rw [List.reverse_cons, List.reverse_cons, List.reverse_nil]
      exact InternalTriplesActive.pair rightNode leftNode
  | previous :: middle :: next :: rest, active => by
      cases active with
      | step triple restActive =>
          have ih :=
            InternalTriplesActive.reverse (middle :: next :: rest) restActive
          have restRev :
              (middle :: next :: rest).reverse =
                rest.reverse ++ next :: [middle] := by
            rw [List.reverse_cons, List.reverse_cons, List.append_assoc]
            rfl
          rw [List.reverse_cons, restRev]
          have shape :
              rest.reverse ++ next :: [middle] ++ [previous] =
                rest.reverse ++ next :: middle :: previous :: [] := by
            rw [List.append_assoc]
            rfl
          rw [shape]
          exact InternalTriplesActive.append_triple rest.reverse next middle
            previous [] (by simpa [restRev] using ih) triple.symm
            (InternalTriplesActive.pair middle previous)

theorem InternalTriplesActive.glue_at
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S}
    (left : List (SeparationNode S)) (shared : SeparationNode S)
    (rightTail : List (SeparationNode S))
    (leftActive : InternalTriplesActive G mutilation conditioned
      (left ++ [shared]))
    (rightActive : InternalTriplesActive G mutilation conditioned
      (shared :: rightTail))
    (join : forall pred succ,
      left.getLast? = some pred ->
        rightTail.head? = some succ ->
          TripleActive G mutilation conditioned pred shared succ) :
    InternalTriplesActive G mutilation conditioned
      (left ++ shared :: rightTail) := by
  cases left with
  | nil =>
      simpa using rightActive
  | cons head tail =>
      cases rightTail with
      | nil =>
          simpa using leftActive
      | cons succ rest =>
          have predLast : Exists fun pred =>
              (head :: tail).getLast? = some pred := by
            clear leftActive rightActive join
            induction tail generalizing head with
            | nil => exact ⟨head, rfl⟩
            | cons y ys ih => exact ih y
          rcases predLast with ⟨pred, predEq⟩
          have joinTriple := join pred succ predEq rfl
          rcases List.getLast?_eq_some_iff.mp predEq with ⟨init, splitLeft⟩
          have leftEq :
              head :: tail ++ [shared] = init ++ pred :: [shared] := by
            rw [splitLeft, List.append_assoc]
            rfl
          have leftActive' :
              InternalTriplesActive G mutilation conditioned
                (init ++ pred :: [shared]) := by
            simpa [leftEq] using leftActive
          have fullEq :
              head :: tail ++ shared :: succ :: rest =
                init ++ pred :: shared :: succ :: rest := by
            rw [splitLeft, List.append_assoc]
            rfl
          rw [fullEq]
          exact InternalTriplesActive.append_triple init pred shared succ rest
            leftActive' joinTriple rightActive

theorem InternalTriplesActive.suffix_append
    {G : ObservedGraph S} {mutilation : GraphMutilation S}
    {conditioned : NodeSet S} :
    forall (before : List (SeparationNode S)) (node : SeparationNode S)
      (after : List (SeparationNode S)),
      InternalTriplesActive G mutilation conditioned
          (before ++ node :: after) ->
        InternalTriplesActive G mutilation conditioned (node :: after)
  | [], node, after, active => by simpa using active
  | head :: tail, node, after, active =>
      InternalTriplesActive.suffix_append tail node after (by
        simpa [List.cons_append] using active.tail)

theorem Consecutive.overlap_glue {relation : α -> α -> Prop}
    {front back : List α} {v : α}
    {frontBefore frontAfter backBefore backAfter : List α}
    (frontCons : Consecutive relation front)
    (backCons : Consecutive relation back)
    (frontSplit : front = frontBefore ++ v :: frontAfter)
    (backSplit : back = backBefore ++ v :: backAfter) :
    Consecutive relation (frontBefore ++ v :: backAfter) := by
  have leftCons : Consecutive relation (frontBefore ++ [v]) := by
    rw [frontSplit] at frontCons
    exact Consecutive.prefix_append frontBefore v frontAfter frontCons
  have suffixCons : Consecutive relation (v :: backAfter) := by
    have dropped := Consecutive.drop backBefore.length back backCons
    have dropEq : back.drop backBefore.length = v :: backAfter := by
      rw [backSplit, drop_append_length]
    simpa [dropEq] using dropped
  have lastLeft : (frontBefore ++ [v]).getLast? = some v := by
    induction frontBefore with
    | nil => simp
    | cons _head tail ih =>
        cases tail with
        | nil => simp
        | cons _ _ => simp [List.getLast?_cons]
  cases htail : backAfter with
  | nil =>
      simpa [htail] using leftCons
  | cons succ more =>
      have suffix' : Consecutive relation (v :: succ :: more) := by
        simpa [htail] using suffixCons
      have join : relation v succ := suffix'.1
      have rightCons : Consecutive relation (succ :: more) := suffix'.2
      have glued :
          Consecutive relation (frontBefore ++ [v] ++ (succ :: more)) :=
        Consecutive.append (frontBefore ++ [v]) (succ :: more) leftCons
          rightCons
          (fun previous newer prevLast newerHead => by
            have prevEq : previous = v :=
              Option.some.inj (prevLast.symm.trans lastLeft)
            have newerEq : newer = succ :=
              Option.some.inj (newerHead.symm.trans rfl)
            rw [prevEq, newerEq]
            exact join)
      have glueEq :
          frontBefore ++ [v] ++ (succ :: more) =
            frontBefore ++ v :: succ :: more := by
        rw [List.append_assoc]
        rfl
      simpa [glueEq] using glued

def ActivePath.singleton (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (node : SeparationNode S)
    (openNode : ObservedGraph.blockedBy conditioned node = false) :
    ActivePath G mutilation conditioned node node where
  nodes := [node]
  starts := rfl
  finishes := rfl
  simple := List.nodup_cons.mpr ⟨fun mem => List.not_mem_nil mem, List.nodup_nil⟩
  adjacent := by simp [Consecutive]
  source_open := openNode
  target_open := openNode
  internal_active := InternalTriplesActive.singleton node

def ActivePath.ofPair (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {left right : SeparationNode S}
    (adjacent : Adjacent G mutilation left right)
    (different : left ≠ right)
    (leftOpen : ObservedGraph.blockedBy conditioned left = false)
    (rightOpen : ObservedGraph.blockedBy conditioned right = false) :
    ActivePath G mutilation conditioned left right where
  nodes := [left, right]
  starts := rfl
  finishes := rfl
  simple := by
    refine List.nodup_cons.mpr ⟨?_, by simp⟩
    intro member
    simp at member
    exact different member
  adjacent := ⟨adjacent, by simp [Consecutive]⟩
  source_open := leftOpen
  target_open := rightOpen
  internal_active := InternalTriplesActive.pair left right

/--
A bidirected edge between distinct open observed endpoints is an active
path through the corresponding explicit latent pair.  Incoming mutilation
must leave both endpoints, matching `G_{\overline{X}}` when those
endpoints lie outside `X`.
-/
def ActivePath.ofBidirected (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {left right : Fin S.count}
    (hedge : G.bidirected left right = true)
    (different : left ≠ right)
    (leftOpen : ObservedGraph.blockedBy conditioned (.observed left) = false)
    (rightOpen : ObservedGraph.blockedBy conditioned (.observed right) = false)
    (leftIncoming : mutilation.removeIncoming left = false)
    (rightIncoming : mutilation.removeIncoming right = false) :
    ActivePath G mutilation conditioned
      (.observed left) (.observed right) where
  nodes := [.observed left, .latentPair left right, .observed right]
  starts := rfl
  finishes := rfl
  simple := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, by simp⟩⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with hlat | hobs
      · cases hlat
      · have heq : left = right := by
          simpa using hobs
        exact different heq
    · intro hmem
      cases List.mem_singleton.mp hmem
  adjacent := by
    constructor
    · refine Or.inr ?_
      simp [ObservedGraph.expandedMutilatedEdge, hedge, leftIncoming, finBeq]
    · constructor
      · refine Or.inl ?_
        simp [ObservedGraph.expandedMutilatedEdge, hedge, rightIncoming, finBeq]
      · simp [Consecutive]
  source_open := leftOpen
  target_open := rightOpen
  internal_active := by
    refine InternalTriplesActive.step ?_ (InternalTriplesActive.pair _ _)
    refine Or.inr ⟨?_, rfl⟩
    intro hcol
    have incoming :
        G.expandedMutilatedEdge mutilation (.observed left)
          (.latentPair left right) = true := hcol.1
    simp [ObservedGraph.expandedMutilatedEdge] at incoming

/--
Two bidirected edges sharing a conditioned vertex form an active path
between the open endpoints: the middle is an activated collider, and the
latent-pair middles are never blocked.
-/
def ActivePath.ofBidirectedCollider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {left collider right : Fin S.count}
    (hedgeLeft : G.bidirected left collider = true)
    (hedgeRight : G.bidirected collider right = true)
    (leftNeCollider : left ≠ collider)
    (rightNeCollider : right ≠ collider)
    (leftNeRight : left ≠ right)
    (leftOpen : ObservedGraph.blockedBy conditioned (.observed left) = false)
    (rightOpen : ObservedGraph.blockedBy conditioned (.observed right) =
      false)
    (leftIncoming : mutilation.removeIncoming left = false)
    (colliderIncoming : mutilation.removeIncoming collider = false)
    (rightIncoming : mutilation.removeIncoming right = false)
    (activated : ColliderActivated G mutilation conditioned
      (.observed collider)) :
    ActivePath G mutilation conditioned
      (.observed left) (.observed right) where
  nodes :=
    [.observed left, .latentPair left collider, .observed collider,
      .latentPair collider right, .observed right]
  starts := rfl
  finishes := rfl
  simple := by
    refine List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_,
        List.nodup_cons.mpr ⟨?_,
          List.nodup_cons.mpr ⟨?_, by simp⟩⟩⟩⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with hlat | hrest
      · cases hlat
      rcases List.mem_cons.mp hrest with hcol | hrest2
      · have heq : left = collider := by simpa using hcol
        exact leftNeCollider heq
      rcases List.mem_cons.mp hrest2 with hlat2 | hrest3
      · cases hlat2
      rcases List.mem_cons.mp hrest3 with hright | hnil
      · have heq : left = right := by simpa using hright
        exact leftNeRight heq
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      rcases List.mem_cons.mp hmem with hcol | hrest
      · cases hcol
      rcases List.mem_cons.mp hrest with hlat2 | hrest2
      · injection hlat2 with h1 h2
        exact leftNeRight (h1.trans h2)
      rcases List.mem_cons.mp hrest2 with hright | hnil
      · cases hright
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      rcases List.mem_cons.mp hmem with hlat2 | hrest
      · cases hlat2
      rcases List.mem_cons.mp hrest with hright | hnil
      · have heq : collider = right := by simpa using hright
        exact rightNeCollider heq.symm
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      cases List.mem_singleton.mp hmem
  adjacent := by
    constructor
    · refine Or.inr ?_
      simp [ObservedGraph.expandedMutilatedEdge, hedgeLeft, leftIncoming,
        finBeq]
    · constructor
      · refine Or.inl ?_
        simp [ObservedGraph.expandedMutilatedEdge, hedgeLeft,
          colliderIncoming, finBeq]
      · constructor
        · refine Or.inr ?_
          simp [ObservedGraph.expandedMutilatedEdge, hedgeRight,
            colliderIncoming, finBeq]
        · constructor
          · refine Or.inl ?_
            simp [ObservedGraph.expandedMutilatedEdge, hedgeRight,
              rightIncoming, finBeq]
          · simp [Consecutive]
  source_open := leftOpen
  target_open := rightOpen
  internal_active := by
    refine InternalTriplesActive.step ?_ ?_
    · refine Or.inr ⟨?_, rfl⟩
      intro hcol
      have incoming :
          G.expandedMutilatedEdge mutilation (.observed left)
            (.latentPair left collider) = true := hcol.1
      simp [ObservedGraph.expandedMutilatedEdge] at incoming
    · refine InternalTriplesActive.step ?_ ?_
      · refine Or.inl ⟨?_, activated⟩
        simp [IsCollider, ObservedGraph.expandedMutilatedEdge, hedgeLeft,
          hedgeRight, colliderIncoming, finBeq]
      · refine InternalTriplesActive.step ?_
          (InternalTriplesActive.pair _ _)
        refine Or.inr ⟨?_, rfl⟩
        intro hcol
        have incoming :
            G.expandedMutilatedEdge mutilation (.observed collider)
              (.latentPair collider right) = true := hcol.1
        simp [ObservedGraph.expandedMutilatedEdge] at incoming

/--
Two activated colliders joined by a bidirected edge form an active path
between the open endpoints.
-/
def ActivePath.ofTwoBidirectedColliders (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {left first second right : Fin S.count}
    (hedgeLeft : G.bidirected left first = true)
    (hedgeMid : G.bidirected first second = true)
    (hedgeRight : G.bidirected second right = true)
    (leftNeFirst : left ≠ first)
    (leftNeSecond : left ≠ second)
    (leftNeRight : left ≠ right)
    (firstNeSecond : first ≠ second)
    (firstNeRight : first ≠ right)
    (secondNeRight : second ≠ right)
    (leftOpen : ObservedGraph.blockedBy conditioned (.observed left) = false)
    (rightOpen : ObservedGraph.blockedBy conditioned (.observed right) =
      false)
    (leftIncoming : mutilation.removeIncoming left = false)
    (firstIncoming : mutilation.removeIncoming first = false)
    (secondIncoming : mutilation.removeIncoming second = false)
    (rightIncoming : mutilation.removeIncoming right = false)
    (activatedFirst : ColliderActivated G mutilation conditioned
      (.observed first))
    (activatedSecond : ColliderActivated G mutilation conditioned
      (.observed second)) :
    ActivePath G mutilation conditioned
      (.observed left) (.observed right) where
  nodes :=
    [.observed left, .latentPair left first, .observed first,
      .latentPair first second, .observed second,
      .latentPair second right, .observed right]
  starts := rfl
  finishes := rfl
  simple := by
    refine List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_,
        List.nodup_cons.mpr ⟨?_,
          List.nodup_cons.mpr ⟨?_,
            List.nodup_cons.mpr ⟨?_,
              List.nodup_cons.mpr ⟨?_, by simp⟩⟩⟩⟩⟩⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with hlat | hrest
      · cases hlat
      rcases List.mem_cons.mp hrest with h1 | hrest2
      · have heq : left = first := by simpa using h1
        exact leftNeFirst heq
      rcases List.mem_cons.mp hrest2 with hlat2 | hrest3
      · cases hlat2
      rcases List.mem_cons.mp hrest3 with h2 | hrest4
      · have heq : left = second := by simpa using h2
        exact leftNeSecond heq
      rcases List.mem_cons.mp hrest4 with hlat3 | hrest5
      · cases hlat3
      rcases List.mem_cons.mp hrest5 with hright | hnil
      · have heq : left = right := by simpa using hright
        exact leftNeRight heq
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      rcases List.mem_cons.mp hmem with h1 | hrest
      · cases h1
      rcases List.mem_cons.mp hrest with hlat2 | hrest2
      · injection hlat2 with ha hb
        exact leftNeSecond (ha.trans hb)
      rcases List.mem_cons.mp hrest2 with h2 | hrest3
      · cases h2
      rcases List.mem_cons.mp hrest3 with hlat3 | hrest4
      · injection hlat3 with ha _hb
        exact leftNeSecond ha
      rcases List.mem_cons.mp hrest4 with hright | hnil
      · cases hright
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      rcases List.mem_cons.mp hmem with hlat2 | hrest
      · cases hlat2
      rcases List.mem_cons.mp hrest with h2 | hrest2
      · have heq : first = second := by simpa using h2
        exact firstNeSecond heq
      rcases List.mem_cons.mp hrest2 with hlat3 | hrest3
      · cases hlat3
      rcases List.mem_cons.mp hrest3 with hright | hnil
      · have heq : first = right := by simpa using hright
        exact firstNeRight heq
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      rcases List.mem_cons.mp hmem with h2 | hrest
      · cases h2
      rcases List.mem_cons.mp hrest with hlat3 | hrest2
      · injection hlat3 with ha hb
        exact firstNeRight (ha.trans hb)
      rcases List.mem_cons.mp hrest2 with hright | hnil
      · cases hright
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      rcases List.mem_cons.mp hmem with hlat3 | hrest
      · cases hlat3
      rcases List.mem_cons.mp hrest with hright | hnil
      · have heq : second = right := by simpa using hright
        exact secondNeRight heq
      · exact (List.not_mem_nil hnil).elim
    · intro hmem
      cases List.mem_singleton.mp hmem
  adjacent := by
    constructor
    · refine Or.inr ?_
      simp [ObservedGraph.expandedMutilatedEdge, hedgeLeft, leftIncoming,
        finBeq]
    · constructor
      · refine Or.inl ?_
        simp [ObservedGraph.expandedMutilatedEdge, hedgeLeft, firstIncoming,
          finBeq]
      · constructor
        · refine Or.inr ?_
          simp [ObservedGraph.expandedMutilatedEdge, hedgeMid, firstIncoming,
            finBeq]
        · constructor
          · refine Or.inl ?_
            simp [ObservedGraph.expandedMutilatedEdge, hedgeMid,
              secondIncoming, finBeq]
          · constructor
            · refine Or.inr ?_
              simp [ObservedGraph.expandedMutilatedEdge, hedgeRight,
                secondIncoming, finBeq]
            · constructor
              · refine Or.inl ?_
                simp [ObservedGraph.expandedMutilatedEdge, hedgeRight,
                  rightIncoming, finBeq]
              · simp [Consecutive]
  source_open := leftOpen
  target_open := rightOpen
  internal_active := by
    refine InternalTriplesActive.step ?_ ?_
    · refine Or.inr ⟨?_, rfl⟩
      intro hcol
      have incoming :
          G.expandedMutilatedEdge mutilation (.observed left)
            (.latentPair left first) = true := hcol.1
      simp [ObservedGraph.expandedMutilatedEdge] at incoming
    · refine InternalTriplesActive.step ?_ ?_
      · refine Or.inl ⟨?_, activatedFirst⟩
        simp [IsCollider, ObservedGraph.expandedMutilatedEdge, hedgeLeft,
          hedgeMid, firstIncoming, finBeq]
      · refine InternalTriplesActive.step ?_ ?_
        · refine Or.inr ⟨?_, rfl⟩
          intro hcol
          have incoming :
              G.expandedMutilatedEdge mutilation (.observed first)
                (.latentPair first second) = true := hcol.1
          simp [ObservedGraph.expandedMutilatedEdge] at incoming
        · refine InternalTriplesActive.step ?_ ?_
          · refine Or.inl ⟨?_, activatedSecond⟩
            simp [IsCollider, ObservedGraph.expandedMutilatedEdge, hedgeMid,
              hedgeRight, secondIncoming, finBeq]
          · refine InternalTriplesActive.step ?_
              (InternalTriplesActive.pair _ _)
            refine Or.inr ⟨?_, rfl⟩
            intro hcol
            have incoming :
                G.expandedMutilatedEdge mutilation (.observed second)
                  (.latentPair second right) = true := hcol.1
            simp [ObservedGraph.expandedMutilatedEdge] at incoming

theorem Consecutive.map {r : α -> α -> Prop} {s : β -> β -> Prop}
    (f : α -> β)
    (preserve : forall left right, r left right -> s (f left) (f right)) :
    forall nodes, Consecutive r nodes -> Consecutive s (nodes.map f)
  | [] => fun _ => by simp [Consecutive]
  | [_] => fun _ => by simp [Consecutive]
  | left :: right :: rest => fun consecutive =>
      ⟨preserve left right consecutive.1,
        Consecutive.map f preserve (right :: rest) consecutive.2⟩

/-- Observed directed edges are expanded observed-observed edges. -/
theorem expandedMutilatedEdge_observed
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (parent child : Fin S.count) :
    G.expandedMutilatedEdge mutilation (.observed parent) (.observed child) =
      G.observedDirectedEdge mutilation parent child :=
  rfl

/-- A forward directed chain cannot be a collider: that would require a
2-cycle, contradicting the topological numbering. -/
theorem not_isCollider_of_forward_chain (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {previous middle next : Fin S.count}
    (forward : G.observedDirectedEdge mutilation middle next = true) :
    Not (IsCollider G mutilation
      (.observed previous) (.observed middle) (.observed next)) := by
  intro hcol
  simp [IsCollider, ObservedGraph.expandedMutilatedEdge] at hcol
  have hrev : S.directed next middle = true := hcol.2.1.1
  simp [ObservedGraph.observedDirectedEdge] at forward
  have hfwd : S.directed middle next = true := forward.1.1
  exact Nat.lt_irrefl middle.val
    (Nat.lt_trans (S.directed_earlier hfwd) (S.directed_earlier hrev))

/-- An outgoing parent cannot form a collider: that would require the
reverse directed edge, again a 2-cycle.  The third vertex may be a latent
pair, as in a fork from a directed child onto a bidirected edge. -/
theorem not_isCollider_of_outgoing (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {previous middle : Fin S.count} {next : SeparationNode S}
    (forward : G.observedDirectedEdge mutilation middle previous = true) :
    Not (IsCollider G mutilation
      (.observed previous) (.observed middle) next) := by
  intro hcol
  have back :
      G.expandedMutilatedEdge mutilation (.observed previous)
        (.observed middle) = true := hcol.1
  simp [ObservedGraph.expandedMutilatedEdge] at back
  have hrev : S.directed previous middle = true := back.1.1
  simp [ObservedGraph.observedDirectedEdge] at forward
  have hfwd : S.directed middle previous = true := forward.1.1
  exact Nat.lt_irrefl middle.val
    (Nat.lt_trans (S.directed_earlier hfwd) (S.directed_earlier hrev))

/-- An outgoing edge `middle → next` forbids a collider at `middle`, even
when the incoming neighbour is a latent pair. -/
theorem not_isCollider_of_outgoing_next (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {middle next : Fin S.count} {previous : SeparationNode S}
    (forward : G.observedDirectedEdge mutilation middle next = true) :
    Not (IsCollider G mutilation
      previous (.observed middle) (.observed next)) := by
  intro hcol
  have back :
      G.expandedMutilatedEdge mutilation (.observed next)
        (.observed middle) = true := hcol.2
  simp [ObservedGraph.expandedMutilatedEdge] at back
  have hrev : S.directed next middle = true := back.1.1
  simp [ObservedGraph.observedDirectedEdge] at forward
  have hfwd : S.directed middle next = true := forward.1.1
  exact Nat.lt_irrefl middle.val
    (Nat.lt_trans (S.directed_earlier hfwd) (S.directed_earlier hrev))

/-- Mapping a simple observed walk injects through the observed constructor. -/
theorem nodup_map_observed {S : ObservedSignature}
    {nodes : List (Fin S.count)} (simple : nodes.Nodup) :
    (nodes.map SeparationNode.observed).Nodup := by
  induction nodes with
  | nil =>
      simp
  | cons head tail ih =>
      have parts := List.nodup_cons.mp simple
      refine List.nodup_cons.mpr ⟨?_, ih parts.2⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨node, nodeMem, hobs⟩
      cases hobs
      exact parts.1 nodeMem

/-- Observed tagging is injective, so a latent pair never appears in the
image of an observed walk. -/
theorem not_mem_map_observed_latent {S : ObservedSignature}
    (left right : Fin S.count) (nodes : List (Fin S.count)) :
    SeparationNode.latentPair left right ∉
      nodes.map SeparationNode.observed := by
  intro hmem
  induction nodes with
  | nil =>
      simp at hmem
  | cons _head tail ih =>
      simp only [List.map, List.mem_cons] at hmem
      rcases hmem with same | later
      · cases same
      · exact ih later

/-- Recovering the original vertex from membership in an observed image. -/
theorem mem_of_observed_mem_map {S : ObservedSignature}
    {nodes : List (Fin S.count)} {n : Fin S.count}
    (h : SeparationNode.observed n ∈ nodes.map SeparationNode.observed) :
    n ∈ nodes := by
  induction nodes with
  | nil =>
      simp at h
  | cons head tail ih =>
      simp only [List.map, List.mem_cons] at h
      rcases h with same | later
      · cases same
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih later))

/-- Directed exact walks are consecutive in the undirected expanded graph. -/
theorem consecutive_adjacent_of_directed_walk (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target) :
    Consecutive (Adjacent G mutilation)
      (walk.nodes.map SeparationNode.observed) :=
  Consecutive.map SeparationNode.observed
    (fun left right hedge =>
      Or.inl (by
        simpa [expandedMutilatedEdge_observed] using hedge))
    walk.nodes walk.nodes_consecutive

/-- Internals of an all-open directed observed walk are active non-colliders. -/
theorem InternalTriplesActive.of_open_directed_walk
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (conditioned : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false) :
    InternalTriplesActive G mutilation conditioned
      (walk.nodes.map SeparationNode.observed) := by
  induction walk with
  | refl node =>
      simp [FiniteReachability.ExactWalk.nodes]
      exact InternalTriplesActive.singleton _
  | @step length source middle target first rest ih =>
      have openRest : forall n, n ∈ rest.nodes ->
          ObservedGraph.blockedBy conditioned (.observed n) = false := by
        intro n hn
        exact openNodes n
          (List.mem_cons.mpr (Or.inr hn))
      have ihRest := ih openRest
      cases rest with
      | refl endpoint =>
          simp [FiniteReachability.ExactWalk.nodes]
          exact InternalTriplesActive.pair _ _
      | @step restLength mid nxt dest second tail =>
          cases htail : tail.nodes with
          | nil =>
              exact (tail.nodes_ne_nil htail).elim
          | cons head after =>
              have hhead := tail.nodes_head
              simp [htail] at hhead
              subst head
              simp [FiniteReachability.ExactWalk.nodes, htail] at ihRest ⊢
              refine InternalTriplesActive.step ?_ ihRest
              refine Or.inr ⟨not_isCollider_of_forward_chain G mutilation
                (previous := source) second, ?_⟩
              exact openNodes middle
                (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))

/--
An exact directed walk whose vertices are all unconditioned is an active
path.  Ancestral lifts glue these chains to bidirected forks.
-/
def ActivePath.ofOpenDirectedWalk (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (simple : walk.nodes.Nodup)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false) :
    ActivePath G mutilation conditioned
      (.observed source) (.observed target) where
  nodes := walk.nodes.map SeparationNode.observed
  starts := by
    simpa [List.head?_map] using walk.nodes_head
  finishes := by
    simpa [List.getLast?_map] using walk.nodes_getLast
  simple := nodup_map_observed simple
  adjacent := consecutive_adjacent_of_directed_walk G mutilation walk
  source_open := openNodes source walk.mem_source
  target_open := openNodes target walk.mem_target
  internal_active :=
    InternalTriplesActive.of_open_directed_walk G mutilation conditioned
      walk openNodes

/--
Reversing an active path remains active: adjacency is symmetric, collider
windows reverse in place, and the endpoints merely swap.  Ancestral forks
glue a reversed walk into `Z` onto a walk into `Y`.
-/
def ActivePath.reverse {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {source target : SeparationNode S}
    (path : ActivePath G mutilation conditioned source target) :
    ActivePath G mutilation conditioned target source where
  nodes := path.nodes.reverse
  starts := by
    rw [head?_reverse_eq_getLast?]
    exact path.finishes
  finishes := by
    simpa [List.getLast?_reverse] using path.starts
  simple := nodup_reverse_of path.simple
  adjacent :=
    Consecutive.reverse (fun _left _right => Adjacent.symm)
      path.nodes path.adjacent
  source_open := path.target_open
  target_open := path.source_open
  internal_active :=
    InternalTriplesActive.reverse path.nodes path.internal_active

/-- Path d-separation does not order the two observed families. -/
theorem PathDSeparated.symm {G : ObservedGraph S}
    {mutilation : GraphMutilation S}
    {left right conditioned : NodeSet S}
    (separated : PathDSeparated G mutilation left right conditioned) :
    PathDSeparated G mutilation right left conditioned := by
  intro h
  rcases h with ⟨source, target, hRight, hLeft, ⟨path⟩⟩
  exact separated ⟨target, source, hLeft, hRight, ⟨path.reverse⟩⟩

/-- An active path is a nonempty cons-list headed by its source. -/
theorem ActivePath.nodes_cons {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {source target : SeparationNode S}
    (path : ActivePath G mutilation conditioned source target) :
    Exists fun tail => path.nodes = source :: tail :=
  List.head?_eq_some_iff.mp path.starts

/-- An active path is a nonempty snoc-list finished by its target. -/
theorem ActivePath.nodes_snoc {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {source target : SeparationNode S}
    (path : ActivePath G mutilation conditioned source target) :
    Exists fun init => path.nodes = init ++ [target] :=
  List.getLast?_eq_some_iff.mp path.finishes

/--
Glue two active paths at a shared open vertex.  Vertices other than the
shared endpoint must not repeat, and the join window at that endpoint must
be an active triple whenever both sides have a neighbour.
-/
def ActivePath.glue {G : ObservedGraph S}
    {mutilation : GraphMutilation S} {conditioned : NodeSet S}
    {src shared dest : SeparationNode S}
    (left : ActivePath G mutilation conditioned src shared)
    (right : ActivePath G mutilation conditioned shared dest)
    (onlyShared : forall x, x ∈ left.nodes -> x ∈ right.nodes -> x = shared)
    (join : forall pred succ,
      left.nodes.dropLast.getLast? = some pred ->
        right.nodes.tail.head? = some succ ->
          TripleActive G mutilation conditioned pred shared succ) :
    ActivePath G mutilation conditioned src dest where
  nodes := left.nodes ++ right.nodes.tail
  starts := by
    rcases left.nodes_cons with ⟨_tail, hleft⟩
    simp [hleft]
  finishes := by
    rcases right.nodes_cons with ⟨rest, hright⟩
    simp [hright]
    cases hrest : rest with
    | nil =>
        have hfin := right.finishes
        simp [hright, hrest] at hfin
        subst dest
        simpa [hrest] using left.finishes
    | cons _succ _more =>
        have hfin := right.finishes
        simp [hright, hrest] at hfin
        simpa [hrest, List.getLast?_append] using hfin
  simple := by
    rcases right.nodes_cons with ⟨rest, hright⟩
    simp [hright]
    have rparts := List.nodup_cons.mp (by simpa [hright] using right.simple)
    refine nodup_append_of_disjoint left.simple rparts.2 ?_
    intro x hxLeft hxRest
    have hxRight : x ∈ right.nodes := by
      simpa [hright] using List.mem_cons.mpr (Or.inr hxRest)
    have eq := onlyShared x hxLeft hxRight
    subst x
    exact rparts.1 hxRest
  adjacent := by
    rcases right.nodes_cons with ⟨rest, hright⟩
    simp [hright]
    refine Consecutive.append left.nodes rest left.adjacent ?_ ?_
    · have radj := right.adjacent
      simp [hright] at radj
      cases rest with
      | nil =>
          simp [Consecutive]
      | cons _succ _more =>
          simp [Consecutive] at radj
          exact radj.2
    · intro previous next prevLast nextHead
      have prevEq : previous = shared :=
        Option.some.inj (prevLast.symm.trans left.finishes)
      subst previous
      cases hrest : rest with
      | nil =>
          simp [hrest] at nextHead
      | cons succ more =>
          simp [hrest] at nextHead
          subst next
          have radj := right.adjacent
          simp [hright, hrest, Consecutive] at radj
          exact radj.1
  source_open := left.source_open
  target_open := right.target_open
  internal_active := by
    rcases right.nodes_cons with ⟨rest, hright⟩
    rcases left.nodes_snoc with ⟨init, hleft⟩
    have recon : left.nodes.dropLast ++ [shared] = left.nodes := by
      rw [hleft, dropLast_snoc]
    have leftActive :
        InternalTriplesActive G mutilation conditioned
          (left.nodes.dropLast ++ [shared]) := by
      simpa [recon] using left.internal_active
    have rightActive :
        InternalTriplesActive G mutilation conditioned (shared :: rest) := by
      simpa [hright] using right.internal_active
    have glued :
        InternalTriplesActive G mutilation conditioned
          (left.nodes.dropLast ++ shared :: rest) :=
      InternalTriplesActive.glue_at left.nodes.dropLast shared rest
        leftActive rightActive (by
          simpa [hright] using join)
    have fullEq :
        left.nodes.dropLast ++ shared :: rest =
          left.nodes ++ rest := by
      have : left.nodes.dropLast ++ [shared] ++ rest =
          left.nodes ++ rest := by
        simp [recon]
      simpa [List.append_assoc] using this
    simpa [hright, fullEq] using glued

/--
Glue the reverse of an all-open directed walk `source → target` onto a
bidirected edge `source ↔ other`.  The result is an active path from
`target` to `other` through `source`.  The other endpoint must not already
lie on the directed walk; a shortest ancestral walk discharges that by
path d-separation of a suffix.
-/
def ActivePath.ofOpenDirectedWalk_glue_bidirected (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {source target other : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (simple : walk.nodes.Nodup)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (hedge : G.bidirected source other = true)
    (different : source ≠ other)
    (otherOpen : ObservedGraph.blockedBy conditioned (.observed other) = false)
    (sourceIncoming : mutilation.removeIncoming source = false)
    (otherIncoming : mutilation.removeIncoming other = false)
    (notOnWalk : other ∉ walk.nodes) :
    ActivePath G mutilation conditioned
      (.observed target) (.observed other) :=
  ActivePath.glue
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned walk simple
      openNodes).reverse
    (ActivePath.ofBidirected G mutilation conditioned hedge different
      (openNodes source walk.mem_source) otherOpen sourceIncoming
      otherIncoming)
    (fun x hxL hxR => by
      have hxL' : x ∈ (walk.nodes.map SeparationNode.observed).reverse := hxL
      have hxLmem := List.mem_reverse.mp hxL'
      rcases List.mem_map.mp hxLmem with ⟨n, nMem, hobs⟩
      subst x
      have hxR' := hxR
      simp only [ActivePath.ofBidirected, List.mem_cons] at hxR'
      rcases hxR' with hsrc | hlat | hother
      · cases hsrc
        rfl
      · cases hlat
      · have heq : n = other := by
          simpa using hother
        subst n
        exact (notOnWalk nMem).elim)
    (fun pred succ hpred hsucc => by
      have hsucc' : succ = .latentPair source other := by
        simpa [ActivePath.ofBidirected] using hsucc.symm
      subst succ
      cases walk with
      | refl node =>
          simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
            FiniteReachability.ExactWalk.nodes] at hpred
      | @step length source middle target first rest =>
          have hpred' : pred = .observed middle := by
            simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
              FiniteReachability.ExactWalk.nodes, List.reverse_cons] at hpred
            rcases hpred with ⟨a, ha, hobs⟩
            have ha' : a = middle :=
              Option.some.inj (ha.symm.trans rest.nodes_head)
            subst a
            exact hobs.symm
          subst pred
          refine Or.inr ⟨not_isCollider_of_outgoing G mutilation first, ?_⟩
          exact openNodes source (by simp [FiniteReachability.ExactWalk.nodes]))

/--
An open directed walk glued onto a bidirected collider: the walk is
reversed so the path runs from `target` through `source` and the
conditioned collider onto the other open endpoint.
-/
def ActivePath.ofOpenDirectedWalk_glue_bidirected_collider
    (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {source target collider other : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (simple : walk.nodes.Nodup)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (hedgeLeft : G.bidirected source collider = true)
    (hedgeRight : G.bidirected collider other = true)
    (sourceNeCollider : source ≠ collider)
    (otherNeCollider : other ≠ collider)
    (sourceNeOther : source ≠ other)
    (otherOpen : ObservedGraph.blockedBy conditioned (.observed other) =
      false)
    (sourceIncoming : mutilation.removeIncoming source = false)
    (colliderIncoming : mutilation.removeIncoming collider = false)
    (otherIncoming : mutilation.removeIncoming other = false)
    (activated : ColliderActivated G mutilation conditioned
      (.observed collider))
    (colliderNotOnWalk : collider ∉ walk.nodes)
    (otherNotOnWalk : other ∉ walk.nodes) :
    ActivePath G mutilation conditioned
      (.observed target) (.observed other) :=
  ActivePath.glue
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned walk simple
      openNodes).reverse
    (ActivePath.ofBidirectedCollider G mutilation conditioned hedgeLeft
      hedgeRight sourceNeCollider otherNeCollider sourceNeOther
      (openNodes source walk.mem_source) otherOpen sourceIncoming
      colliderIncoming otherIncoming activated)
    (fun x hxL hxR => by
      have hxLmem := List.mem_reverse.mp hxL
      rcases List.mem_map.mp hxLmem with ⟨n, nMem, hobs⟩
      subst x
      have hxR' := hxR
      simp only [ActivePath.ofBidirectedCollider, List.mem_cons] at hxR'
      rcases hxR' with hsrc | hlat | hcol | hlat2 | hother
      · cases hsrc
        rfl
      · cases hlat
      · have heq : n = collider := by
          simpa using hcol
        subst n
        exact (colliderNotOnWalk nMem).elim
      · cases hlat2
      · have heq : n = other := by
          simpa using hother
        subst n
        exact (otherNotOnWalk nMem).elim)
    (fun pred succ hpred hsucc => by
      have hsucc' : succ = .latentPair source collider := by
        simpa [ActivePath.ofBidirectedCollider] using hsucc.symm
      subst succ
      cases walk with
      | refl node =>
          simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
            FiniteReachability.ExactWalk.nodes] at hpred
      | @step length source middle target first rest =>
          have hpred' : pred = .observed middle := by
            simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
              FiniteReachability.ExactWalk.nodes, List.reverse_cons] at hpred
            rcases hpred with ⟨a, ha, hobs⟩
            have ha' : a = middle :=
              Option.some.inj (ha.symm.trans rest.nodes_head)
            subst a
            exact hobs.symm
          subst pred
          refine Or.inr ⟨not_isCollider_of_outgoing G mutilation first, ?_⟩
          exact openNodes source (by simp [FiniteReachability.ExactWalk.nodes]))

/--
An open directed walk glued onto two bidirected colliders: the walk is
reversed so the path runs from `target` through `source` and the two
conditioned colliders onto the other open endpoint.
-/
def ActivePath.ofOpenDirectedWalk_glue_two_bidirected_colliders
    (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {source target first second other : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (simple : walk.nodes.Nodup)
    (openNodes : forall n, n ∈ walk.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (hedgeLeft : G.bidirected source first = true)
    (hedgeMid : G.bidirected first second = true)
    (hedgeRight : G.bidirected second other = true)
    (sourceNeFirst : source ≠ first)
    (sourceNeSecond : source ≠ second)
    (sourceNeOther : source ≠ other)
    (firstNeSecond : first ≠ second)
    (firstNeOther : first ≠ other)
    (secondNeOther : second ≠ other)
    (otherOpen : ObservedGraph.blockedBy conditioned (.observed other) =
      false)
    (sourceIncoming : mutilation.removeIncoming source = false)
    (firstIncoming : mutilation.removeIncoming first = false)
    (secondIncoming : mutilation.removeIncoming second = false)
    (otherIncoming : mutilation.removeIncoming other = false)
    (activatedFirst : ColliderActivated G mutilation conditioned
      (.observed first))
    (activatedSecond : ColliderActivated G mutilation conditioned
      (.observed second))
    (firstNotOnWalk : first ∉ walk.nodes)
    (secondNotOnWalk : second ∉ walk.nodes)
    (otherNotOnWalk : other ∉ walk.nodes) :
    ActivePath G mutilation conditioned
      (.observed target) (.observed other) :=
  ActivePath.glue
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned walk simple
      openNodes).reverse
    (ActivePath.ofTwoBidirectedColliders G mutilation conditioned hedgeLeft
      hedgeMid hedgeRight sourceNeFirst sourceNeSecond sourceNeOther
      firstNeSecond firstNeOther secondNeOther
      (openNodes source walk.mem_source) otherOpen sourceIncoming
      firstIncoming secondIncoming otherIncoming activatedFirst
      activatedSecond)
    (fun x hxL hxR => by
      have hxLmem := List.mem_reverse.mp hxL
      rcases List.mem_map.mp hxLmem with ⟨n, nMem, hobs⟩
      subst x
      have hxR' := hxR
      simp only [ActivePath.ofTwoBidirectedColliders, List.mem_cons] at hxR'
      rcases hxR' with hsrc | hlat | h1 | hlat2 | h2 | hlat3 | hother
      · cases hsrc
        rfl
      · cases hlat
      · have heq : n = first := by
          simpa using h1
        subst n
        exact (firstNotOnWalk nMem).elim
      · cases hlat2
      · have heq : n = second := by
          simpa using h2
        subst n
        exact (secondNotOnWalk nMem).elim
      · cases hlat3
      · have heq : n = other := by
          simpa using hother
        subst n
        exact (otherNotOnWalk nMem).elim)
    (fun pred succ hpred hsucc => by
      have hsucc' : succ = .latentPair source first := by
        simpa [ActivePath.ofTwoBidirectedColliders] using hsucc.symm
      subst succ
      cases walk with
      | refl node =>
          simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
            FiniteReachability.ExactWalk.nodes] at hpred
      | @step length source middle target firstEdge rest =>
          have hpred' : pred = .observed middle := by
            simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
              FiniteReachability.ExactWalk.nodes, List.reverse_cons] at hpred
            rcases hpred with ⟨a, ha, hobs⟩
            have ha' : a = middle :=
              Option.some.inj (ha.symm.trans rest.nodes_head)
            subst a
            exact hobs.symm
          subst pred
          refine Or.inr ⟨not_isCollider_of_outgoing G mutilation firstEdge,
            ?_⟩
          exact openNodes source (by simp [FiniteReachability.ExactWalk.nodes]))

/-- Every non-source vertex of a mutilated directed walk has its incoming
arrows intact, so it is not an intervened child in `G_{\overline{X}}`. -/
theorem directed_walk_mem_not_removeIncoming (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {length : Nat} {source target node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (member : node ∈ walk.nodes) (different : node ≠ source) :
    mutilation.removeIncoming node = false := by
  induction walk with
  | refl endpoint =>
      simp only [FiniteReachability.ExactWalk.nodes, List.mem_singleton]
        at member
      subst node
      exact (different rfl).elim
  | @step length source middle target first rest ih =>
      simp only [FiniteReachability.ExactWalk.nodes, List.mem_cons] at member
      rcases member with same | later
      · subst node
        exact (different rfl).elim
      · by_cases hmid : node = middle
        · subst node
          simp [ObservedGraph.observedDirectedEdge] at first
          exact first.2
        · exact ih later hmid

end PathSpecification

namespace FiniteReachability
namespace ExactWalk

/-- Reversing a directed walk yields consecutive reverse-edges.  Placed
after `Consecutive.snoc` because the proof snoc-glues the reversed tail. -/
theorem consecutive_reverse {edge : α -> α -> Bool}
    {length : Nat} {source target : α}
    (walk : ExactWalk edge length source target) :
    PathSpecification.Consecutive
      (fun left right => edge right left = true) walk.nodes.reverse := by
  induction walk with
  | refl node =>
      simp [nodes, PathSpecification.Consecutive]
  | @step length source middle target first rest ih =>
      have revEq : (source :: rest.nodes).reverse =
          rest.nodes.reverse ++ [source] := by
        simp [List.reverse_cons]
      rw [nodes_step, revEq]
      apply PathSpecification.Consecutive.snoc ih
      intro older olderLast
      have lastEq : rest.nodes.reverse.getLast? = some middle := by
        simpa [List.getLast?_reverse] using rest.nodes_head
      rw [lastEq] at olderLast
      cases olderLast
      exact first

end ExactWalk
end FiniteReachability

theorem FiniteReachability.Reachable.of_consecutive
    (edge : α -> α -> Bool) (nodes : List α) {source target : α}
    (starts : nodes.head? = some source)
    (finishes : nodes.getLast? = some target)
    (consecutive : PathSpecification.Consecutive
      (fun left right => edge left right = true) nodes) :
    FiniteReachability.Reachable edge source target := by
  induction nodes generalizing source with
  | nil => simp at starts
  | cons first tail ih =>
      simp only [List.head?_cons, Option.some.injEq] at starts
      subst source
      cases tail with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at finishes
          subst target
          exact FiniteReachability.Reachable.refl edge first
      | cons next rest =>
          have tailFinishes : (next :: rest).getLast? = some target := by
            simpa using finishes
          exact FiniteReachability.Reachable.prepend consecutive.1
            (ih rfl tailFinishes consecutive.2)

/--
On an explicitly enumerated finite carrier, every finite walk has an
equivalent bounded walk.  The proof shortens the walk first, so no
decidability principle beyond the supplied Boolean equality is needed.
-/
theorem FiniteReachability.boundedWalk_of_reachable
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (same_iff : forall left right, same left right = true <-> left = right)
    (complete : forall node, node ∈ nodes)
    {source target : α}
    (reachable : FiniteReachability.Reachable edge source target) :
    FiniteReachability.BoundedWalk edge nodes.length source target := by
  rcases reachable with ⟨length, walk⟩
  have initiallyBounded : FiniteReachability.BoundedWalk edge length
      source target := ⟨length, Nat.le_refl _, walk⟩
  rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
      same nodes edge same_iff complete initiallyBounded with ⟨simple⟩
  have vertexBound : simple.walk.nodes.length <= nodes.length :=
    nodup_length_le_of_subset same same_iff simple.walk.nodes nodes
      simple.simple (fun node _member => complete node)
  have edgeBound : simple.length <= nodes.length := by
    rw [simple.walk.nodes_length] at vertexBound
    omega
  exact ⟨simple.length, edgeBound, ⟨simple.walk⟩⟩

theorem finBeq_eq_true_iff {n : Nat} (left right : Fin n) :
    finBeq left right = true <-> left = right := by
  simp [finBeq, Fin.ext_iff]

namespace SeparationNode

theorem code_injective {S : ObservedSignature} :
    Function.Injective (@code S) := by
  intro left right sameCode
  cases left with
  | observed left =>
      cases right with
      | observed right =>
          congr 1
          apply Fin.ext
          simpa [code] using sameCode
      | latentPair first second =>
          simp only [code] at sameCode
          have lower : S.count <= S.count + first.val * S.count + second.val :=
            Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          have impossible : S.count <= left.val := by
            calc
              S.count <= S.count + first.val * S.count + second.val := lower
              _ = left.val := sameCode.symm
          exact (Nat.not_le_of_gt left.isLt impossible).elim
  | latentPair leftFirst leftSecond =>
      cases right with
      | observed right =>
          simp only [code] at sameCode
          have lower :
              S.count <= S.count + leftFirst.val * S.count + leftSecond.val :=
            Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          have impossible : S.count <= right.val := by
            calc
              S.count <= S.count + leftFirst.val * S.count + leftSecond.val := lower
              _ = right.val := sameCode
          exact (Nat.not_le_of_gt right.isLt impossible).elim
      | latentPair rightFirst rightSecond =>
          simp only [code] at sameCode
          have normalized :
              S.count + (leftFirst.val * S.count + leftSecond.val) =
                S.count + (rightFirst.val * S.count + rightSecond.val) := by
            simpa [Nat.add_assoc] using sameCode
          have core :
              leftFirst.val * S.count + leftSecond.val =
                rightFirst.val * S.count + rightSecond.val :=
            Nat.add_left_cancel normalized
          have countPositive : 0 < S.count := by
            exact Nat.zero_lt_of_lt leftFirst.isLt
          have seconds : leftSecond.val = rightSecond.val := by
            have remainders := congrArg (fun value => value % S.count) core
            simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt,
              leftSecond.isLt, rightSecond.isLt] using remainders
          have firsts : leftFirst.val = rightFirst.val := by
            have quotients := congrArg (fun value => value / S.count) core
            simpa [Nat.mul_add_div countPositive, Nat.div_eq_of_lt,
              Nat.mul_comm, leftSecond.isLt, rightSecond.isLt] using quotients
          have firstEq : leftFirst = rightFirst := Fin.ext firsts
          have secondEq : leftSecond = rightSecond := Fin.ext seconds
          cases firstEq
          cases secondEq
          rfl

theorem beq_eq_true_iff (left right : SeparationNode S) :
    beq left right = true <-> left = right := by
  change left.code.beq right.code = true <-> left = right
  rw [Nat.beq_eq]
  exact code_injective.eq_iff

theorem beq_eq_false_iff (left right : SeparationNode S) :
    beq left right = false <-> left ≠ right := by
  constructor
  · intro equalFalse sameNode
    subst right
    have equalTrue := (beq_eq_true_iff left left).mpr rfl
    rw [equalFalse] at equalTrue
    contradiction
  · intro different
    cases equalValue : beq left right with
    | false => rfl
    | true =>
        exact (different ((beq_eq_true_iff left right).mp equalValue)).elim

theorem not_beq_eq_true_iff (left right : SeparationNode S) :
    Bool.not (beq left right) = true <-> left ≠ right := by
  constructor
  · intro notEqual
    cases equalValue : beq left right with
    | false => exact (beq_eq_false_iff left right).mp equalValue
    | true => simp [equalValue] at notEqual
  · intro different
    have equalFalse := (beq_eq_false_iff left right).mpr different
    simp [equalFalse]

theorem beq_comm (left right : SeparationNode S) :
    beq left right = beq right left := by
  simp only [beq]
  exact natBeq_comm left.code right.code

/-- A topological rank for the explicit-latent separation DAG. -/
def rank : SeparationNode S -> Nat
  | .latentPair _ _ => 0
  | .observed node => node.val + 1

theorem mem_all_observed (node : Fin S.count) :
    observed node ∈ allObserved S := by
  simp [allObserved, List.mem_ofFn]

theorem mem_all_latentPairs (left right : Fin S.count) :
    latentPair left right ∈ allLatentPairs S := by
  simp [allLatentPairs, List.mem_ofFn]

theorem mem_all (node : SeparationNode S) : node ∈ all S := by
  cases node with
  | observed node => simp [all, mem_all_observed]
  | latentPair left right => simp [all, mem_all_latentPairs]

end SeparationNode

/-- Membership in a `SeparationNode` list is a Boolean `any` of `beq`.
Oxford overlap search uses this to stay inside executable `find?`. -/
theorem any_beq_eq_true_iff (nodes : List (SeparationNode S))
    (node : SeparationNode S) :
    nodes.any (fun y => SeparationNode.beq y node) = true <-> node ∈ nodes := by
  constructor
  · intro h
    rcases List.any_eq_true.mp h with ⟨y, hy, heq⟩
    have same := (SeparationNode.beq_eq_true_iff y node).mp heq
    subst node
    exact hy
  · intro h
    exact List.any_eq_true.mpr
      ⟨node, h, (SeparationNode.beq_eq_true_iff node node).mpr rfl⟩

/-- First vertex of `front` that also occurs in `back`, if any. -/
def firstSharedSeparation? (front back : List (SeparationNode S)) :
    Option (SeparationNode S) :=
  front.find? (fun v => back.any (fun y => SeparationNode.beq y v))

theorem firstSharedSeparation?_eq_none_disjoint
    {front back : List (SeparationNode S)}
    (h : firstSharedSeparation? front back = none) :
    forall v, v ∈ front -> v ∈ back -> False := by
  intro v vFront vBack
  have noneAll := List.find?_eq_none.mp h
  have predFalse := noneAll v vFront
  have predTrue : back.any (fun y => SeparationNode.beq y v) = true :=
    (any_beq_eq_true_iff back v).mpr vBack
  rw [predTrue] at predFalse
  contradiction

/-- A first shared vertex of a prefix remains first after any suffix. -/
theorem firstSharedSeparation?_append_left
    {xs ys back : List (SeparationNode S)} {u : SeparationNode S}
    (h : firstSharedSeparation? xs back = some u) :
    firstSharedSeparation? (xs ++ ys) back = some u :=
  find?_append_left (fun v => back.any (fun y => SeparationNode.beq y v))
    xs ys h

/-- If a prefix shares nothing with `back`, the next cell is first shared
exactly when it occurs in `back`. -/
theorem firstSharedSeparation?_eq_none_append_cons
    {xs back : List (SeparationNode S)} {y : SeparationNode S}
    (ys : List (SeparationNode S))
    (hnone : firstSharedSeparation? xs back = none)
    (hy : y ∈ back) :
    firstSharedSeparation? (xs ++ y :: ys) back = some y :=
  find?_eq_none_append_cons
    (fun v => back.any (fun z => SeparationNode.beq z v)) xs y ys hnone
    ((any_beq_eq_true_iff back y).mpr hy)

theorem firstSharedSeparation?_eq_some_split
    {front back : List (SeparationNode S)} {v : SeparationNode S}
    (h : firstSharedSeparation? front back = some v) :
    Exists fun before => Exists fun after =>
      front = before ++ v :: after /\
        (forall x, x ∈ before -> Not (x ∈ back)) /\ v ∈ back := by
  rcases find?_eq_some_split
      (fun w => back.any (fun y => SeparationNode.beq y w)) front v h with
    ⟨before, after, split, noneBefore, pred⟩
  refine ⟨before, after, split, ?_, (any_beq_eq_true_iff back v).mp pred⟩
  intro x hx xBack
  have predFalse := noneBefore x hx
  have predTrue := (any_beq_eq_true_iff back x).mpr xBack
  rw [predTrue] at predFalse
  contradiction

/-- Overlapping trails have a first shared vertex. -/
theorem firstSharedSeparation?_isSome_of_mem
    {front back : List (SeparationNode S)} {v : SeparationNode S}
    (hvFront : v ∈ front) (hvBack : v ∈ back) :
    Exists fun u => firstSharedSeparation? front back = some u := by
  cases h : firstSharedSeparation? front back with
  | some u =>
      exact ⟨u, rfl⟩
  | none =>
      exact (firstSharedSeparation?_eq_none_disjoint h v hvFront hvBack).elim

namespace PathSpecification

/--
Two all-open directed walks from a common source yield an active path
between their targets, glued at the first shared vertex of the reversed
left walk with the right walk.  A common open ancestor of `Z` and `Y` is
the case `source` equal on both walks.  Placed after the first-shared
search so the glue can name that vertex.
-/
def ActivePath.ofOpenDirectedFork (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {lengthZ lengthY : Nat} {shared zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthZ shared zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthY shared yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false) :
    ActivePath G mutilation conditioned
      (.observed zEnd) (.observed yEnd) := by
  let front := (walkZ.nodes.map SeparationNode.observed).reverse
  let back := walkY.nodes.map SeparationNode.observed
  have hvFront : SeparationNode.observed shared ∈ front :=
    List.mem_reverse.mpr
      (List.mem_map.mpr ⟨shared, walkZ.mem_source, rfl⟩)
  have hvBack : SeparationNode.observed shared ∈ back :=
    List.mem_map.mpr ⟨shared, walkY.mem_source, rfl⟩
  let pred := fun v => back.any (fun y => SeparationNode.beq y v)
  match hsplit : find?Split pred front with
  | none =>
      have hnone : firstSharedSeparation? front back = none :=
        find?_eq_none_of_find?Split pred front hsplit
      exact (firstSharedSeparation?_eq_none_disjoint hnone
        (.observed shared) hvFront hvBack).elim
  | some (before, u, after) =>
  have spec := find?Split_spec pred front before u after hsplit
  have splitFront := spec.1
  have noneBefore := spec.2.1
  have predU := spec.2.2
  have uBack : u ∈ back := (any_beq_eq_true_iff back u).mp predU
  have disjointBefore : forall x, x ∈ before -> Not (x ∈ back) := by
    intro x hx xBack
    have predFalse : pred x = false := noneBefore x hx
    have predTrue : pred x = true :=
      (any_beq_eq_true_iff back x).mpr xBack
    rw [predTrue] at predFalse
    cases predFalse
  have uFront : u ∈ front := by
    rw [splitFront]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  match u, uBack, uFront with
  | .latentPair left right, uBack, _uFront =>
      exact (not_mem_map_observed_latent left right walkY.nodes uBack).elim
  | .observed meet, uBack, uFront =>
  have meetY : meet ∈ walkY.nodes := mem_of_observed_mem_map uBack
  have meetZ : meet ∈ walkZ.nodes :=
    mem_of_observed_mem_map (List.mem_reverse.mp uFront)
  rcases walkZ.suffixFrom meet meetZ with ⟨_lenZ, sufZ, preZ, ⟨hnodesZ⟩⟩
  rcases walkY.suffixFrom meet meetY with ⟨_lenY, sufY, _preY, ⟨hnodesY⟩⟩
  have simpleSufZ : sufZ.nodes.Nodup := by
    have hnd := simpleZ
    rw [hnodesZ] at hnd
    exact (List.nodup_append.mp hnd).2.1
  have simpleSufY : sufY.nodes.Nodup := by
    have hnd := simpleY
    rw [hnodesY] at hnd
    exact (List.nodup_append.mp hnd).2.1
  have hu : firstSharedSeparation? front back =
      some (.observed meet) :=
    find?_eq_some_of_find?Split pred front before (.observed meet) after
      hsplit
  have subZ : forall n, n ∈ sufZ.nodes -> n ∈ walkZ.nodes := fun n hn => by
    rw [hnodesZ]
    exact List.mem_append.mpr (Or.inr hn)
  have subY : forall n, n ∈ sufY.nodes -> n ∈ walkY.nodes := fun n hn => by
    rw [hnodesY]
    exact List.mem_append.mpr (Or.inr hn)
  refine ActivePath.glue
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned sufZ simpleSufZ
      (fun n hn => openZ n (subZ n hn))).reverse
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned sufY simpleSufY
      (fun n hn => openY n (subY n hn)))
    ?_ ?_
  · intro x hxL hxR
    have hxLmem := List.mem_reverse.mp hxL
    rcases List.mem_map.mp hxLmem with ⟨n, hnZ, hobs⟩
    subst x
    rcases List.mem_map.mp hxR with ⟨n', hnY, hobsY⟩
    have nEq : n = n' := by
      cases hobsY
      rfl
    subst n'
    by_cases hmeet : n = meet
    · subst n
      rfl
    · have nHead := sufZ.nodes_head
      cases hsuf : sufZ.nodes with
      | nil =>
          simp [hsuf] at nHead
      | cons head tail =>
          simp [hsuf] at nHead hnZ
          subst head
          rcases hnZ with same | inTail
          · exact (hmeet same).elim
          · have frontEq :
                front =
                  (tail.map SeparationNode.observed).reverse ++
                    SeparationNode.observed meet ::
                      (preZ.map SeparationNode.observed).reverse := by
              simp [front, hnodesZ, hsuf, List.map_append, List.reverse_append]
            have meetNotTail : meet ∉ tail :=
              (List.nodup_cons.mp (by simpa [hsuf] using simpleSufZ)).1
            have meetNotRevTail :
                SeparationNode.observed meet ∉
                  (tail.map SeparationNode.observed).reverse := by
              intro hmem
              rcases List.mem_map.mp (List.mem_reverse.mp hmem) with
                ⟨m, hm, hobs⟩
              cases hobs
              exact meetNotTail hm
            have meetNotBefore : SeparationNode.observed meet ∉ before :=
              fun hmem => disjointBefore _ hmem uBack
            cases hpref :
                firstSharedSeparation? (tail.map SeparationNode.observed).reverse
                  back with
            | some u =>
                have hleft :=
                  firstSharedSeparation?_append_left
                    (ys :=
                      SeparationNode.observed meet ::
                        (preZ.map SeparationNode.observed).reverse)
                    hpref
                have hfront : firstSharedSeparation? front back = some u := by
                  simpa [frontEq] using hleft
                have hu' : u = SeparationNode.observed meet := by
                  rw [hfront] at hu
                  injection hu
                subst u
                have uMem :
                    SeparationNode.observed meet ∈
                      (tail.map SeparationNode.observed).reverse := by
                  rcases firstSharedSeparation?_eq_some_split hpref with
                    ⟨_b, _a, split, _, _⟩
                  rw [split]
                  exact List.mem_append.mpr
                    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
                exact (meetNotRevTail uMem).elim
            | none =>
                have hEqLists :
                    before ++ SeparationNode.observed meet :: after =
                      (tail.map SeparationNode.observed).reverse ++
                        SeparationNode.observed meet ::
                          (preZ.map SeparationNode.observed).reverse := by
                  rw [← splitFront, frontEq]
                rcases append_cons_inj_of_not_mem hEqLists meetNotBefore
                    meetNotRevTail with ⟨beforeEq, _⟩
                have nBefore : SeparationNode.observed n ∈ before := by
                  rw [beforeEq]
                  exact List.mem_reverse.mpr
                    (List.mem_map.mpr ⟨n, inTail, rfl⟩)
                have nBack : SeparationNode.observed n ∈ back :=
                  List.mem_map.mpr ⟨n, subY n hnY, rfl⟩
                exact (disjointBefore _ nBefore nBack).elim
  · intro pred succ hpred hsucc
    cases sufY with
    | refl node =>
        simp [ActivePath.ofOpenDirectedWalk,
          FiniteReachability.ExactWalk.nodes] at hsucc
    | @step length source middle target first rest =>
        have hsucc' : succ = .observed middle := by
          simp [ActivePath.ofOpenDirectedWalk,
            FiniteReachability.ExactWalk.nodes] at hsucc
          rcases hsucc with ⟨a, ha, hobs⟩
          have ha' : a = middle :=
            Option.some.inj (ha.symm.trans rest.nodes_head)
          subst a
          exact hobs.symm
        subst succ
        cases sufZ with
        | refl node =>
            simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
              FiniteReachability.ExactWalk.nodes] at hpred
        | @step lengthZ sourceZ middleZ targetZ firstZ restZ =>
            have hpred' : pred = .observed middleZ := by
              simp [ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
                FiniteReachability.ExactWalk.nodes, List.reverse_cons]
                at hpred
              rcases hpred with ⟨a, ha, hobs⟩
              have ha' : a = middleZ :=
                Option.some.inj (ha.symm.trans restZ.nodes_head)
              subst a
              exact hobs.symm
            subst pred
            refine Or.inr ⟨not_isCollider_of_outgoing G mutilation firstZ, ?_⟩
            exact openY meet meetY

/--
Glue two all-open directed walks across a bidirected edge between their
sources.  The result is an active path between the walk targets.  Shared
vertices are discharged separately as a fork; the Type constructor takes
the walks as disjoint.
-/
def ActivePath.ofOpenWalks_glue_bidirected (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {lengthZ lengthY : Nat} {sourceZ sourceY zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (hedge : G.bidirected sourceZ sourceY = true)
    (different : sourceZ ≠ sourceY)
    (sourceZIncoming : mutilation.removeIncoming sourceZ = false)
    (sourceYIncoming : mutilation.removeIncoming sourceY = false)
    (notOnZ : sourceY ∉ walkZ.nodes)
    (notOnY : sourceZ ∉ walkY.nodes)
    (disjointWalks : forall n, n ∈ walkZ.nodes -> n ∈ walkY.nodes -> False) :
    ActivePath G mutilation conditioned
      (.observed zEnd) (.observed yEnd) := by
  have leftNodes :
      (ActivePath.ofOpenDirectedWalk_glue_bidirected G mutilation conditioned
          walkZ simpleZ openZ hedge different
          (openY sourceY walkY.mem_source) sourceZIncoming sourceYIncoming
          notOnZ).nodes =
        (walkZ.nodes.map SeparationNode.observed).reverse ++
          [.latentPair sourceZ sourceY, .observed sourceY] := by
    simp [ActivePath.ofOpenDirectedWalk_glue_bidirected, ActivePath.glue,
      ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
      ActivePath.ofBidirected]
  have sourceYOpen := openY sourceY walkY.mem_source
  refine ActivePath.glue
    (ActivePath.ofOpenDirectedWalk_glue_bidirected G mutilation conditioned
      walkZ simpleZ openZ hedge different sourceYOpen sourceZIncoming
      sourceYIncoming notOnZ)
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned walkY simpleY
      openY)
    ?_ ?_
  · intro x hxL hxR
    rcases List.mem_map.mp hxR with ⟨n, hnY, hobs⟩
    subst x
    have hxL' : SeparationNode.observed n ∈
        (walkZ.nodes.map SeparationNode.observed).reverse ++
          [.latentPair sourceZ sourceY, .observed sourceY] := by
      simpa [leftNodes] using hxL
    rcases List.mem_append.mp hxL' with inRev | inBid
    · have hxLmem := List.mem_reverse.mp inRev
      rcases List.mem_map.mp hxLmem with ⟨m, hmZ, hobs'⟩
      have meq : m = n := by
        cases hobs'
        rfl
      subst m
      exact (disjointWalks n hmZ hnY).elim
    · simp only [List.mem_cons] at inBid
      rcases inBid with hlat | hsrcY
      · cases hlat
      · have heq : n = sourceY := by
          simpa using hsrcY
        subst n
        rfl
  · intro pred succ hpred hsucc
    cases walkY with
    | refl node =>
        simp [ActivePath.ofOpenDirectedWalk,
          FiniteReachability.ExactWalk.nodes] at hsucc
    | @step length source middle target first rest =>
        have hsucc' : succ = .observed middle := by
          simp [ActivePath.ofOpenDirectedWalk,
            FiniteReachability.ExactWalk.nodes] at hsucc
          rcases hsucc with ⟨a, ha, hobs⟩
          have ha' : a = middle :=
            Option.some.inj (ha.symm.trans rest.nodes_head)
          subst a
          exact hobs.symm
        subst succ
        have hpred' : pred = SeparationNode.latentPair sourceZ sourceY := by
          have hshape :
              (walkZ.nodes.map SeparationNode.observed).reverse ++
                [SeparationNode.latentPair sourceZ sourceY,
                  SeparationNode.observed sourceY] =
                ((walkZ.nodes.map SeparationNode.observed).reverse ++
                  [SeparationNode.latentPair sourceZ sourceY]) ++
                  [SeparationNode.observed sourceY] := by
            simp [List.append_assoc]
          have hdl :
              ((walkZ.nodes.map SeparationNode.observed).reverse ++
                [SeparationNode.latentPair sourceZ sourceY,
                  SeparationNode.observed sourceY]).dropLast.getLast? =
                some (SeparationNode.latentPair sourceZ sourceY) := by
            rw [hshape, dropLast_snoc]
            simp [List.getLast?_append]
          simpa [leftNodes] using (hpred.symm.trans hdl)
        subst pred
        refine Or.inr ⟨not_isCollider_of_outgoing_next G mutilation first,
          sourceYOpen⟩

/--
Two open directed walks joined through a bidirected collider at a
conditioned vertex.  The resulting path runs from the first walk's
endpoint to the second's.
-/
def ActivePath.ofOpenWalks_glue_bidirected_collider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {lengthZ lengthY : Nat}
    {sourceZ sourceY collider zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (hedgeLeft : G.bidirected sourceZ collider = true)
    (hedgeRight : G.bidirected collider sourceY = true)
    (sourceZNeCollider : sourceZ ≠ collider)
    (sourceYNeCollider : sourceY ≠ collider)
    (sourceZNeSourceY : sourceZ ≠ sourceY)
    (sourceZIncoming : mutilation.removeIncoming sourceZ = false)
    (colliderIncoming : mutilation.removeIncoming collider = false)
    (sourceYIncoming : mutilation.removeIncoming sourceY = false)
    (activated : ColliderActivated G mutilation conditioned
      (.observed collider))
    (colliderNotOnZ : collider ∉ walkZ.nodes)
    (colliderNotOnY : collider ∉ walkY.nodes)
    (notOnZ : sourceY ∉ walkZ.nodes)
    (notOnY : sourceZ ∉ walkY.nodes)
    (disjointWalks : forall n, n ∈ walkZ.nodes -> n ∈ walkY.nodes ->
      False) :
    ActivePath G mutilation conditioned
      (.observed zEnd) (.observed yEnd) := by
  have leftNodes :
      (ActivePath.ofOpenDirectedWalk_glue_bidirected_collider G mutilation
          conditioned walkZ simpleZ openZ hedgeLeft hedgeRight
          sourceZNeCollider sourceYNeCollider sourceZNeSourceY
          (openY sourceY walkY.mem_source) sourceZIncoming colliderIncoming
          sourceYIncoming activated colliderNotOnZ notOnZ).nodes =
        (walkZ.nodes.map SeparationNode.observed).reverse ++
          [.latentPair sourceZ collider, .observed collider,
            .latentPair collider sourceY, .observed sourceY] := by
    simp [ActivePath.ofOpenDirectedWalk_glue_bidirected_collider,
      ActivePath.glue, ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
      ActivePath.ofBidirectedCollider]
  have sourceYOpen := openY sourceY walkY.mem_source
  refine ActivePath.glue
    (ActivePath.ofOpenDirectedWalk_glue_bidirected_collider G mutilation
      conditioned walkZ simpleZ openZ hedgeLeft hedgeRight
      sourceZNeCollider sourceYNeCollider sourceZNeSourceY sourceYOpen
      sourceZIncoming colliderIncoming sourceYIncoming activated
      colliderNotOnZ notOnZ)
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned walkY simpleY
      openY)
    ?_ ?_
  · intro x hxL hxR
    rcases List.mem_map.mp hxR with ⟨n, hnY, hobs⟩
    subst x
    have hxL' : SeparationNode.observed n ∈
        (walkZ.nodes.map SeparationNode.observed).reverse ++
          [.latentPair sourceZ collider, .observed collider,
            .latentPair collider sourceY, .observed sourceY] := by
      simpa [leftNodes] using hxL
    rcases List.mem_append.mp hxL' with inRev | inCol
    · have hxLmem := List.mem_reverse.mp inRev
      rcases List.mem_map.mp hxLmem with ⟨m, hmZ, hobs'⟩
      have meq : m = n := by
        cases hobs'
        rfl
      subst m
      exact (disjointWalks n hmZ hnY).elim
    · simp only [List.mem_cons] at inCol
      rcases inCol with hlat | hcol | hlat2 | hsrcY
      · cases hlat
      · have heq : n = collider := by
          simpa using hcol
        subst n
        exact (colliderNotOnY hnY).elim
      · cases hlat2
      · have heq : n = sourceY := by
          simpa using hsrcY
        subst n
        rfl
  · intro pred succ hpred hsucc
    cases walkY with
    | refl node =>
        simp [ActivePath.ofOpenDirectedWalk,
          FiniteReachability.ExactWalk.nodes] at hsucc
    | @step length source middle target first rest =>
        have hsucc' : succ = .observed middle := by
          simp [ActivePath.ofOpenDirectedWalk,
            FiniteReachability.ExactWalk.nodes] at hsucc
          rcases hsucc with ⟨a, ha, hobs⟩
          have ha' : a = middle :=
            Option.some.inj (ha.symm.trans rest.nodes_head)
          subst a
          exact hobs.symm
        subst succ
        have hpred' : pred = SeparationNode.latentPair collider sourceY := by
          have hshape :
              (walkZ.nodes.map SeparationNode.observed).reverse ++
                [SeparationNode.latentPair sourceZ collider,
                  SeparationNode.observed collider,
                  SeparationNode.latentPair collider sourceY,
                  SeparationNode.observed sourceY] =
                ((walkZ.nodes.map SeparationNode.observed).reverse ++
                  [SeparationNode.latentPair sourceZ collider,
                    SeparationNode.observed collider,
                    SeparationNode.latentPair collider sourceY]) ++
                  [SeparationNode.observed sourceY] := by
            simp [List.append_assoc]
          have hdl :
              ((walkZ.nodes.map SeparationNode.observed).reverse ++
                [SeparationNode.latentPair sourceZ collider,
                  SeparationNode.observed collider,
                  SeparationNode.latentPair collider sourceY,
                  SeparationNode.observed sourceY]).dropLast.getLast? =
                some (SeparationNode.latentPair collider sourceY) := by
            rw [hshape, dropLast_snoc]
            simp [List.getLast?_append]
          simpa [leftNodes] using (hpred.symm.trans hdl)
        subst pred
        refine Or.inr ⟨not_isCollider_of_outgoing_next G mutilation first,
          sourceYOpen⟩

/--
Two open directed walks joined through two bidirected colliders.  The
resulting path runs from the first walk's endpoint to the second's.
-/
def ActivePath.ofOpenWalks_glue_two_bidirected_colliders
    (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {lengthZ lengthY : Nat}
    {sourceZ sourceY first second zEnd yEnd : Fin S.count}
    (walkZ : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthZ sourceZ zEnd)
    (walkY : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) lengthY sourceY yEnd)
    (simpleZ : walkZ.nodes.Nodup) (simpleY : walkY.nodes.Nodup)
    (openZ : forall n, n ∈ walkZ.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (openY : forall n, n ∈ walkY.nodes ->
      ObservedGraph.blockedBy conditioned (.observed n) = false)
    (hedgeLeft : G.bidirected sourceZ first = true)
    (hedgeMid : G.bidirected first second = true)
    (hedgeRight : G.bidirected second sourceY = true)
    (sourceZNeFirst : sourceZ ≠ first)
    (sourceZNeSecond : sourceZ ≠ second)
    (sourceZNeSourceY : sourceZ ≠ sourceY)
    (firstNeSecond : first ≠ second)
    (firstNeSourceY : first ≠ sourceY)
    (secondNeSourceY : second ≠ sourceY)
    (sourceZIncoming : mutilation.removeIncoming sourceZ = false)
    (firstIncoming : mutilation.removeIncoming first = false)
    (secondIncoming : mutilation.removeIncoming second = false)
    (sourceYIncoming : mutilation.removeIncoming sourceY = false)
    (activatedFirst : ColliderActivated G mutilation conditioned
      (.observed first))
    (activatedSecond : ColliderActivated G mutilation conditioned
      (.observed second))
    (firstNotOnZ : first ∉ walkZ.nodes)
    (secondNotOnZ : second ∉ walkZ.nodes)
    (firstNotOnY : first ∉ walkY.nodes)
    (secondNotOnY : second ∉ walkY.nodes)
    (notOnZ : sourceY ∉ walkZ.nodes)
    (notOnY : sourceZ ∉ walkY.nodes)
    (disjointWalks : forall n, n ∈ walkZ.nodes -> n ∈ walkY.nodes ->
      False) :
    ActivePath G mutilation conditioned
      (.observed zEnd) (.observed yEnd) := by
  have leftNodes :
      (ActivePath.ofOpenDirectedWalk_glue_two_bidirected_colliders G
          mutilation conditioned walkZ simpleZ openZ hedgeLeft hedgeMid
          hedgeRight sourceZNeFirst sourceZNeSecond sourceZNeSourceY
          firstNeSecond firstNeSourceY secondNeSourceY
          (openY sourceY walkY.mem_source) sourceZIncoming firstIncoming
          secondIncoming sourceYIncoming activatedFirst activatedSecond
          firstNotOnZ secondNotOnZ notOnZ).nodes =
        (walkZ.nodes.map SeparationNode.observed).reverse ++
          [.latentPair sourceZ first, .observed first,
            .latentPair first second, .observed second,
            .latentPair second sourceY, .observed sourceY] := by
    simp [ActivePath.ofOpenDirectedWalk_glue_two_bidirected_colliders,
      ActivePath.glue, ActivePath.reverse, ActivePath.ofOpenDirectedWalk,
      ActivePath.ofTwoBidirectedColliders]
  have sourceYOpen := openY sourceY walkY.mem_source
  refine ActivePath.glue
    (ActivePath.ofOpenDirectedWalk_glue_two_bidirected_colliders G
      mutilation conditioned walkZ simpleZ openZ hedgeLeft hedgeMid
      hedgeRight sourceZNeFirst sourceZNeSecond sourceZNeSourceY
      firstNeSecond firstNeSourceY secondNeSourceY sourceYOpen
      sourceZIncoming firstIncoming secondIncoming sourceYIncoming
      activatedFirst activatedSecond firstNotOnZ secondNotOnZ notOnZ)
    (ActivePath.ofOpenDirectedWalk G mutilation conditioned walkY simpleY
      openY)
    ?_ ?_
  · intro x hxL hxR
    rcases List.mem_map.mp hxR with ⟨n, hnY, hobs⟩
    subst x
    have hxL' : SeparationNode.observed n ∈
        (walkZ.nodes.map SeparationNode.observed).reverse ++
          [.latentPair sourceZ first, .observed first,
            .latentPair first second, .observed second,
            .latentPair second sourceY, .observed sourceY] := by
      simpa [leftNodes] using hxL
    rcases List.mem_append.mp hxL' with inRev | inCol
    · have hxLmem := List.mem_reverse.mp inRev
      rcases List.mem_map.mp hxLmem with ⟨m, hmZ, hobs'⟩
      have meq : m = n := by
        cases hobs'
        rfl
      subst m
      exact (disjointWalks n hmZ hnY).elim
    · simp only [List.mem_cons] at inCol
      rcases inCol with hlat | h1 | hlat2 | h2 | hlat3 | hsrcY
      · cases hlat
      · have heq : n = first := by
          simpa using h1
        subst n
        exact (firstNotOnY hnY).elim
      · cases hlat2
      · have heq : n = second := by
          simpa using h2
        subst n
        exact (secondNotOnY hnY).elim
      · cases hlat3
      · have heq : n = sourceY := by
          simpa using hsrcY
        subst n
        rfl
  · intro pred succ hpred hsucc
    cases walkY with
    | refl node =>
        simp [ActivePath.ofOpenDirectedWalk,
          FiniteReachability.ExactWalk.nodes] at hsucc
    | @step length source middle target firstEdge rest =>
        have hsucc' : succ = .observed middle := by
          simp [ActivePath.ofOpenDirectedWalk,
            FiniteReachability.ExactWalk.nodes] at hsucc
          rcases hsucc with ⟨a, ha, hobs⟩
          have ha' : a = middle :=
            Option.some.inj (ha.symm.trans rest.nodes_head)
          subst a
          exact hobs.symm
        subst succ
        have hpred' : pred = SeparationNode.latentPair second sourceY := by
          have hshape :
              (walkZ.nodes.map SeparationNode.observed).reverse ++
                [SeparationNode.latentPair sourceZ first,
                  SeparationNode.observed first,
                  SeparationNode.latentPair first second,
                  SeparationNode.observed second,
                  SeparationNode.latentPair second sourceY,
                  SeparationNode.observed sourceY] =
                ((walkZ.nodes.map SeparationNode.observed).reverse ++
                  [SeparationNode.latentPair sourceZ first,
                    SeparationNode.observed first,
                    SeparationNode.latentPair first second,
                    SeparationNode.observed second,
                    SeparationNode.latentPair second sourceY]) ++
                  [SeparationNode.observed sourceY] := by
            simp [List.append_assoc]
          have hdl :
              ((walkZ.nodes.map SeparationNode.observed).reverse ++
                [SeparationNode.latentPair sourceZ first,
                  SeparationNode.observed first,
                  SeparationNode.latentPair first second,
                  SeparationNode.observed second,
                  SeparationNode.latentPair second sourceY,
                  SeparationNode.observed sourceY]).dropLast.getLast? =
                some (SeparationNode.latentPair second sourceY) := by
            rw [hshape, dropLast_snoc]
            simp [List.getLast?_append]
          simpa [leftNodes] using (hpred.symm.trans hdl)
        subst pred
        refine Or.inr ⟨not_isCollider_of_outgoing_next G mutilation firstEdge,
          sourceYOpen⟩

end PathSpecification

namespace ObservedGraph

theorem expandedMutilatedEdge_rank_lt (G : ObservedGraph S)
    (mutilation : GraphMutilation S) {source target : SeparationNode S}
    (edge : G.expandedMutilatedEdge mutilation source target = true) :
    source.rank < target.rank := by
  cases source with
  | observed parent =>
      cases target with
      | observed child =>
          simp only [expandedMutilatedEdge, Bool.and_eq_true] at edge
          exact Nat.add_lt_add_right (S.directed_earlier edge.1.1) 1
      | latentPair left right => simp [expandedMutilatedEdge] at edge
  | latentPair left right =>
      cases target with
      | observed child => simp [SeparationNode.rank]
      | latentPair first second => simp [expandedMutilatedEdge] at edge

theorem expandedMutilatedEdge_irreflexive (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (node : SeparationNode S) :
    G.expandedMutilatedEdge mutilation node node = false := by
  cases edgeValue : G.expandedMutilatedEdge mutilation node node with
  | false => rfl
  | true =>
      exact (Nat.lt_irrefl node.rank
        (G.expandedMutilatedEdge_rank_lt mutilation edgeValue)).elim

/-- Expanded DAG adjacency never loops: ranking is strictly increasing. -/
theorem adjacent_irrefl (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (node : SeparationNode S) :
    Not (PathSpecification.Adjacent G mutilation node node) := by
  intro adjacent
  rcases adjacent with forward | reverse
  · rw [G.expandedMutilatedEdge_irreflexive mutilation node] at forward
    contradiction
  · rw [G.expandedMutilatedEdge_irreflexive mutilation node] at reverse
    contradiction

/-- The executable expanded-DAG search has the expected bounded-walk meaning. -/
theorem expandedReachable_eq_true_iff (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (source target : SeparationNode S) :
    G.expandedReachable mutilation source target = true <->
      FiniteReachability.BoundedWalk (G.expandedMutilatedEdge mutilation)
        G.separationNodes.length source target := by
  apply FiniteReachability.within_eq_true_iff_boundedWalk
  · exact SeparationNode.beq_eq_true_iff
  · exact SeparationNode.mem_all

/-- A node is selected by `ancestorOf` exactly when it reaches a target. -/
theorem ancestorOf_eq_true_iff (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    (source : SeparationNode S) :
    G.ancestorOf mutilation targets source = true <->
      Exists fun target : Fin S.count =>
        targets target = true /\
          FiniteReachability.BoundedWalk
            (G.expandedMutilatedEdge mutilation)
            G.separationNodes.length source (.observed target) := by
  simp only [ancestorOf, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨target, _targetMember, targetSelected, reachable⟩
    exact ⟨target, targetSelected,
      (G.expandedReachable_eq_true_iff mutilation source
        (.observed target)).mp reachable⟩
  · rintro ⟨target, targetSelected, reachable⟩
    exact ⟨target, by simp [List.mem_ofFn], targetSelected,
      (G.expandedReachable_eq_true_iff mutilation source
        (.observed target)).mpr reachable⟩

theorem ancestorOf_target (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {target : Fin S.count} (selected : targets target = true) :
    G.ancestorOf mutilation targets (.observed target) = true := by
  apply (G.ancestorOf_eq_true_iff mutilation targets
    (.observed target)).mpr
  exact ⟨target, selected,
    FiniteReachability.BoundedWalk.refl
      (G.expandedMutilatedEdge mutilation) G.separationNodes.length _⟩

theorem ancestorOf_mono (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (smaller larger : NodeSet S)
    (included : forall node, smaller node = true -> larger node = true)
    {source : SeparationNode S}
    (ancestor : G.ancestorOf mutilation smaller source = true) :
    G.ancestorOf mutilation larger source = true := by
  rcases (G.ancestorOf_eq_true_iff mutilation smaller source).mp ancestor with
    ⟨target, selected, walk⟩
  exact (G.ancestorOf_eq_true_iff mutilation larger source).mpr
    ⟨target, included target selected, walk⟩

/-- An ancestor set is closed backwards along expanded-DAG edges. -/
theorem ancestorOf_prepend (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {source middle : SeparationNode S}
    (first : G.expandedMutilatedEdge mutilation source middle = true)
    (middleAncestor : G.ancestorOf mutilation targets middle = true) :
    G.ancestorOf mutilation targets source = true := by
  rcases (G.ancestorOf_eq_true_iff mutilation targets middle).mp
      middleAncestor with ⟨target, selected, rest⟩
  have reachable : FiniteReachability.Reachable
      (G.expandedMutilatedEdge mutilation) source (.observed target) :=
    FiniteReachability.Reachable.prepend first
      (FiniteReachability.Reachable.of_bounded rest)
  have bounded := FiniteReachability.boundedWalk_of_reachable
    SeparationNode.beq G.separationNodes
    (G.expandedMutilatedEdge mutilation)
    SeparationNode.beq_eq_true_iff SeparationNode.mem_all reachable
  exact (G.ancestorOf_eq_true_iff mutilation targets source).mpr
    ⟨target, selected, bounded⟩

/--
Every node on an active path belongs to the ancestral subgraph generated by
its endpoints and the conditioning set.  A maximal-rank counterexample would
have both incident arrows pointing into it, hence would be an activated
collider and therefore an ancestor after all.
-/
theorem activePath_nodes_ancestor_of_endpoints (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {source target : SeparationNode S}
    (sourceAncestor : G.ancestorOf mutilation targets source = true)
    (targetAncestor : G.ancestorOf mutilation targets target = true)
    (activatedIncluded : forall node,
      G.ancestorOf mutilation conditioned node = true ->
        G.ancestorOf mutilation targets node = true)
    (path : PathSpecification.ActivePath G mutilation conditioned
      source target) :
    forall node, node ∈ path.nodes ->
      G.ancestorOf mutilation targets node = true := by
  intro node member
  cases nodeAncestor : G.ancestorOf mutilation targets node with
  | true => rfl
  | false =>
      rcases exists_rank_maximal_false SeparationNode.rank
          (G.ancestorOf mutilation targets) path.nodes
          ⟨node, member, nodeAncestor⟩ with
        ⟨best, bestMember, bestNotAncestor, maximal⟩
      have bestNotSource : best ≠ source := by
        intro same
        subst best
        rw [sourceAncestor] at bestNotAncestor
        contradiction
      have bestNotTarget : best ≠ target := by
        intro same
        subst best
        rw [targetAncestor] at bestNotAncestor
        contradiction
      rcases exists_internal_neighbors_of_mem path.starts path.finishes
          bestMember bestNotSource bestNotTarget with
        ⟨beforePrefix, previous, next, suffix, split⟩
      have previousMember : previous ∈ path.nodes := by
        rw [split]
        simp
      have nextMember : next ∈ path.nodes := by
        rw [split]
        simp
      have consecutive : PathSpecification.Consecutive
          (PathSpecification.Adjacent G mutilation)
          (beforePrefix ++ previous :: best :: next :: suffix) := by
        rw [← split]
        exact path.adjacent
      have previousAdjacent :
          PathSpecification.Adjacent G mutilation previous best :=
        PathSpecification.Consecutive.pair_of_append beforePrefix
          (next :: suffix) previous best consecutive
      have nextAdjacent :
          PathSpecification.Adjacent G mutilation best next :=
        PathSpecification.Consecutive.pair_of_append
          (beforePrefix ++ [previous]) suffix best next (by
            simpa [List.append_assoc] using consecutive)
      have previousIntoBest :
          G.expandedMutilatedEdge mutilation previous best = true := by
        rcases previousAdjacent with into | outOfBest
        · exact into
        · cases previousAncestor :
              G.ancestorOf mutilation targets previous with
          | true =>
              have impossible := G.ancestorOf_prepend mutilation targets
                outOfBest previousAncestor
              rw [bestNotAncestor] at impossible
              contradiction
          | false =>
              have rankIncreases :=
                G.expandedMutilatedEdge_rank_lt mutilation outOfBest
              have rankMax := maximal previous previousMember previousAncestor
              omega
      have nextIntoBest :
          G.expandedMutilatedEdge mutilation next best = true := by
        rcases nextAdjacent with outOfBest | into
        · cases nextAncestor : G.ancestorOf mutilation targets next with
          | true =>
              have impossible := G.ancestorOf_prepend mutilation targets
                outOfBest nextAncestor
              rw [bestNotAncestor] at impossible
              contradiction
          | false =>
              have rankIncreases :=
                G.expandedMutilatedEdge_rank_lt mutilation outOfBest
              have rankMax := maximal next nextMember nextAncestor
              omega
        · exact into
      have collider : PathSpecification.IsCollider G mutilation
          previous best next := ⟨previousIntoBest, nextIntoBest⟩
      have activeTriple : PathSpecification.TripleActive G mutilation
          conditioned previous best next := by
        have allActive := path.internal_active
        rw [split] at allActive
        exact PathSpecification.InternalTriplesActive.triple_of_append
          beforePrefix suffix previous best next allActive
      rcases activeTriple with colliderAndActivated | nonColliderAndOpen
      · have nowAncestor := activatedIncluded best colliderAndActivated.2
        rw [bestNotAncestor] at nowAncestor
        contradiction
      · exact (nonColliderAndOpen.1 collider).elim

theorem activePath_nodes_ancestor (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {source target : Fin S.count}
    (sourceSelected : left source = true)
    (targetSelected : right target = true)
    (path : PathSpecification.ActivePath G mutilation conditioned
      (.observed source) (.observed target)) :
    forall node, node ∈ path.nodes ->
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) node = true := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  apply G.activePath_nodes_ancestor_of_endpoints mutilation targets conditioned
  · apply G.ancestorOf_target
    simp [targets, NodeSet.union, sourceSelected]
  · apply G.ancestorOf_target
    simp [targets, NodeSet.union, targetSelected]
  · intro node activated
    apply G.ancestorOf_mono mutilation conditioned targets _ activated
    intro selected selectedConditioned
    simp [targets, NodeSet.union, selectedConditioned]

theorem observedAncestorOf_eq_true_iff (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    (source : Fin S.count) :
    G.observedAncestorOf mutilation targets source = true <->
      Exists fun target : Fin S.count =>
        targets target = true /\
          FiniteReachability.BoundedWalk (G.observedDirectedEdge mutilation)
            (List.ofFn (fun i : Fin S.count => i)).length source target := by
  simp only [observedAncestorOf, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨target, _targetMember, targetSelected, reachable⟩
    exact ⟨target, targetSelected,
      (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
        (List.ofFn (fun i : Fin S.count => i))
        (G.observedDirectedEdge mutilation) finBeq_eq_true_iff
        (fun node => by simp [List.mem_ofFn]) _ source target).mp reachable⟩
  · rintro ⟨target, targetSelected, reachable⟩
    refine ⟨target, by simp [List.mem_ofFn], targetSelected, ?_⟩
    exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge mutilation) finBeq_eq_true_iff
      (fun node => by simp [List.mem_ofFn]) _ source target).mpr reachable

/-- Ancestry in a mutilated DAG supplies a simple directed walk into the
target family that is shortest among all such walks. -/
theorem exists_minimal_walk_of_observedAncestorOf
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S) (source : Fin S.count)
    (hanc : G.observedAncestorOf mutilation targets source = true) :
    Exists fun target : Fin S.count =>
      targets target = true /\
        Exists fun length : Nat =>
          Exists fun walk :
              FiniteReachability.ExactWalk
                (G.observedDirectedEdge mutilation) length source target =>
            walk.nodes.Nodup /\
              (forall target' alternative,
                targets target' = true ->
                  Nonempty (FiniteReachability.ExactWalk
                    (G.observedDirectedEdge mutilation)
                    alternative source target') ->
                    length <= alternative) := by
  rcases (G.observedAncestorOf_eq_true_iff mutilation targets source).mp hanc with
    ⟨target0, selected0, bounded⟩
  rcases FiniteReachability.exists_minimal_exactWalk_to_set
      finBeq (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge mutilation) finBeq_eq_true_iff
      (fun node => by simp [List.mem_ofFn])
      ⟨target0, selected0, bounded⟩ with
    ⟨target, selected, length, walk, minimal⟩
  rcases walk with ⟨walk⟩
  refine ⟨target, selected, length, walk, ?_, minimal⟩
  exact walk.nodes_nodup_of_minimal (fun alternative alternativeWalk =>
    minimal target alternative selected alternativeWalk)

/-- Every vertex of a directed walk into a target is itself an ancestor of
that target, via the suffix walk. -/
theorem observedAncestorOf_of_mem_walk
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S)
    {length : Nat} {source target node : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (G.observedDirectedEdge mutilation) length source target)
    (selected : targets target = true)
    (member : node ∈ walk.nodes) :
    G.observedAncestorOf mutilation targets node = true := by
  rcases walk.suffix_of_mem member with ⟨_suffixLength, _bound, suffix⟩
  rcases suffix with ⟨suffix⟩
  have complete :
      forall n : Fin S.count,
        n ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun n => List.mem_ofFn.mpr ⟨n, rfl⟩
  have reachable :
      FiniteReachability.Reachable (G.observedDirectedEdge mutilation)
        node target :=
    ⟨_, ⟨suffix⟩⟩
  have bounded :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge mutilation) finBeq_eq_true_iff complete
      reachable
  exact (G.observedAncestorOf_eq_true_iff mutilation targets node).mpr
    ⟨target, selected, bounded⟩

/-- Ancestry composes: a walk into an intermediate family, each of whose
members already reaches the targets, is a walk into the targets. -/
theorem observedAncestorOf_compose
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (mids targets : NodeSet S) (source : Fin S.count)
    (fromSource : G.observedAncestorOf mutilation mids source = true)
    (fromMids : forall i, mids i = true ->
      G.observedAncestorOf mutilation targets i = true) :
    G.observedAncestorOf mutilation targets source = true := by
  rcases (G.observedAncestorOf_eq_true_iff mutilation mids source).mp
      fromSource with ⟨mid, midSelected, boundedMid⟩
  have midReaches := fromMids mid midSelected
  rcases (G.observedAncestorOf_eq_true_iff mutilation targets mid).mp
      midReaches with ⟨target, targetSelected, boundedTarget⟩
  rcases boundedMid with ⟨_lenMid, _boundMid, walkMid⟩
  rcases walkMid with ⟨walkMid⟩
  rcases boundedTarget with ⟨_lenTarget, _boundTarget, walkTarget⟩
  rcases walkTarget with ⟨walkTarget⟩
  have complete :
      forall n : Fin S.count,
        n ∈ List.ofFn (fun i : Fin S.count => i) :=
    fun n => List.mem_ofFn.mpr ⟨n, rfl⟩
  have reachable :
      FiniteReachability.Reachable (G.observedDirectedEdge mutilation)
        source target :=
    ⟨_, ⟨walkMid.append walkTarget⟩⟩
  have bounded :=
    FiniteReachability.boundedWalk_of_reachable finBeq
      (List.ofFn (fun i : Fin S.count => i))
      (G.observedDirectedEdge mutilation) finBeq_eq_true_iff complete
      reachable
  exact (G.observedAncestorOf_eq_true_iff mutilation targets source).mpr
    ⟨target, targetSelected, bounded⟩

def MoralOpenEdge (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets conditioned : NodeSet S)
    (left right : SeparationNode S) : Bool :=
  !(blockedBy conditioned left) && !(blockedBy conditioned right) &&
    G.ancestralMoralEdge mutilation targets left right

theorem ancestralMoralEdge_of_adjacent (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {left right : SeparationNode S}
    (leftAncestor : G.ancestorOf mutilation targets left = true)
    (rightAncestor : G.ancestorOf mutilation targets right = true)
    (adjacent : PathSpecification.Adjacent G mutilation left right) :
    G.ancestralMoralEdge mutilation targets left right = true := by
  have different : left ≠ right := by
    intro same
    subst right
    rcases adjacent with forward | reverse
    · rw [G.expandedMutilatedEdge_irreflexive mutilation] at forward
      contradiction
    · rw [G.expandedMutilatedEdge_irreflexive mutilation] at reverse
      contradiction
  simp only [ancestralMoralEdge, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true]
  refine ⟨⟨⟨leftAncestor, rightAncestor⟩,
    (SeparationNode.not_beq_eq_true_iff left right).mpr different⟩, ?_⟩
  exact Or.inl adjacent

theorem ancestralMoralEdge_of_collider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {left middle right : SeparationNode S}
    (leftAncestor : G.ancestorOf mutilation targets left = true)
    (middleAncestor : G.ancestorOf mutilation targets middle = true)
    (rightAncestor : G.ancestorOf mutilation targets right = true)
    (different : left ≠ right)
    (collider : PathSpecification.IsCollider G mutilation
      left middle right) :
    G.ancestralMoralEdge mutilation targets left right = true := by
  simp only [ancestralMoralEdge, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true]
  refine ⟨⟨⟨leftAncestor, rightAncestor⟩,
    (SeparationNode.not_beq_eq_true_iff left right).mpr different⟩,
      Or.inr ?_⟩
  exact ⟨middle, SeparationNode.mem_all middle,
    ⟨middleAncestor, collider.1⟩, collider.2⟩

theorem moralOpenEdge_of_ancestral (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {left right : SeparationNode S}
    (leftOpen : blockedBy conditioned left = false)
    (rightOpen : blockedBy conditioned right = false)
    (moral : G.ancestralMoralEdge mutilation targets left right = true) :
    G.MoralOpenEdge mutilation targets conditioned left right = true := by
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨by simp [leftOpen], by simp [rightOpen]⟩,
      moral⟩

theorem PathSpecification.TripleActive.collider_of_blocked
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (conditioned : NodeSet S) (previous middle next : SeparationNode S)
    (active : PathSpecification.TripleActive G mutilation conditioned
      previous middle next)
    (blocked : blockedBy conditioned middle = true) :
    PathSpecification.IsCollider G mutilation previous middle next := by
  rcases active with colliderAndActivated | nonColliderAndOpen
  · exact colliderAndActivated.1
  · have openProof := nonColliderAndOpen.2
    unfold PathSpecification.NonColliderOpen at openProof
    rw [blocked] at openProof
    contradiction

theorem ancestralMoralEdge_symmetric (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {left right : SeparationNode S}
    (edge : G.ancestralMoralEdge mutilation targets left right = true) :
    G.ancestralMoralEdge mutilation targets right left = true := by
  simp only [ancestralMoralEdge, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true] at edge ⊢
  rcases edge with
    ⟨⟨⟨leftAncestor, rightAncestor⟩, different⟩, directOrMoral⟩
  refine ⟨⟨⟨rightAncestor, leftAncestor⟩, ?_⟩, ?_⟩
  · rw [SeparationNode.beq_comm right left]
    exact different
  · rcases directOrMoral with directOrReverse | common
    · rcases directOrReverse with direct | reverse
      · exact Or.inl (Or.inr direct)
      · exact Or.inl (Or.inl reverse)
    · rcases common with
        ⟨child, childMember, ⟨childAncestor, leftParent⟩, rightParent⟩
      exact Or.inr
        ⟨child, childMember, ⟨childAncestor, rightParent⟩, leftParent⟩

theorem moralOpenEdge_symmetric (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {left right : SeparationNode S}
    (edge : G.MoralOpenEdge mutilation targets conditioned left right = true) :
    G.MoralOpenEdge mutilation targets conditioned right left = true := by
  rcases Bool.and_eq_true_iff.mp edge with ⟨openEnds, moral⟩
  rcases Bool.and_eq_true_iff.mp openEnds with ⟨leftOpen, rightOpen⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨rightOpen, leftOpen⟩,
      G.ancestralMoralEdge_symmetric mutilation targets moral⟩

theorem MoralOpenEdge.unpacked (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {left right : SeparationNode S}
    (edge : G.MoralOpenEdge mutilation targets conditioned left right = true) :
    blockedBy conditioned left = false /\
      blockedBy conditioned right = false /\
        G.ancestralMoralEdge mutilation targets left right = true := by
  rcases Bool.and_eq_true_iff.mp edge with ⟨openEnds, moral⟩
  rcases Bool.and_eq_true_iff.mp openEnds with ⟨leftOpen, rightOpen⟩
  exact ⟨by simpa using leftOpen, by simpa using rightOpen, moral⟩

theorem ancestralMoralEdge_cases (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {left right : SeparationNode S}
    (moral : G.ancestralMoralEdge mutilation targets left right = true) :
    PathSpecification.Adjacent G mutilation left right \/
      Exists fun child : SeparationNode S =>
        G.ancestorOf mutilation targets child = true /\
          G.expandedMutilatedEdge mutilation left child = true /\
            G.expandedMutilatedEdge mutilation right child = true := by
  simp only [ancestralMoralEdge, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true] at moral
  rcases moral with ⟨⟨⟨_leftAncestor, _rightAncestor⟩, _different⟩, directOrMoral⟩
  rcases directOrMoral with directOrReverse | common
  · exact Or.inl directOrReverse
  · rcases common with
      ⟨child, _member, ⟨childAncestor, leftParent⟩, rightParent⟩
    exact Or.inr ⟨child, childAncestor, leftParent, rightParent⟩

theorem expandedMutilatedEdge_ne (G : ObservedGraph S)
    (mutilation : GraphMutilation S) {parent child : SeparationNode S}
    (edge : G.expandedMutilatedEdge mutilation parent child = true) :
    parent ≠ child := by
  intro same
  subst child
  rw [G.expandedMutilatedEdge_irreflexive mutilation] at edge
  contradiction

theorem NodeSet.union_eq_true {S : ObservedSignature}
    (X Y : NodeSet S) (i : Fin S.count) :
    NodeSet.union X Y i = true <-> X i = true \/ Y i = true :=
  Bool.or_eq_true_iff

theorem blockedBy_false_of_not_conditioned_ancestor (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {source node : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.expandedMutilatedEdge mutilation) length source node)
    (sourceNotActivated : G.ancestorOf mutilation conditioned source = false) :
    blockedBy conditioned node = false := by
  cases node with
  | latentPair _left _right =>
      simp [blockedBy]
  | observed index =>
      cases selected : conditioned index with
      | false =>
          simp [blockedBy, selected]
      | true =>
          have activated : G.ancestorOf mutilation conditioned source = true := by
            apply (G.ancestorOf_eq_true_iff mutilation conditioned source).mpr
            exact ⟨index, selected,
              FiniteReachability.boundedWalk_of_reachable
                SeparationNode.beq G.separationNodes
                (G.expandedMutilatedEdge mutilation)
                SeparationNode.beq_eq_true_iff SeparationNode.mem_all
                ⟨length, ⟨walk⟩⟩⟩
          rw [activated] at sourceNotActivated
          contradiction

theorem ancestorOf_of_exactWalk (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {length : Nat} {source node : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.expandedMutilatedEdge mutilation) length source node)
    (nodeAncestor : G.ancestorOf mutilation targets node = true) :
    G.ancestorOf mutilation targets source = true := by
  induction walk with
  | refl => exact nodeAncestor
  | step first rest ih =>
      exact G.ancestorOf_prepend mutilation targets first (ih nodeAncestor)

theorem ancestorOf_mem_exactWalk (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {length : Nat} {source node vertex : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.expandedMutilatedEdge mutilation) length source node)
    (member : vertex ∈ walk.nodes)
    (nodeAncestor : G.ancestorOf mutilation targets node = true) :
    G.ancestorOf mutilation targets vertex = true := by
  rcases walk.suffix_of_mem member with ⟨_suffixLength, _bound, suffix⟩
  rcases suffix with ⟨suffix⟩
  exact G.ancestorOf_of_exactWalk mutilation targets suffix nodeAncestor

theorem blockedBy_false_mem_exactWalk (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {source node vertex : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.expandedMutilatedEdge mutilation) length source node)
    (sourceNotActivated : G.ancestorOf mutilation conditioned source = false)
    (member : vertex ∈ walk.nodes) :
    blockedBy conditioned vertex = false := by
  rcases walk.prefix_of_mem member with ⟨_prefixLength, _bound, prefixWalk⟩
  rcases prefixWalk with ⟨prefixWalk⟩
  exact G.blockedBy_false_of_not_conditioned_ancestor mutilation conditioned
    prefixWalk sourceNotActivated

theorem exists_descendant_in_left_or_right (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {node : SeparationNode S}
    (inLarge : G.ancestorOf mutilation
      (NodeSet.union left (NodeSet.union right conditioned)) node = true)
    (notConditionedAncestor :
      G.ancestorOf mutilation conditioned node = false) :
    Exists fun target : Fin S.count =>
      (left target = true \/ right target = true) /\
        conditioned target = false /\
          FiniteReachability.BoundedWalk
            (G.expandedMutilatedEdge mutilation)
            G.separationNodes.length node (.observed target) := by
  rcases (G.ancestorOf_eq_true_iff mutilation
      (NodeSet.union left (NodeSet.union right conditioned)) node).mp
      inLarge with ⟨target, selected, walk⟩
  have selectedSplit :
      left target = true \/ right target = true \/
        conditioned target = true := by
    rcases (NodeSet.union_eq_true left
        (NodeSet.union right conditioned) target).mp selected with
      inLeft | inRightOrCond
    · exact Or.inl inLeft
    · rcases (NodeSet.union_eq_true right conditioned target).mp
          inRightOrCond with inRight | inCond
      · exact Or.inr (Or.inl inRight)
      · exact Or.inr (Or.inr inCond)
  rcases selectedSplit with inLeft | inRight | inCond
  · cases conditionedValue : conditioned target with
    | false => exact ⟨target, Or.inl inLeft, conditionedValue, walk⟩
    | true =>
        have activated : G.ancestorOf mutilation conditioned node = true :=
          (G.ancestorOf_eq_true_iff mutilation conditioned node).mpr
            ⟨target, conditionedValue, walk⟩
        rw [activated] at notConditionedAncestor
        contradiction
  · cases conditionedValue : conditioned target with
    | false => exact ⟨target, Or.inr inRight, conditionedValue, walk⟩
    | true =>
        have activated : G.ancestorOf mutilation conditioned node = true :=
          (G.ancestorOf_eq_true_iff mutilation conditioned node).mpr
            ⟨target, conditionedValue, walk⟩
        rw [activated] at notConditionedAncestor
        contradiction
  · have activated : G.ancestorOf mutilation conditioned node = true :=
      (G.ancestorOf_eq_true_iff mutilation conditioned node).mpr
        ⟨target, inCond, walk⟩
    rw [activated] at notConditionedAncestor
    contradiction

theorem moralOpenEdge_of_directed (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {parent child : SeparationNode S}
    (edge : G.expandedMutilatedEdge mutilation parent child = true)
    (parentAncestor : G.ancestorOf mutilation targets parent = true)
    (childAncestor : G.ancestorOf mutilation targets child = true)
    (parentOpen : blockedBy conditioned parent = false)
    (childOpen : blockedBy conditioned child = false) :
    G.MoralOpenEdge mutilation targets conditioned parent child = true :=
  G.moralOpenEdge_of_ancestral mutilation targets conditioned
    parentOpen childOpen
    (G.ancestralMoralEdge_of_adjacent mutilation targets
      parentAncestor childAncestor (Or.inl edge))

theorem not_collider_of_forward_edges (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {previous middle next : SeparationNode S}
    (intoMiddle : G.expandedMutilatedEdge mutilation previous middle = true)
    (outOfMiddle : G.expandedMutilatedEdge mutilation middle next = true) :
    Not (PathSpecification.IsCollider G mutilation previous middle next) := by
  intro collider
  have rankInto := G.expandedMutilatedEdge_rank_lt mutilation intoMiddle
  have rankOut := G.expandedMutilatedEdge_rank_lt mutilation outOfMiddle
  have rankBack := G.expandedMutilatedEdge_rank_lt mutilation collider.2
  omega


theorem nodup_prefix_append {α : Type _} {before : List α}
    {node : α} {after : List α}
    (simple : (before ++ node :: after).Nodup) :
    (before ++ [node]).Nodup := by
  induction before with
  | nil => simp
  | cons head tail ih =>
      rw [List.cons_append] at simple
      have parts := List.nodup_cons.mp simple
      refine List.nodup_cons.mpr ⟨?_, ih parts.2⟩
      intro member
      apply parts.1
      change head ∈ tail ++ [node] at member
      rw [List.mem_append, List.mem_singleton] at member
      rcases member with inTail | same
      · exact List.mem_append.mpr (Or.inl inTail)
      · subst node
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- The complementary suffix of a simple split remains simple. -/
theorem nodup_suffix_cons {α : Type _} {before : List α}
    {node : α} {after : List α}
    (simple : (before ++ node :: after).Nodup) :
    (node :: after).Nodup := by
  have parts := nodup_of_split simple
  exact List.nodup_cons.mpr ⟨parts.2.2.1, parts.2.2.2.1⟩

theorem take_prefix_append {α : Type _} (before : List α) (node : α)
    (after : List α) :
    (before ++ node :: after).take (before.length + 1) = before ++ [node] := by
  induction before with
  | nil => simp
  | cons head tail ih =>
      simp [ih]

theorem getLast?_snoc {α : Type _} (before : List α) (node : α) :
    (before ++ [node]).getLast? = some node := by
  induction before with
  | nil => simp
  | cons head tail ih =>
      cases tail with
      | nil => simp
      | cons _ _ => simp [List.getLast?_cons]

def splitMemSeparation (node : SeparationNode S) :
    (nodes : List (SeparationNode S)) → node ∈ nodes →
      { p : List (SeparationNode S) × List (SeparationNode S) //
        nodes = p.1 ++ node :: p.2 }
  | [], member => False.elim (by cases member)
  | head :: tail, member =>
      if hbeq : SeparationNode.beq head node = true then
        ⟨([], tail), by
          have same := (SeparationNode.beq_eq_true_iff head node).mp hbeq
          cases same
          simp⟩
      else
        have later : node ∈ tail := by
          simp only [List.mem_cons] at member
          rcases member with same | later
          · cases same
            exact (hbeq ((SeparationNode.beq_eq_true_iff node node).mpr rfl)).elim
          · exact later
        let split := splitMemSeparation node tail later
        ⟨(head :: split.val.1, split.val.2), by
          simpa [List.cons_append] using
            congrArg (List.cons head) split.property⟩

def prefixActivePath (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {conditioned : NodeSet S} {source target node : SeparationNode S}
    (path : PathSpecification.ActivePath G mutilation conditioned source target)
    (member : node ∈ path.nodes)
    (openNode : blockedBy conditioned node = false) :
    PathSpecification.ActivePath G mutilation conditioned source node :=
  let split := splitMemSeparation node path.nodes member
  let before := split.val.1
  let after := split.val.2
  have starts : (before ++ node :: after).head? = some source := by
    rw [← split.property]
    exact path.starts
  have consecutiveFull : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (before ++ node :: after) := by
    rw [← split.property]
    exact path.adjacent
  have activeFull : PathSpecification.InternalTriplesActive G mutilation
      conditioned (before ++ node :: after) := by
    rw [← split.property]
    exact path.internal_active
  have simpleFull : (before ++ node :: after).Nodup := by
    rw [← split.property]
    exact path.simple
  { nodes := before ++ [node]
    starts := by
      cases hbefore : before with
      | nil =>
          simp only [hbefore, List.nil_append, List.head?_cons,
            Option.some.injEq] at starts
          subst node
          simp
      | cons head tail =>
          simpa [hbefore, List.cons_append] using starts
    finishes := getLast?_snoc before node
    simple := nodup_prefix_append simpleFull
    adjacent := PathSpecification.Consecutive.prefix_append before node after
      consecutiveFull
    source_open := path.source_open
    target_open := openNode
    internal_active := by
      have takeEq := take_prefix_append before node after
      have activeTake := PathSpecification.InternalTriplesActive.take activeFull
        (before.length + 1)
      simpa [takeEq] using activeTake }

/-- The complementary suffix of an active path, cut at an open vertex, is
itself an active path.  First-shared forks glue this onto a prefix of the
other trail. -/
def suffixActivePath (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {conditioned : NodeSet S} {source target node : SeparationNode S}
    (path : PathSpecification.ActivePath G mutilation conditioned source target)
    (member : node ∈ path.nodes)
    (openNode : blockedBy conditioned node = false) :
    PathSpecification.ActivePath G mutilation conditioned node target :=
  let split := splitMemSeparation node path.nodes member
  let before := split.val.1
  let after := split.val.2
  have consecutiveFull : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (before ++ node :: after) := by
    rw [← split.property]
    exact path.adjacent
  have activeFull : PathSpecification.InternalTriplesActive G mutilation
      conditioned (before ++ node :: after) := by
    rw [← split.property]
    exact path.internal_active
  have simpleFull : (before ++ node :: after).Nodup := by
    rw [← split.property]
    exact path.simple
  have finishesFull : (before ++ node :: after).getLast? = some target := by
    rw [← split.property]
    exact path.finishes
  { nodes := node :: after
    starts := rfl
    finishes := by
      cases hafter : after with
      | nil =>
          have hfin := finishesFull
          simp [hafter] at hfin
          subst target
          rfl
      | cons _succ _more =>
          have hfin := finishesFull
          simp [hafter, List.getLast?_append] at hfin
          exact hfin
    simple := nodup_suffix_cons simpleFull
    adjacent := by
      have dropped :=
        PathSpecification.Consecutive.drop before.length
          (before ++ node :: after) consecutiveFull
      simpa [drop_append_length] using dropped
    source_open := openNode
    target_open := path.target_open
    internal_active :=
      PathSpecification.InternalTriplesActive.suffix_append before node after
        activeFull }

theorem consecutive_adjacent_of_marriedCount_zero (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {nodes : List (SeparationNode S)}
    (married : PathSpecification.marriedCount G mutilation nodes = 0) :
    PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation) nodes :=
  PathSpecification.Consecutive.adjacent_of_marriedCount_zero married

def activePath_of_simpleMoralWalk (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    (targets conditioned : NodeSet S)
    {source target : SeparationNode S}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation targets conditioned) source target)
    (married : PathSpecification.marriedCount G mutilation walk.walk.nodes = 0)
    (inactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned walk.walk.nodes = 0)
    (sourceOpen : blockedBy conditioned source = false)
    (targetOpen : blockedBy conditioned target = false) :
    PathSpecification.ActivePath G mutilation conditioned source target where
  nodes := walk.walk.nodes
  starts := walk.walk.nodes_head
  finishes := walk.walk.nodes_getLast
  simple := walk.simple
  adjacent := G.consecutive_adjacent_of_marriedCount_zero mutilation married
  source_open := sourceOpen
  target_open := targetOpen
  internal_active :=
    PathSpecification.InternalTriplesActive.of_inactiveColliderCount_zero
      walk.walk.nodes inactive

/-- Computational witness for a moralised collider child. -/
def commonChild? (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S) (left right : SeparationNode S) :
    Option (SeparationNode S) :=
  G.separationNodes.find? (fun child =>
    G.ancestorOf mutilation targets child &&
      G.expandedMutilatedEdge mutilation left child &&
        G.expandedMutilatedEdge mutilation right child)

theorem commonChild?_eq_some (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {left right child : SeparationNode S}
    (found : G.commonChild? mutilation targets left right = some child) :
    G.ancestorOf mutilation targets child = true /\
      G.expandedMutilatedEdge mutilation left child = true /\
        G.expandedMutilatedEdge mutilation right child = true := by
  have pred := List.find?_some found
  rcases Bool.and_eq_true_iff.mp pred with ⟨leftAndAncestor, rightParent⟩
  rcases Bool.and_eq_true_iff.mp leftAndAncestor with
    ⟨childAncestor, leftParent⟩
  exact ⟨childAncestor, leftParent, rightParent⟩

theorem commonChild?_of_married (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {left right : SeparationNode S}
    (moral : G.ancestralMoralEdge mutilation targets left right = true)
    (notAdjacent :
      PathSpecification.adjacentBool G mutilation left right = false) :
    Exists fun child =>
      G.commonChild? mutilation targets left right = some child := by
  simp only [ancestralMoralEdge, Bool.and_eq_true, Bool.or_eq_true] at moral
  rcases moral with ⟨⟨⟨_leftAncestor, _rightAncestor⟩, _different⟩, directOrMoral⟩
  rcases directOrMoral with directOrReverse | commonAny
  · have adjacentTrue :
        PathSpecification.adjacentBool G mutilation left right = true := by
      simpa [PathSpecification.adjacentBool, Bool.or_eq_true] using
        directOrReverse
    rw [notAdjacent] at adjacentTrue
    contradiction
  · cases found : G.commonChild? mutilation targets left right with
    | none =>
        have noneAll := List.find?_eq_none.mp found
        rcases List.any_eq_true.mp commonAny with ⟨child, member, pred⟩
        exact (noneAll child member pred).elim
    | some child => exact ⟨child, rfl⟩

/-- Expand married moral edges by inserting a witnessing collider child. -/
def expandMoralNodes (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets conditioned : NodeSet S) :
    {length : Nat} → {source target : SeparationNode S} →
    FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length source target →
    List (SeparationNode S)
  | _, _, _, .refl node => [node]
  | _, source, _target, .step _first rest =>
      let restNodes :=
        expandMoralNodes G mutilation targets conditioned rest
      if PathSpecification.adjacentBool G mutilation source
          (rest.nodes.headD source) then
        source :: restNodes
      else
        match G.commonChild? mutilation targets source
            (rest.nodes.headD source) with
        | some child => source :: child :: restNodes
        | none => source :: restNodes

theorem expandMoralNodes_head (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {source target : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length source target) :
    (G.expandMoralNodes mutilation targets conditioned walk).head? =
      some source := by
  match walk with
  | .refl node => simp [expandMoralNodes]
  | .step first rest =>
      simp only [expandMoralNodes]
      split
      · simp
      · split <;> simp

theorem expandMoralNodes_ne_nil (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {source target : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length source target) :
    G.expandMoralNodes mutilation targets conditioned walk ≠ [] := by
  have headEq := G.expandMoralNodes_head mutilation targets conditioned walk
  intro empty
  rw [empty] at headEq
  simp at headEq

theorem expandMoralNodes_getLast (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {source target : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length source target) :
    (G.expandMoralNodes mutilation targets conditioned walk).getLast? =
      some target := by
  match walk with
  | .refl node => simp [expandMoralNodes]
  | .step first rest =>
      have restLast :=
        G.expandMoralNodes_getLast mutilation targets conditioned rest
      have restNe :=
        G.expandMoralNodes_ne_nil mutilation targets conditioned rest
      simp only [expandMoralNodes]
      split
      · cases hrest :
            G.expandMoralNodes mutilation targets conditioned rest with
        | nil => exact (restNe hrest).elim
        | cons head tail =>
            simpa [hrest, List.getLast?_cons] using restLast
      · split
        · cases hrest :
              G.expandMoralNodes mutilation targets conditioned rest with
          | nil => exact (restNe hrest).elim
          | cons head tail =>
              simpa [hrest, List.getLast?_cons] using restLast
        · cases hrest :
              G.expandMoralNodes mutilation targets conditioned rest with
          | nil => exact (restNe hrest).elim
          | cons head tail =>
              simpa [hrest, List.getLast?_cons] using restLast

theorem ancestorOf_of_ancestralMoralEdge (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {left right : SeparationNode S}
    (moral : G.ancestralMoralEdge mutilation targets left right = true) :
    G.ancestorOf mutilation targets left = true /\
      G.ancestorOf mutilation targets right = true := by
  simp only [ancestralMoralEdge, Bool.and_eq_true] at moral
  exact ⟨moral.1.1.1, moral.1.1.2⟩

theorem expandMoralNodes_consecutive_adjacent (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {walkSource walkTarget : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length walkSource
        walkTarget) :
    PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (G.expandMoralNodes mutilation targets conditioned walk) := by
  induction walk with
  | refl node => simp [expandMoralNodes, PathSpecification.Consecutive]
  | @step length source middle target first rest ih =>
      have restHead :=
        G.expandMoralNodes_head mutilation targets conditioned rest
      have restNe :=
        G.expandMoralNodes_ne_nil mutilation targets conditioned rest
      have unpacked :=
        MoralOpenEdge.unpacked G mutilation targets conditioned first
      have destHead := rest.nodes_headD (default := source)
      have moralDest :
          G.ancestralMoralEdge mutilation targets source
            (rest.nodes.headD source) = true := by
        rw [destHead]
        exact unpacked.2.2
      unfold expandMoralNodes
      split
      · rename_i adjacentTrue
        cases hrest :
            G.expandMoralNodes mutilation targets conditioned rest with
        | nil => exact (restNe hrest).elim
        | cons head tail =>
            have headEq : head = rest.nodes.headD source := by
              simp [hrest, Option.some.injEq] at restHead
              exact restHead.trans destHead.symm
            subst head
            exact ⟨(PathSpecification.Adjacent_iff_adjacentBool G
                mutilation source (rest.nodes.headD source)).mpr adjacentTrue,
              by simpa [hrest] using ih⟩
      · rename_i adjacentFalse
        have notAdjacent :
            PathSpecification.adjacentBool G mutilation source
              (rest.nodes.headD source) = false :=
          Bool.eq_false_iff.mpr adjacentFalse
        split
        · rename_i child found
          have childEdges :=
            G.commonChild?_eq_some mutilation targets found
          cases hrest :
              G.expandMoralNodes mutilation targets conditioned rest with
          | nil => exact (restNe hrest).elim
          | cons head tail =>
              have headEq : head = rest.nodes.headD source := by
                simp [hrest, Option.some.injEq] at restHead
                exact restHead.trans destHead.symm
              subst head
              exact ⟨Or.inl childEdges.2.1,
                ⟨Or.inr childEdges.2.2, by simpa [hrest] using ih⟩⟩
        · rename_i foundNone
          rcases G.commonChild?_of_married mutilation targets moralDest
              notAdjacent with ⟨_child, someChild⟩
          rw [foundNone] at someChild
          cases someChild

theorem expandMoralNodes_mem_ancestor (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {walkSource walkTarget : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length walkSource
        walkTarget)
    (sourceAncestor : G.ancestorOf mutilation targets walkSource = true)
    {node : SeparationNode S}
    (member : node ∈ G.expandMoralNodes mutilation targets conditioned walk) :
    G.ancestorOf mutilation targets node = true := by
  induction walk generalizing node with
  | refl endpoint =>
      simp [expandMoralNodes] at member
      subst node
      exact sourceAncestor
  | @step length source middle target first rest ih =>
      have unpacked :=
        MoralOpenEdge.unpacked G mutilation targets conditioned first
      have destHead := rest.nodes_headD (default := source)
      have middleAncestor :
          G.ancestorOf mutilation targets middle = true :=
        (G.ancestorOf_of_ancestralMoralEdge mutilation targets
          unpacked.2.2).2
      unfold expandMoralNodes at member
      split at member
      · rcases List.mem_cons.mp member with same | later
        · subst node
          exact sourceAncestor
        · exact ih middleAncestor later
      · split at member
        · rcases List.mem_cons.mp member with same | later
          · subst node
            exact sourceAncestor
          · rcases List.mem_cons.mp later with sameChild | laterRest
            · subst node
              rename_i child found
              exact (G.commonChild?_eq_some mutilation targets found).1
            · exact ih middleAncestor laterRest
        · rcases List.mem_cons.mp member with same | later
          · subst node
            exact sourceAncestor
          · exact ih middleAncestor later

/--
Every consecutive triple on an expansion is either a collider (the window
around an inserted common child) or has an open middle (an original
`MoralOpenEdge` vertex).  In particular a blocked non-collider cannot
appear as the first inactive window of `expandMoralNodes`.
-/
theorem expandMoralNodes_middle_open_or_collider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {walkSource walkTarget : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length walkSource
        walkTarget)
    (before : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (expandEq : G.expandMoralNodes mutilation targets conditioned walk =
      before ++ previous :: middle :: next :: after) :
    PathSpecification.isColliderBool G mutilation previous middle next =
      true ∨
      blockedBy conditioned middle = false := by
  induction walk generalizing before previous middle next after with
  | refl node =>
      simp [expandMoralNodes] at expandEq
      have lenEq := congrArg List.length expandEq
      simp [List.length_append, List.length_cons] at lenEq
      omega
  | @step length source dest target first rest ih =>
      have restHead :=
        G.expandMoralNodes_head mutilation targets conditioned rest
      have restNe :=
        G.expandMoralNodes_ne_nil mutilation targets conditioned rest
      have unpacked :=
        MoralOpenEdge.unpacked G mutilation targets conditioned first
      have destHead := rest.nodes_headD (default := source)
      have destOpen : blockedBy conditioned dest = false := unpacked.2.1
      have moralDest :
          G.ancestralMoralEdge mutilation targets source
            (rest.nodes.headD source) = true := by
        rw [destHead]
        exact unpacked.2.2
      unfold expandMoralNodes at expandEq
      split at expandEq
      · cases before with
        | nil =>
            injection expandEq with previousEq restEq
            subst previous
            cases hrest :
                G.expandMoralNodes mutilation targets conditioned rest with
            | nil => exact (restNe hrest).elim
            | cons head tail =>
                rw [hrest] at restEq restHead
                injection restEq with middleEq afterEq
                subst middle
                simp only [List.head?_cons, Option.some.injEq] at restHead
                subst head
                exact Or.inr destOpen
        | cons _front frontRest =>
            simp [List.cons_append] at expandEq
            rcases expandEq with ⟨rfl, restEq⟩
            exact ih frontRest previous middle next after restEq
      · rename_i adjacentFalse
        have notAdjacent :
            PathSpecification.adjacentBool G mutilation source
              (rest.nodes.headD source) = false :=
          Bool.eq_false_iff.mpr adjacentFalse
        split at expandEq
        · rename_i child found
          have childEdges :=
            G.commonChild?_eq_some mutilation targets found
          cases before with
          | nil =>
              injection expandEq with previousEq restEq
              subst previous
              injection restEq with middleEq afterEq
              subst middle
              cases hrest :
                  G.expandMoralNodes mutilation targets conditioned rest with
              | nil => exact (restNe hrest).elim
              | cons head tail =>
                  rw [hrest] at afterEq restHead
                  injection afterEq with nextEq _tailEq
                  subst next
                  simp only [List.head?_cons, Option.some.injEq] at restHead
                  subst head
                  refine Or.inl ?_
                  simp [PathSpecification.isColliderBool]
                  exact ⟨childEdges.2.1, by
                    rw [← destHead]
                    exact childEdges.2.2⟩
          | cons _front frontRest =>
              cases frontRest with
              | nil =>
                  simp [List.cons_append] at expandEq
                  rcases expandEq with ⟨rfl, restEq⟩
                  rcases restEq with ⟨rfl, afterEq⟩
                  cases hrest :
                      G.expandMoralNodes mutilation targets conditioned rest with
                  | nil => exact (restNe hrest).elim
                  | cons head tail =>
                      rw [hrest] at afterEq restHead
                      injection afterEq with middleEq _tailEq
                      subst middle
                      simp only [List.head?_cons, Option.some.injEq] at restHead
                      subst head
                      exact Or.inr destOpen
              | cons _second later =>
                  simp [List.cons_append] at expandEq
                  rcases expandEq with ⟨rfl, restEq⟩
                  rcases restEq with ⟨rfl, afterEq⟩
                  exact ih later previous middle next after afterEq
        · rename_i foundNone
          rcases G.commonChild?_of_married mutilation targets moralDest
              notAdjacent with ⟨_child, someChild⟩
          rw [foundNone] at someChild
          cases someChild

/-- Every consecutive window of a moral expansion is a collider or has an
open middle.  Direct from the window-wise expansion lemma. -/
theorem expandMoralNodes_tripleOpenOrCollider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {walkSource walkTarget : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length walkSource
        walkTarget) :
    PathSpecification.TripleOpenOrCollider G mutilation conditioned
      (G.expandMoralNodes mutilation targets conditioned walk) :=
  PathSpecification.TripleOpenOrCollider.of_every_window _
    (fun before previous middle next after eq =>
      G.expandMoralNodes_middle_open_or_collider mutilation targets
        conditioned walk before previous middle next after eq)

theorem consecutive_adjacent_of_directedWalk (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {length : Nat} {source target : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.expandedMutilatedEdge mutilation) length source target) :
    PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation) walk.nodes :=
  PathSpecification.Consecutive.mono
    (fun _left _right edge => Or.inl edge) walk.nodes
    walk.nodes_consecutive

theorem internal_active_of_directed_open (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {walkSource walkTarget : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.expandedMutilatedEdge mutilation) length walkSource walkTarget)
    (openNodes : forall vertex, vertex ∈ walk.nodes ->
      blockedBy conditioned vertex = false) :
    PathSpecification.InternalTriplesActive G mutilation conditioned
      walk.nodes := by
  induction walk with
  | refl node =>
      simp [FiniteReachability.ExactWalk.nodes]
      exact PathSpecification.InternalTriplesActive.singleton node
  | @step length source middle target first rest ih =>
      cases rest with
      | refl _ =>
          simp [FiniteReachability.ExactWalk.nodes]
          exact PathSpecification.InternalTriplesActive.pair source middle
      | @step restLength _ restNext _ second tail =>
          have middleOpen := openNodes middle (by
            simp [FiniteReachability.ExactWalk.nodes])
          have notCollider :=
            G.not_collider_of_forward_edges mutilation first second
          have triple :
              PathSpecification.TripleActive G mutilation conditioned
                source middle restNext :=
            Or.inr ⟨notCollider, middleOpen⟩
          have tailSplit : Exists fun suffix =>
              tail.nodes = restNext :: suffix := by
            cases hnodes : tail.nodes with
            | nil => exact (tail.nodes_ne_nil hnodes).elim
            | cons head suffix =>
                have headEq := tail.nodes_head
                simp [hnodes] at headEq
                subst head
                exact ⟨suffix, rfl⟩
          rcases tailSplit with ⟨suffix, split⟩
          have restOpen : forall vertex,
              vertex ∈ (FiniteReachability.ExactWalk.step second tail).nodes ->
                blockedBy conditioned vertex = false := by
            intro vertex member
            have member' : vertex = middle ∨ vertex ∈ tail.nodes := by
              simpa [FiniteReachability.ExactWalk.nodes] using member
            exact openNodes vertex (by
              simp [FiniteReachability.ExactWalk.nodes]
              exact Or.inr member')
          have restActive := ih restOpen
          have restNodes :
              (FiniteReachability.ExactWalk.step second tail).nodes =
                middle :: restNext :: suffix := by
            simp [FiniteReachability.ExactWalk.nodes, split]
          rw [restNodes] at restActive
          simpa [FiniteReachability.ExactWalk.nodes, split] using
            PathSpecification.InternalTriplesActive.step triple restActive

def nodupSeparation : List (SeparationNode S) -> Bool
  | [] => true
  | x :: xs =>
      !(xs.any (fun y => SeparationNode.beq y x)) && nodupSeparation xs

def cutCycle : List (SeparationNode S) -> List (SeparationNode S)
  | [] => []
  | x :: xs =>
      match xs.findIdx? (fun y => SeparationNode.beq y x) with
      | none => x :: cutCycle xs
      | some idx => x :: xs.drop (idx + 1)

theorem findIdx?_some_lt {α} {p : α → Bool} :
    forall xs : List α, forall idx : Nat,
      xs.findIdx? p = some idx -> idx < xs.length
  | [], idx, h => by simp at h
  | x :: xs, idx, h => by
      rw [List.findIdx?_cons] at h
      split at h
      · cases h
        exact Nat.zero_lt_succ _
      · cases htail : xs.findIdx? p with
        | none => simp [htail] at h
        | some j =>
            simp [htail] at h
            cases h
            exact Nat.succ_lt_succ (findIdx?_some_lt xs j htail)

theorem findIdx?_of_any {α} {p : α → Bool} :
    forall xs : List α, xs.any p = true ->
      Exists fun idx => xs.findIdx? p = some idx
  | [], h => by simp at h
  | x :: xs, h => by
      cases hx : p x with
      | true =>
          exact ⟨0, by simp [List.findIdx?_cons, hx]⟩
      | false =>
          have tailAny : xs.any p = true := by
            simpa [List.any_cons, hx] using h
          rcases findIdx?_of_any xs tailAny with ⟨j, hj⟩
          refine ⟨j + 1, ?_⟩
          simp [List.findIdx?_cons, hx, hj]

theorem cutCycle_length_le :
    forall nodes : List (SeparationNode S),
      (cutCycle nodes).length <= nodes.length
  | [] => by simp [cutCycle]
  | x :: xs => by
      cases hidx :
          xs.findIdx? (fun y => SeparationNode.beq y x) with
      | none =>
          simpa [cutCycle, hidx] using cutCycle_length_le xs
      | some idx =>
          have idxBound : idx < xs.length := findIdx?_some_lt xs idx hidx
          simp [cutCycle, hidx, List.length_drop]
          try omega

theorem cutCycle_length_lt :
    forall nodes : List (SeparationNode S),
      nodupSeparation nodes = false ->
        (cutCycle nodes).length < nodes.length
  | [] => by
      intro h
      simp [nodupSeparation] at h
  | x :: xs => by
      intro h
      simp only [nodupSeparation] at h
      cases hany : xs.any (fun y => SeparationNode.beq y x) with
      | true =>
          rcases findIdx?_of_any xs hany with ⟨idx, hidx⟩
          have idxBound : idx < xs.length := findIdx?_some_lt xs idx hidx
          simp [cutCycle, hidx, List.length_drop]
          omega
      | false =>
          have tailFalse : nodupSeparation xs = false := by
            simp [hany] at h
            exact h
          cases hidx :
              xs.findIdx? (fun y => SeparationNode.beq y x) with
          | none =>
              simpa [cutCycle, hidx] using cutCycle_length_lt xs tailFalse
          | some idx =>
              have idxBound : idx < xs.length := findIdx?_some_lt xs idx hidx
              simp [cutCycle, hidx, List.length_drop]
              omega

/-- Drop repeated vertices by iterating `cutCycle` at most `nodes.length` times. -/
def simplifySeparation.go :
    Nat → List (SeparationNode S) → List (SeparationNode S)
  | 0, nodes => nodes
  | n + 1, nodes =>
      if nodupSeparation nodes = true then nodes
      else simplifySeparation.go n (cutCycle nodes)

def simplifySeparation (nodes : List (SeparationNode S)) :
    List (SeparationNode S) :=
  simplifySeparation.go nodes.length nodes

/--
A simple open moral walk that is already a DAG adjacency walk with every
internal triple active is an active path between its observed endpoints.
-/
theorem exists_activePath_of_zero_measure (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (married : PathSpecification.marriedCount G mutilation walk.walk.nodes = 0)
    (inactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned walk.walk.nodes = 0)
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        (.observed sourceIdx) (.observed targetIdx)) :=
  ⟨G.activePath_of_simpleMoralWalk mutilation
    (NodeSet.union left (NodeSet.union right conditioned)) conditioned
    walk married inactive sourceOpen targetOpen⟩

theorem cutCycle_head :
    forall nodes : List (SeparationNode S),
      nodes ≠ [] -> (cutCycle nodes).head? = nodes.head?
  | [], ne => (ne rfl).elim
  | x :: xs, _ne => by
      cases hidx :
          xs.findIdx? (fun y => SeparationNode.beq y x) with
      | none => simp [cutCycle, hidx]
      | some idx => simp [cutCycle, hidx]

theorem cutCycle_ne_nil (nodes : List (SeparationNode S))
    (ne : nodes ≠ []) : cutCycle nodes ≠ [] := by
  have headEq := cutCycle_head nodes ne
  cases hcut : cutCycle nodes with
  | nil =>
      simp [hcut] at headEq
      cases nodes with
      | nil => exact (ne rfl).elim
      | cons _ _ => simp at headEq
  | cons _ _ => intro h; cases h

theorem findIdx?_some_pred {α} {p : α → Bool} {xs : List α} {idx : Nat}
    (h : xs.findIdx? p = some idx) (bound : idx < xs.length) :
    p xs[idx] = true := by
  induction xs generalizing idx with
  | nil => exact (Nat.not_lt_zero idx bound).elim
  | cons x xs ih =>
      rw [List.findIdx?_cons] at h
      split at h
      · cases h
        assumption
      · cases htail : xs.findIdx? p with
        | none => simp [htail] at h
        | some j =>
            simp [htail] at h
            cases h
            have jbound : j < xs.length := findIdx?_some_lt xs j htail
            simpa [List.getElem_cons_succ] using ih htail jbound

theorem getLast?_drop_eq {α} {n : Nat} {xs : List α}
    (bound : n < xs.length) :
    (xs.drop n).getLast? = xs.getLast? := by
  rw [List.getLast?_drop]
  have : ¬ xs.length ≤ n := Nat.not_le.mpr bound
  simp [this]

theorem mem_cutCycle {node : SeparationNode S} :
    forall nodes : List (SeparationNode S),
      node ∈ cutCycle nodes -> node ∈ nodes
  | [], member => by simp [cutCycle] at member
  | x :: xs, member => by
      cases hidx :
          xs.findIdx? (fun y => SeparationNode.beq y x) with
      | none =>
          simp [cutCycle, hidx] at member
          rcases member with same | later
          · subst node
            simp
          · exact List.mem_cons_of_mem _ (mem_cutCycle xs later)
      | some idx =>
          simp [cutCycle, hidx] at member
          rcases member with same | later
          · subst node
            simp
          · exact List.mem_cons_of_mem _
              (List.mem_of_mem_drop later)

theorem nodupSeparation_eq_true_iff :
    forall nodes : List (SeparationNode S),
      nodupSeparation nodes = true <-> nodes.Nodup
  | [] => by simp [nodupSeparation]
  | x :: xs => by
      simp only [nodupSeparation, Bool.and_eq_true, Bool.not_eq_true',
        List.nodup_cons]
      constructor
      · intro ⟨notLater, tail⟩
        constructor
        · intro member
          have later :
              xs.any (fun y => SeparationNode.beq y x) = true := by
            refine List.any_eq_true.mpr ⟨x, member, ?_⟩
            exact (SeparationNode.beq_eq_true_iff x x).mpr rfl
          rw [later] at notLater
          contradiction
        · exact (nodupSeparation_eq_true_iff xs).mp tail
      · intro ⟨notLater, tail⟩
        constructor
        · cases hany : xs.any (fun y => SeparationNode.beq y x) with
          | false => rfl
          | true =>
              rcases List.any_eq_true.mp hany with ⟨y, member, same⟩
              have eqY : y = x :=
                (SeparationNode.beq_eq_true_iff y x).mp same
              subst y
              exact (notLater member).elim
        · exact (nodupSeparation_eq_true_iff xs).mpr tail

theorem cutCycle_getLast :
    forall nodes : List (SeparationNode S),
      nodes ≠ [] -> (cutCycle nodes).getLast? = nodes.getLast?
  | [], ne => (ne rfl).elim
  | x :: xs, _ne => by
      cases hidx :
          xs.findIdx? (fun y => SeparationNode.beq y x) with
      | none =>
          cases xs with
          | nil => simp [cutCycle, hidx]
          | cons y ys =>
              have tailLast :=
                cutCycle_getLast (y :: ys) (List.cons_ne_nil _ _)
              have cutEq : cutCycle (x :: y :: ys) =
                  x :: cutCycle (y :: ys) := by
                simp [cutCycle, hidx]
              have cutNe :=
                cutCycle_ne_nil (y :: ys) (List.cons_ne_nil _ _)
              cases hcut : cutCycle (y :: ys) with
              | nil => exact (cutNe hcut).elim
              | cons z zs =>
                  rw [cutEq, hcut]
                  have tailLast' : (z :: zs).getLast? = (y :: ys).getLast? := by
                    rw [← hcut]
                    exact tailLast
                  simpa [List.getLast?_cons_cons] using tailLast'
      | some idx =>
          have idxBound : idx < xs.length := findIdx?_some_lt xs idx hidx
          have cutEq : cutCycle (x :: xs) = x :: xs.drop (idx + 1) := by
            simp [cutCycle, hidx]
          rw [cutEq]
          cases hdrop : xs.drop (idx + 1) with
          | nil =>
              have duplicate :
                  SeparationNode.beq xs[idx] x = true :=
                findIdx?_some_pred hidx idxBound
              have duplicateEq : xs[idx] = x :=
                (SeparationNode.beq_eq_true_iff _ _).mp duplicate
              have dropIdx :
                  xs.drop idx = x :: xs.drop (idx + 1) := by
                rw [List.drop_eq_getElem_cons idxBound, duplicateEq]
              have lastAtDup : (xs.drop idx).getLast? = some x := by
                simp [dropIdx, hdrop]
              have lastXs : xs.getLast? = some x := by
                have := getLast?_drop_eq idxBound
                rw [← this]
                exact lastAtDup
              cases xs with
              | nil => simp at idxBound
              | cons _ _ =>
                  simpa [List.getLast?_cons] using lastXs.symm
          | cons z zs =>
              have nlt : idx + 1 < xs.length := by
                have dropLen : (xs.drop (idx + 1)).length =
                    xs.length - (idx + 1) := by
                  simp [List.length_drop]
                simp [hdrop] at dropLen
                omega
              have dropLast := getLast?_drop_eq nlt
              cases xs with
              | nil => simp at hdrop
              | cons _ _ =>
                  simp [hdrop] at dropLast
                  simpa [List.getLast?_cons_cons, List.getLast?_cons]
                    using dropLast

/-- Cycle deletion preserves consecutive relatedness: every remaining
adjacent pair was already an edge of the original walk. -/
theorem consecutive_cutCycle {relation : SeparationNode S → SeparationNode S → Prop}
    (nodes : List (SeparationNode S))
    (hcons : PathSpecification.Consecutive relation nodes) :
    PathSpecification.Consecutive relation (cutCycle nodes) := by
  match nodes with
  | [] => simp [cutCycle, PathSpecification.Consecutive]
  | [x] => simp [cutCycle, PathSpecification.Consecutive]
  | x :: y :: rest =>
      cases hidx :
          (y :: rest).findIdx? (fun z => SeparationNode.beq z x) with
      | none =>
          have tailCut := consecutive_cutCycle (y :: rest) hcons.2
          have headEq : (cutCycle (y :: rest)).head? = some y :=
            cutCycle_head (y :: rest) (List.cons_ne_nil _ _)
          cases hcut : cutCycle (y :: rest) with
          | nil =>
              exact (cutCycle_ne_nil (y :: rest) (List.cons_ne_nil _ _) hcut).elim
          | cons z zs =>
              have zEq : z = y := by
                have : (cutCycle (y :: rest)).head? = some y := headEq
                simp [hcut] at this
                exact this
              subst z
              have cutEq : cutCycle (x :: y :: rest) = x :: y :: zs := by
                simp only [cutCycle, hidx]
                exact congrArg (List.cons x) hcut
              rw [cutEq]
              exact ⟨hcons.1, by simpa [hcut] using tailCut⟩
      | some idx =>
          have idxBound : idx < (y :: rest).length :=
            findIdx?_some_lt (y :: rest) idx hidx
          have duplicate :
              SeparationNode.beq ((y :: rest)[idx]) x = true :=
            findIdx?_some_pred hidx idxBound
          have duplicateEq : (y :: rest)[idx] = x :=
            (SeparationNode.beq_eq_true_iff _ _).mp duplicate
          have dropCons := PathSpecification.Consecutive.drop (idx + 1)
            (y :: rest) hcons.2
          cases hdrop : (y :: rest).drop (idx + 1) with
          | nil =>
              simp [cutCycle, hidx, hdrop, PathSpecification.Consecutive]
          | cons z zs =>
              have pair : relation x z := by
                have consYs := hcons.2
                have split :
                    y :: rest =
                      (y :: rest).take idx ++ x :: z :: zs := by
                  calc y :: rest
                      = (y :: rest).take idx ++ (y :: rest).drop idx :=
                          (List.take_append_drop idx (y :: rest)).symm
                    _ = (y :: rest).take idx ++
                          (y :: rest)[idx] :: (y :: rest).drop (idx + 1) := by
                          rw [List.drop_eq_getElem_cons idxBound]
                    _ = (y :: rest).take idx ++ x :: z :: zs := by
                          rw [duplicateEq, hdrop]
                rw [split] at consYs
                exact PathSpecification.Consecutive.pair_of_append
                  ((y :: rest).take idx) zs x z consYs
              have cutEq : cutCycle (x :: y :: rest) = x :: z :: zs := by
                simp [cutCycle, hidx, hdrop]
              rw [cutEq]
              exact ⟨pair, by simpa [hdrop] using dropCons⟩
termination_by nodes.length

/--
Cycle deletion preserves collider-or-open middles along a DAG-adjacent
trail.  Copied windows are original consecutive triples.  A splice
`(x, y, w)` at a blocked `y` reuses the two original incoming parents:
the first window supplies `x → y` and the window at the second copy of
`y` supplies `w → y`.
-/
theorem cutCycle_tripleOpenOrCollider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (nodes : List (SeparationNode S))
    (hcons : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation) nodes)
    (hopen : PathSpecification.TripleOpenOrCollider G mutilation
      conditioned nodes) :
    PathSpecification.TripleOpenOrCollider G mutilation conditioned
      (cutCycle nodes) := by
  match nodes with
  | [] => trivial
  | [_] => trivial
  | x :: y :: rest =>
      cases rest with
      | nil =>
          cases hidx :
              [y].findIdx? (fun z => SeparationNode.beq z x) with
          | none =>
              simp [cutCycle, hidx]
              trivial
          | some idx =>
              have idxBound : idx < [y].length :=
                findIdx?_some_lt [y] idx hidx
              have duplicate :
                  SeparationNode.beq ([y][idx]) x = true :=
                findIdx?_some_pred hidx idxBound
              have yEq : y = x := by
                have : idx = 0 := by simp at idxBound; exact idxBound
                subst idx
                exact (SeparationNode.beq_eq_true_iff y x).mp duplicate
              subst y
              exact (G.adjacent_irrefl mutilation x hcons.1).elim
      | cons z0 rest' =>
          have first := hopen.1
          have tailOpen :
              PathSpecification.TripleOpenOrCollider G mutilation
                conditioned (y :: z0 :: rest') :=
            hopen.2
          cases hidx :
              (y :: z0 :: rest').findIdx? (fun z => SeparationNode.beq z x)
              with
          | none =>
              have tailCut :=
                cutCycle_tripleOpenOrCollider G mutilation conditioned
                  (y :: z0 :: rest') hcons.2 tailOpen
              have headEq :
                  (cutCycle (y :: z0 :: rest')).head? = some y :=
                cutCycle_head (y :: z0 :: rest') (List.cons_ne_nil _ _)
              cases hcut : cutCycle (y :: z0 :: rest') with
              | nil =>
                  exact (cutCycle_ne_nil (y :: z0 :: rest')
                    (List.cons_ne_nil _ _) hcut).elim
              | cons z zs =>
                  have zEq : z = y := by
                    simp [hcut] at headEq
                    exact headEq
                  subst z
                  have cutEq :
                      cutCycle (x :: y :: z0 :: rest') = x :: y :: zs := by
                    simp only [cutCycle, hidx]
                    exact congrArg (List.cons x) hcut
                  rw [cutEq]
                  cases zs with
                  | nil => trivial
                  | cons w more =>
                      have tail' :
                          PathSpecification.TripleOpenOrCollider G
                            mutilation conditioned (y :: w :: more) := by
                        simpa [hcut] using tailCut
                      refine ⟨?_, tail'⟩
                      cases openY : blockedBy conditioned y with
                      | false => exact Or.inr rfl
                      | true =>
                          have origCollider :
                              PathSpecification.isColliderBool G mutilation
                                x y z0 = true := by
                            rcases first with c | openMiddle
                            · exact c
                            · rw [openY] at openMiddle
                              cases openMiddle
                          cases hidxY :
                              (z0 :: rest').findIdx?
                                (fun z => SeparationNode.beq z y) with
                          | none =>
                              have cutDef :
                                  cutCycle (y :: z0 :: rest') =
                                    y :: cutCycle (z0 :: rest') := by
                                simp [cutCycle, hidxY]
                              rw [cutDef] at hcut
                              injection hcut with _ restCut
                              have wEq : w = z0 := by
                                have hd :=
                                  cutCycle_head (z0 :: rest')
                                    (List.cons_ne_nil _ _)
                                rw [restCut] at hd
                                simp at hd
                                exact hd
                              subst w
                              exact Or.inl origCollider
                          | some idxY =>
                              have cutDef :
                                  cutCycle (y :: z0 :: rest') =
                                    y :: (z0 :: rest').drop (idxY + 1) := by
                                simp [cutCycle, hidxY]
                              rw [cutDef] at hcut
                              injection hcut with _ dropEq
                              have idxBoundY :
                                  idxY < (z0 :: rest').length :=
                                findIdx?_some_lt (z0 :: rest') idxY hidxY
                              have dupY :
                                  SeparationNode.beq
                                    ((z0 :: rest')[idxY]) y = true :=
                                findIdx?_some_pred hidxY idxBoundY
                              have dupEq : (z0 :: rest')[idxY] = y :=
                                (SeparationNode.beq_eq_true_iff _ _).mp dupY
                              cases idxY with
                              | zero =>
                                  have z0Eq : z0 = y := by
                                    simpa using dupEq
                                  subst z0
                                  exact (G.adjacent_irrefl mutilation y
                                    hcons.2.1).elim
                              | succ k =>
                                  have boundK1 :
                                      k + 1 < (y :: z0 :: rest').length :=
                                    Nat.lt_succ_of_lt idxBoundY
                                  have dropTail :
                                      (y :: z0 :: rest').drop (k + 2) =
                                        y :: w :: more := by
                                    have tdrop :
                                        (y :: z0 :: rest').drop (k + 2) =
                                          (z0 :: rest').drop (k + 1) := rfl
                                    have dcons :
                                        (z0 :: rest').drop (k + 1) =
                                          (z0 :: rest')[k + 1]'idxBoundY ::
                                            (z0 :: rest').drop (k + 2) :=
                                      List.drop_eq_getElem_cons idxBoundY
                                    have atY :
                                        (z0 :: rest')[k + 1]'idxBoundY = y :=
                                      dupEq
                                    rw [tdrop, dcons, atY, dropEq]
                                  have splitT :
                                      y :: z0 :: rest' =
                                        (y :: z0 :: rest').take (k + 1) ++
                                          (y :: z0 :: rest')[k + 1]'boundK1 ::
                                            y :: w :: more := by
                                    have td :=
                                      List.take_append_drop (k + 1)
                                        (y :: z0 :: rest')
                                    have dconsT :=
                                      List.drop_eq_getElem_cons boundK1
                                    calc y :: z0 :: rest'
                                        = (y :: z0 :: rest').take (k + 1) ++
                                            (y :: z0 :: rest').drop
                                              (k + 1) := td.symm
                                      _ = (y :: z0 :: rest').take (k + 1) ++
                                            (y :: z0 :: rest')[k + 1]'boundK1 ::
                                              (y :: z0 :: rest').drop
                                                (k + 2) := by
                                          rw [dconsT]
                                      _ = (y :: z0 :: rest').take (k + 1) ++
                                            (y :: z0 :: rest')[k + 1]'boundK1 ::
                                              y :: w :: more := by
                                          rw [dropTail]
                                  have window :=
                                    PathSpecification.TripleOpenOrCollider.of_append
                                      ((y :: z0 :: rest').take (k + 1))
                                      ((y :: z0 :: rest')[k + 1]'boundK1) y w
                                      more
                                      (by
                                        rw [← splitT]
                                        exact tailOpen)
                                  have secondCollider :
                                      PathSpecification.isColliderBool G
                                        mutilation
                                        ((y :: z0 :: rest')[k + 1]'boundK1) y w =
                                          true := by
                                    rcases window with c | openMiddle
                                    · exact c
                                    · rw [openY] at openMiddle
                                      cases openMiddle
                                  have xy :
                                      G.expandedMutilatedEdge mutilation x y =
                                        true :=
                                    (Bool.and_eq_true_iff.mp origCollider).1
                                  have wy :
                                      G.expandedMutilatedEdge mutilation w y =
                                        true :=
                                    (Bool.and_eq_true_iff.mp secondCollider).2
                                  refine Or.inl ?_
                                  simp [PathSpecification.isColliderBool, xy, wy]
          | some idx =>
              have idxBound : idx < (y :: z0 :: rest').length :=
                findIdx?_some_lt (y :: z0 :: rest') idx hidx
              have duplicate :
                  SeparationNode.beq ((y :: z0 :: rest')[idx]) x = true :=
                findIdx?_some_pred hidx idxBound
              have duplicateEq : (y :: z0 :: rest')[idx] = x :=
                (SeparationNode.beq_eq_true_iff _ _).mp duplicate
              cases idx with
              | zero =>
                  have yEq : y = x := by
                    simpa using duplicateEq
                  subst y
                  exact (G.adjacent_irrefl mutilation x hcons.1).elim
              | succ k =>
                  cases hdrop :
                      (y :: z0 :: rest').drop (k + 2) with
                  | nil =>
                      simp [cutCycle, hidx, hdrop]
                      trivial
                  | cons z zs =>
                      cases zs with
                      | nil =>
                          simp [cutCycle, hidx, hdrop]
                          trivial
                      | cons w more =>
                          have split :
                              y :: z0 :: rest' =
                                (y :: z0 :: rest').take (k + 1) ++
                                  x :: z :: w :: more := by
                            have td :=
                              List.take_append_drop (k + 1)
                                (y :: z0 :: rest')
                            have de :
                                (y :: z0 :: rest').drop (k + 1) =
                                  x :: z :: w :: more := by
                              have dcons :=
                                List.drop_eq_getElem_cons idxBound
                              calc (y :: z0 :: rest').drop (k + 1)
                                  = (y :: z0 :: rest')[k + 1] ::
                                      (y :: z0 :: rest').drop (k + 2) := dcons
                                _ = x :: (y :: z0 :: rest').drop (k + 2) := by
                                    rw [duplicateEq]
                                _ = x :: z :: w :: more := by
                                    rw [hdrop]
                            calc y :: z0 :: rest'
                                = (y :: z0 :: rest').take (k + 1) ++
                                    (y :: z0 :: rest').drop (k + 1) :=
                                  td.symm
                              _ = (y :: z0 :: rest').take (k + 1) ++
                                    x :: z :: w :: more := by
                                  rw [de]
                          have cutEq :
                              cutCycle (x :: y :: z0 :: rest') =
                                x :: z :: w :: more := by
                            simp [cutCycle, hidx, hdrop]
                          rw [cutEq]
                          let front := (y :: z0 :: rest').take (k + 1)
                          have split' :
                              y :: z0 :: rest' =
                                front ++ x :: z :: w :: more := split
                          have full :
                              x :: y :: z0 :: rest' =
                                (x :: front) ++ x :: z :: w :: more := by
                            calc x :: y :: z0 :: rest'
                                = x :: (front ++ x :: z :: w :: more) := by
                                  rw [split']
                              _ = (x :: front) ++ x :: z :: w :: more := by
                                  rw [List.cons_append]
                          have firstWindow :=
                            PathSpecification.TripleOpenOrCollider.of_append
                              (x :: front) x z w more
                              (by
                                rw [← full]
                                exact hopen)
                          have full2 :
                              x :: y :: z0 :: rest' =
                                (x :: front ++ [x]) ++ z :: w :: more := by
                            calc x :: y :: z0 :: rest'
                                = (x :: front) ++ x :: z :: w :: more := full
                              _ = (x :: front ++ [x]) ++ z :: w :: more :=
                                  (List.append_assoc (x :: front) [x]
                                    (z :: w :: more)).symm
                          have suffixOpen :=
                            PathSpecification.TripleOpenOrCollider.suffix_of_append
                              (x :: front ++ [x]) z (w :: more)
                              (by
                                rw [← full2]
                                exact hopen)
                          exact ⟨firstWindow, suffixOpen⟩
termination_by nodes.length

theorem simplifySeparation.go_consecutive
    {relation : SeparationNode S → SeparationNode S → Prop} :
    forall (fuel : Nat) (nodes : List (SeparationNode S)),
      PathSpecification.Consecutive relation nodes ->
        PathSpecification.Consecutive relation
          (simplifySeparation.go fuel nodes)
  | 0, nodes, hcons => by
      simpa [simplifySeparation.go] using hcons
  | fuel + 1, nodes, hcons => by
      simp only [simplifySeparation.go]
      split
      · exact hcons
      · exact simplifySeparation.go_consecutive fuel (cutCycle nodes)
          (consecutive_cutCycle nodes hcons)

theorem simplifySeparation.go_nodup :
    forall (fuel : Nat) (nodes : List (SeparationNode S)),
      nodes.length <= fuel ->
        (simplifySeparation.go fuel nodes).Nodup
  | 0, nodes, bound => by
      cases nodes with
      | nil => simp [simplifySeparation.go]
      | cons _ _ =>
          simp [List.length_cons] at bound
  | fuel + 1, nodes, bound => by
      simp only [simplifySeparation.go]
      split
      · rename_i hnodup
        exact (nodupSeparation_eq_true_iff nodes).mp hnodup
      · rename_i hnot
        have hfalse : nodupSeparation nodes = false :=
          Bool.eq_false_iff.mpr hnot
        have shorter := cutCycle_length_lt nodes hfalse
        have boundCut : (cutCycle nodes).length <= fuel :=
          Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le shorter bound)
        exact simplifySeparation.go_nodup fuel (cutCycle nodes) boundCut

theorem simplifySeparation.go_head :
    forall (fuel : Nat) (nodes : List (SeparationNode S)),
      nodes ≠ [] ->
        (simplifySeparation.go fuel nodes).head? = nodes.head?
  | 0, nodes, ne => by
      simp [simplifySeparation.go]
  | fuel + 1, nodes, ne => by
      simp only [simplifySeparation.go]
      split
      · rfl
      · have cutNe := cutCycle_ne_nil nodes ne
        have cutHead := cutCycle_head nodes ne
        have ih := simplifySeparation.go_head fuel (cutCycle nodes) cutNe
        exact ih.trans cutHead

theorem simplifySeparation.go_getLast :
    forall (fuel : Nat) (nodes : List (SeparationNode S)),
      nodes ≠ [] ->
        (simplifySeparation.go fuel nodes).getLast? = nodes.getLast?
  | 0, nodes, ne => by
      simp [simplifySeparation.go]
  | fuel + 1, nodes, ne => by
      simp only [simplifySeparation.go]
      split
      · rfl
      · have cutNe := cutCycle_ne_nil nodes ne
        have cutLast := cutCycle_getLast nodes ne
        have ih :=
          simplifySeparation.go_getLast fuel (cutCycle nodes) cutNe
        exact ih.trans cutLast

theorem simplifySeparation_consecutive
    {relation : SeparationNode S → SeparationNode S → Prop}
    {nodes : List (SeparationNode S)}
    (hcons : PathSpecification.Consecutive relation nodes) :
    PathSpecification.Consecutive relation (simplifySeparation nodes) :=
  simplifySeparation.go_consecutive nodes.length nodes hcons

theorem simplifySeparation_nodup (nodes : List (SeparationNode S)) :
    (simplifySeparation nodes).Nodup :=
  simplifySeparation.go_nodup nodes.length nodes (Nat.le_refl _)

theorem simplifySeparation_head {nodes : List (SeparationNode S)}
    (ne : nodes ≠ []) :
    (simplifySeparation nodes).head? = nodes.head? :=
  simplifySeparation.go_head nodes.length nodes ne

theorem simplifySeparation_getLast {nodes : List (SeparationNode S)}
    (ne : nodes ≠ []) :
    (simplifySeparation nodes).getLast? = nodes.getLast? :=
  simplifySeparation.go_getLast nodes.length nodes ne

theorem simplifySeparation.go_tripleOpenOrCollider
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (conditioned : NodeSet S) :
    forall (fuel : Nat) (nodes : List (SeparationNode S)),
      PathSpecification.Consecutive
          (PathSpecification.Adjacent G mutilation) nodes ->
        PathSpecification.TripleOpenOrCollider G mutilation conditioned
            nodes ->
          PathSpecification.TripleOpenOrCollider G mutilation conditioned
            (simplifySeparation.go fuel nodes)
  | 0, nodes, _hcons, hopen => by
      simpa [simplifySeparation.go] using hopen
  | fuel + 1, nodes, hcons, hopen => by
      simp only [simplifySeparation.go]
      split
      · exact hopen
      · exact simplifySeparation.go_tripleOpenOrCollider G mutilation
          conditioned fuel (cutCycle nodes)
          (consecutive_cutCycle nodes hcons)
          (cutCycle_tripleOpenOrCollider G mutilation conditioned nodes
            hcons hopen)

theorem simplifySeparation_tripleOpenOrCollider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {nodes : List (SeparationNode S)}
    (hcons : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation) nodes)
    (hopen : PathSpecification.TripleOpenOrCollider G mutilation
      conditioned nodes) :
    PathSpecification.TripleOpenOrCollider G mutilation conditioned
      (simplifySeparation nodes) :=
  simplifySeparation.go_tripleOpenOrCollider G mutilation conditioned
    nodes.length nodes hcons hopen

theorem mem_simplifySeparation.go {node : SeparationNode S} :
    forall (fuel : Nat) (nodes : List (SeparationNode S)),
      node ∈ simplifySeparation.go fuel nodes -> node ∈ nodes
  | 0, nodes, member => by
      simpa [simplifySeparation.go] using member
  | fuel + 1, nodes, member => by
      simp only [simplifySeparation.go] at member
      split at member
      · exact member
      · exact mem_cutCycle nodes
          (mem_simplifySeparation.go fuel (cutCycle nodes) member)

theorem mem_simplifySeparation {node : SeparationNode S}
    {nodes : List (SeparationNode S)}
    (member : node ∈ simplifySeparation nodes) :
    node ∈ nodes :=
  mem_simplifySeparation.go nodes.length nodes member

/-- An internally active, simple DAG-adjacency walk is an active path. -/
def activePath_of_adjacent_nodes (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {source target : SeparationNode S}
    (nodes : List (SeparationNode S))
    (starts : nodes.head? = some source)
    (finishes : nodes.getLast? = some target)
    (simple : nodes.Nodup)
    (adjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation) nodes)
    (inactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned nodes = 0)
    (sourceOpen : blockedBy conditioned source = false)
    (targetOpen : blockedBy conditioned target = false) :
    PathSpecification.ActivePath G mutilation conditioned source target where
  nodes := nodes
  starts := starts
  finishes := finishes
  simple := simple
  adjacent := adjacent
  source_open := sourceOpen
  target_open := targetOpen
  internal_active :=
    PathSpecification.InternalTriplesActive.of_inactiveColliderCount_zero
      nodes inactive

theorem ancestorOf_of_left_selected (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx : Fin S.count} (selected : left sourceIdx = true) :
    G.ancestorOf mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      (.observed sourceIdx) = true :=
  G.ancestorOf_target mutilation
    (NodeSet.union left (NodeSet.union right conditioned))
    ((NodeSet.union_eq_true left (NodeSet.union right conditioned)
      sourceIdx).mpr (Or.inl selected))

theorem ancestorOf_of_right_selected (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {targetIdx : Fin S.count} (selected : right targetIdx = true) :
    G.ancestorOf mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      (.observed targetIdx) = true :=
  G.ancestorOf_target mutilation
    (NodeSet.union left (NodeSet.union right conditioned))
    ((NodeSet.union_eq_true left (NodeSet.union right conditioned)
      targetIdx).mpr (Or.inr ((NodeSet.union_eq_true right conditioned
        targetIdx).mpr (Or.inl selected))))

/-- Expansion of a simple moral walk is a DAG-adjacency walk.  When that walk
is already simple and internally active, it is an active path on the original
observed endpoints. -/
theorem exists_activePath_of_expanded_zero (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (simple : (G.expandMoralNodes mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned walk.walk).Nodup)
    (inactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned
      (G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk) = 0) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        (.observed sourceIdx) (.observed targetIdx)) :=
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let expanded := G.expandMoralNodes mutilation targets conditioned walk.walk
  ⟨G.activePath_of_adjacent_nodes mutilation conditioned expanded
    (G.expandMoralNodes_head mutilation targets conditioned walk.walk)
    (G.expandMoralNodes_getLast mutilation targets conditioned walk.walk)
    simple
    (G.expandMoralNodes_consecutive_adjacent mutilation targets
      conditioned walk.walk)
    inactive sourceOpen targetOpen⟩

/-- A simple directed expanded-DAG walk whose vertices avoid `conditioned`
is an active path: every internal vertex is a non-collider and is open. -/
def activePath_of_directed_simple (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {source target : SeparationNode S}
    (walk : FiniteReachability.SimpleWalk
      (G.expandedMutilatedEdge mutilation) source target)
    (openNodes : forall vertex, vertex ∈ walk.walk.nodes ->
      blockedBy conditioned vertex = false) :
    PathSpecification.ActivePath G mutilation conditioned source target :=
  G.activePath_of_adjacent_nodes mutilation conditioned walk.walk.nodes
    walk.walk.nodes_head walk.walk.nodes_getLast walk.simple
    (G.consecutive_adjacent_of_directedWalk mutilation walk.walk)
    (PathSpecification.inactiveColliderCount_eq_zero_of_internal_active
      walk.walk.nodes
      (G.internal_active_of_directed_open mutilation conditioned
        walk.walk openNodes))
    (openNodes source (by
      rcases List.head?_eq_some_iff.mp walk.walk.nodes_head with ⟨_, split⟩
      simp [split]))
    (openNodes target (by
      rcases List.getLast?_eq_some_iff.mp walk.walk.nodes_getLast with
        ⟨_, split⟩
      simp [split]))

/-- Reverse a simple directed expanded-DAG walk: adjacency is symmetric,
internal activity is orientation-independent, and every vertex remains
open.  Oxford's left-endpoint glue uses this when the continuation from
the collider is already an active path rather than the original suffix. -/
def activePath_of_reverse_directed (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {source target : SeparationNode S}
    (walk : FiniteReachability.SimpleWalk
      (G.expandedMutilatedEdge mutilation) source target)
    (openNodes : forall vertex, vertex ∈ walk.walk.nodes ->
      blockedBy conditioned vertex = false) :
    PathSpecification.ActivePath G mutilation conditioned target source :=
  G.activePath_of_adjacent_nodes mutilation conditioned
    walk.walk.nodes.reverse
    (by
      rw [head?_reverse_eq_getLast?]
      exact walk.walk.nodes_getLast)
    (by
      simpa [List.getLast?_reverse] using walk.walk.nodes_head)
    (nodup_reverse_of walk.simple)
    (PathSpecification.Consecutive.reverse
      (fun _left _right adj => PathSpecification.Adjacent.symm adj)
      walk.walk.nodes
      (G.consecutive_adjacent_of_directedWalk mutilation walk.walk))
    (PathSpecification.inactiveColliderCount_eq_zero_of_internal_active
      walk.walk.nodes.reverse
      (PathSpecification.InternalTriplesActive.reverse
        walk.walk.nodes
        (G.internal_active_of_directed_open mutilation conditioned
          walk.walk openNodes)))
    (openNodes target (by
      rcases List.getLast?_eq_some_iff.mp walk.walk.nodes_getLast with
        ⟨_, split⟩
      simp [split]))
    (openNodes source (by
      rcases List.head?_eq_some_iff.mp walk.walk.nodes_head with ⟨_, split⟩
      simp [split]))

theorem blockedBy_false_of_unactivated (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {node : SeparationNode S}
    (unactivated : G.ancestorOf mutilation conditioned node = false) :
    blockedBy conditioned node = false := by
  cases node with
  | latentPair _ _ =>
      simp [blockedBy]
  | observed index =>
      cases selected : conditioned index with
      | false => simp [blockedBy, selected]
      | true =>
          have activated : G.ancestorOf mutilation conditioned
              (.observed index) = true :=
            G.ancestorOf_target mutilation conditioned selected
          rw [activated] at unactivated
          contradiction

theorem unactivated_of_inactive_collider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {previous middle next : SeparationNode S}
    (collider : PathSpecification.isColliderBool G mutilation
      previous middle next = true)
    (inactive : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false) :
    G.ancestorOf mutilation conditioned middle = false := by
  simp [PathSpecification.tripleActiveBool, collider] at inactive
  exact inactive

/-- An inactive non-collider is a blocked vertex: `tripleActiveBool` on a
non-collider is exactly the negation of `blockedBy`. -/
theorem blockedBy_of_inactive_noncollider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {previous middle next : SeparationNode S}
    (notCollider : PathSpecification.isColliderBool G mutilation
      previous middle next = false)
    (inactive : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false) :
    blockedBy conditioned middle = true := by
  simp [PathSpecification.tripleActiveBool, notCollider] at inactive
  cases blocked : blockedBy conditioned middle with
  | true => rfl
  | false => simp [blocked] at inactive

/-- An inactive window on a collider-or-open trail is necessarily a
collider: a non-collider would have an open middle, contradicting
inactivity. -/
theorem isColliderBool_of_inactive_openOrCollider (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {nodes : List (SeparationNode S)}
    {before : List (SeparationNode S)}
    {previous middle next : SeparationNode S}
    {after : List (SeparationNode S)}
    (hopen : PathSpecification.TripleOpenOrCollider G mutilation
      conditioned nodes)
    (split : nodes = before ++ previous :: middle :: next :: after)
    (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false) :
    PathSpecification.isColliderBool G mutilation previous middle next =
      true := by
  have openOr :=
    PathSpecification.TripleOpenOrCollider.of_append before previous
      middle next after (by simpa [split] using hopen)
  cases colliderValue :
      PathSpecification.isColliderBool G mutilation previous middle next with
  | true => rfl
  | false =>
      have blocked :=
        G.blockedBy_of_inactive_noncollider mutilation conditioned
          colliderValue inactiveTriple
      rcases openOr with collider | openMiddle
      · rw [colliderValue] at collider
        cases collider
      · rw [blocked] at openMiddle
        cases openMiddle

/--
The first inactive window of an expansion is a collider.  Original moral
vertices are open, and an inserted common child is introduced exactly as
the middle of a collider triple.
-/
theorem isColliderBool_of_expanded_inactive (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {length : Nat} {walkSource walkTarget : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.MoralOpenEdge mutilation targets conditioned) length walkSource
        walkTarget)
    (before : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (expandEq : G.expandMoralNodes mutilation targets conditioned walk =
      before ++ previous :: middle :: next :: after)
    (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false) :
    PathSpecification.isColliderBool G mutilation previous middle next =
      true := by
  have openOr :=
    G.expandMoralNodes_middle_open_or_collider mutilation targets
      conditioned walk before previous middle next after expandEq
  cases colliderValue :
      PathSpecification.isColliderBool G mutilation previous middle next with
  | true => rfl
  | false =>
      have blocked :=
        G.blockedBy_of_inactive_noncollider mutilation conditioned
          colliderValue inactiveTriple
      rcases openOr with collider | openMiddle
      · rw [colliderValue] at collider
        cases collider
      · rw [blocked] at openMiddle
        cases openMiddle

/-- An outgoing directed edge from `middle` forbids a collider at that
vertex: the DAG ranking cannot decrease along the reverse of the same
edge.  Oxford join triples are of this shape. -/
theorem not_collider_of_outgoing (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {previous middle next : SeparationNode S}
    (out : G.expandedMutilatedEdge mutilation middle next = true) :
    Not (PathSpecification.IsCollider G mutilation previous middle next) := by
  intro collider
  have rankOut := G.expandedMutilatedEdge_rank_lt mutilation out
  have rankIn := G.expandedMutilatedEdge_rank_lt mutilation collider.2
  omega

/-- An outgoing edge `middle → previous` equally forbids a collider whose
first parent is `previous`: the two directed ranks cannot both hold. -/
theorem not_collider_of_outgoing_previous (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {previous middle next : SeparationNode S}
    (out : G.expandedMutilatedEdge mutilation middle previous = true) :
    Not (PathSpecification.IsCollider G mutilation previous middle next) := by
  intro collider
  have rankOut := G.expandedMutilatedEdge_rank_lt mutilation out
  have rankIn := G.expandedMutilatedEdge_rank_lt mutilation collider.1
  omega

/-- Every vertex of a directed walk from an unactivated source is open:
a conditioned observed vertex on the walk would activate the source by
ancestry. -/
theorem blockedBy_false_of_directed_from_unactivated (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {length : Nat} {source target vertex : SeparationNode S}
    (walk : FiniteReachability.ExactWalk
      (G.expandedMutilatedEdge mutilation) length source target)
    (unactivated : G.ancestorOf mutilation conditioned source = false)
    (member : vertex ∈ walk.nodes) :
    blockedBy conditioned vertex = false := by
  rcases FiniteReachability.ExactWalk.prefix_of_mem walk member with
    ⟨_prefixLength, _bound, prefixWalk⟩
  rcases prefixWalk with ⟨prefixWalk⟩
  exact G.blockedBy_false_of_not_conditioned_ancestor mutilation
    conditioned prefixWalk unactivated

theorem getLast?_suffix_append {α} {before : List α} {node target : α}
    {after : List α}
    (h : (before ++ node :: after).getLast? = some target) :
    (node :: after).getLast? = some target := by
  induction before with
  | nil => simpa using h
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases after with
          | nil => simpa using h
          | cons _ _ => simpa [List.getLast?_cons] using h
      | cons _ _ =>
          simpa [List.getLast?_cons] using ih (by
            simpa [List.cons_append, List.getLast?_cons] using h)

/--
Oxford's right-endpoint reroute: the inactive-zero prefix ending at an
unactivated collider, concatenated with a directed descendant walk to a
vertex of `right`, is an active path (after cutting at the first shared
vertex if the two trails overlap).  The join at the collider is a
non-collider because the continuation is outgoing.
-/
theorem exists_activePath_oxford_right (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (before : List (SeparationNode S))
    (previous middle : SeparationNode S)
    {source target : SeparationNode S}
    (starts : (before ++ previous :: [middle]).head? = some source)
    (simple : (before ++ previous :: [middle]).Nodup)
    (adjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (before ++ previous :: [middle]))
    (inactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned (before ++ previous :: [middle]) = 0)
    (sourceOpen : blockedBy conditioned source = false)
    (intoMiddle : G.expandedMutilatedEdge mutilation previous middle = true)
    (unactivated : G.ancestorOf mutilation conditioned middle = false)
    (directed : FiniteReachability.SimpleWalk
      (G.expandedMutilatedEdge mutilation) middle target) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        source target) := by
  let dest := target
  let front := before ++ previous :: [middle]
  have middleOpen : blockedBy conditioned middle = false :=
    G.blockedBy_false_of_unactivated mutilation conditioned unactivated
  have directedOpen : forall vertex, vertex ∈ directed.walk.nodes ->
      blockedBy conditioned vertex = false :=
    fun vertex member =>
      G.blockedBy_false_of_directed_from_unactivated mutilation conditioned
        directed.walk unactivated member
  have targetOpen : blockedBy conditioned dest = false := by
    change blockedBy conditioned target = false
    rcases List.getLast?_eq_some_iff.mp directed.walk.nodes_getLast with
      ⟨_, split⟩
    exact directedOpen target (by simp [split])
  have frontActive :
      PathSpecification.InternalTriplesActive G mutilation conditioned front :=
    PathSpecification.InternalTriplesActive.of_inactiveColliderCount_zero
      front inactive
  rcases directed with ⟨_length, walk, walkSimple⟩
  cases walk with
  | refl _node =>
      have lastFront : front.getLast? = some dest := by
        simp [front, dest]
      exact ⟨G.activePath_of_adjacent_nodes mutilation conditioned front
        starts lastFront simple adjacent inactive sourceOpen targetOpen⟩
  | @step restLength src child tgt firstEdge restWalk =>
      let back := restWalk.nodes
      have backSimple : back.Nodup := (List.nodup_cons.mp (by
        simpa [FiniteReachability.ExactWalk.nodes] using walkSimple)).2
      have backCons : PathSpecification.Consecutive
          (PathSpecification.Adjacent G mutilation) back :=
        G.consecutive_adjacent_of_directedWalk mutilation restWalk
      have directedActive :
          PathSpecification.InternalTriplesActive G mutilation conditioned
            (middle :: back) := by
        simpa [FiniteReachability.ExactWalk.nodes] using
          G.internal_active_of_directed_open mutilation conditioned
            (.step firstEdge restWalk) directedOpen
      have backActive :
          PathSpecification.InternalTriplesActive G mutilation conditioned
            back := by
        simpa using directedActive.tail
      have lastBack : back.getLast? = some dest :=
        restWalk.nodes_getLast
      have headBack : back.head? = some child := restWalk.nodes_head
      have joinEdge :
          PathSpecification.Adjacent G mutilation middle child :=
        Or.inl firstEdge
      cases hshare : firstSharedSeparation? front back with
      | none =>
          have disjoint : forall v, v ∈ front -> v ∈ back -> False :=
            firstSharedSeparation?_eq_none_disjoint hshare
          have gluedSimple : (front ++ back).Nodup :=
            nodup_append_of_disjoint simple backSimple disjoint
          have gluedCons : PathSpecification.Consecutive
              (PathSpecification.Adjacent G mutilation) (front ++ back) :=
            PathSpecification.Consecutive.append front back adjacent backCons
              (fun prev next prevLast nextHead => by
                have lastFront :
                    front.getLast? = some middle := by
                  simp [front]
                rw [lastFront] at prevLast
                cases prevLast
                rw [headBack] at nextHead
                cases nextHead
                exact joinEdge)
          have childSuffix : Exists fun suffix => back = child :: suffix := by
            cases hback : back with
            | nil =>
                exact (restWalk.nodes_ne_nil hback).elim
            | cons head suffix =>
                have headEq : head = child := by
                  simp [hback] at headBack
                  exact headBack
                subst head
                exact ⟨suffix, rfl⟩
          rcases childSuffix with ⟨suffix, backEq⟩
          have gluedActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (front ++ back) := by
            have joinTriple :
                PathSpecification.TripleActive G mutilation conditioned
                  previous middle child :=
              Or.inr ⟨G.not_collider_of_forward_edges mutilation
                intoMiddle firstEdge, middleOpen⟩
            have fullEq :
                front ++ back =
                  before ++ previous :: middle :: child :: suffix := by
              simp [front, backEq]
            rw [fullEq]
            exact PathSpecification.InternalTriplesActive.append_triple
              before previous middle child suffix
              (by simpa [front] using frontActive) joinTriple
              (by simpa [backEq] using directedActive)
          have gluedStarts : (front ++ back).head? = some source := by
            rcases List.head?_eq_some_iff.mp starts with ⟨tail, split⟩
            simp [front, split]
          have gluedFinishes : (front ++ back).getLast? = some dest := by
            rcases List.getLast?_eq_some_iff.mp lastBack with ⟨pre, split⟩
            simp [split]
          exact ⟨G.activePath_of_adjacent_nodes mutilation conditioned
            (front ++ back) gluedStarts gluedFinishes gluedSimple gluedCons
            (PathSpecification.inactiveColliderCount_eq_zero_of_internal_active
              _ gluedActive)
            sourceOpen targetOpen⟩
      | some v =>
          rcases firstSharedSeparation?_eq_some_split hshare with
            ⟨frontBefore, frontAfter, frontSplit, beforeDisjoint, vBack⟩
          let splitBack := splitMemSeparation v back vBack
          let backBefore := splitBack.val.1
          let backAfter := splitBack.val.2
          have backSplit : back = backBefore ++ v :: backAfter :=
            splitBack.property
          have gluedSimple : (frontBefore ++ v :: backAfter).Nodup :=
            nodup_overlap_glue simple backSimple frontSplit backSplit
              beforeDisjoint
          have gluedCons : PathSpecification.Consecutive
              (PathSpecification.Adjacent G mutilation)
              (frontBefore ++ v :: backAfter) :=
            PathSpecification.Consecutive.overlap_glue adjacent backCons
              frontSplit backSplit
          have leftActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (frontBefore ++ [v]) := by
            have takeEq := take_prefix_append frontBefore v frontAfter
            have taken := PathSpecification.InternalTriplesActive.take
              (by simpa [frontSplit] using frontActive)
              (frontBefore.length + 1)
            simpa [takeEq] using taken
          have rightActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (v :: backAfter) :=
            PathSpecification.InternalTriplesActive.suffix_append
              backBefore v backAfter (by simpa [backSplit] using backActive)
          have vOpen : blockedBy conditioned v = false :=
            directedOpen v (List.mem_cons.mpr (Or.inr vBack))
          have gluedActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (frontBefore ++ v :: backAfter) :=
            PathSpecification.InternalTriplesActive.glue_at
              frontBefore v backAfter leftActive rightActive
              (fun pred succ predLast succHead => by
                have out : G.expandedMutilatedEdge mutilation v succ =
                    true := by
                  have directedBack :
                      PathSpecification.Consecutive
                        (fun left right =>
                          G.expandedMutilatedEdge mutilation left right =
                            true)
                        back :=
                    restWalk.nodes_consecutive
                  rcases List.head?_eq_some_iff.mp succHead with
                    ⟨more, succEq⟩
                  have fullEq :
                      back = backBefore ++ v :: succ :: more := by
                    rw [backSplit, succEq]
                  rw [fullEq] at directedBack
                  exact PathSpecification.Consecutive.pair_of_append
                    backBefore more v succ directedBack
                exact Or.inr ⟨G.not_collider_of_outgoing mutilation out,
                  vOpen⟩)
          have gluedStarts : (frontBefore ++ v :: backAfter).head? =
              some source := by
            have headFront : front.head? = some source :=
              starts
            rw [frontSplit] at headFront
            cases hbefore : frontBefore with
            | nil =>
                rw [hbefore] at headFront
                simp only [List.nil_append, List.head?_cons,
                  Option.some.injEq] at headFront
                subst v
                simp
            | cons head tail =>
                rw [hbefore] at headFront
                simpa [hbefore, List.cons_append] using headFront
          have gluedFinishes : (frontBefore ++ v :: backAfter).getLast? =
              some dest := by
            have lastEq :
                (backBefore ++ v :: backAfter).getLast? = some dest := by
              rw [← backSplit]
              exact lastBack
            have suffixLast : (v :: backAfter).getLast? = some dest :=
              getLast?_suffix_append lastEq
            rcases List.getLast?_eq_some_iff.mp suffixLast with ⟨pre, split⟩
            simp [split]
          exact ⟨G.activePath_of_adjacent_nodes mutilation conditioned
            (frontBefore ++ v :: backAfter) gluedStarts gluedFinishes
            gluedSimple gluedCons
            (PathSpecification.inactiveColliderCount_eq_zero_of_internal_active
              _ gluedActive)
            sourceOpen targetOpen⟩

/--
Oxford's left-endpoint reroute: reverse a directed descendant walk from an
unactivated collider to a vertex of `left`, then continue along the original
suffix to the right endpoint.  The suffix is required to be internally
active; later inactive windows are a shorter trail and are handled by
induction on the expanded walk.
-/
theorem exists_activePath_oxford_left (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    (next : SeparationNode S)
    (after : List (SeparationNode S))
    (middle : SeparationNode S)
    {u targetIdx : Fin S.count}
    (suffixFinishes : (middle :: next :: after).getLast? =
      some (.observed targetIdx))
    (suffixSimple : (middle :: next :: after).Nodup)
    (suffixAdjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (middle :: next :: after))
    (suffixInactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned (middle :: next :: after) = 0)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (unactivated : G.ancestorOf mutilation conditioned middle = false)
    (directed : FiniteReachability.SimpleWalk
      (G.expandedMutilatedEdge mutilation) middle (.observed u)) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        (.observed u) (.observed targetIdx)) := by
  have middleOpen : blockedBy conditioned middle = false :=
    G.blockedBy_false_of_unactivated mutilation conditioned unactivated
  have directedOpen : forall vertex, vertex ∈ directed.walk.nodes ->
      blockedBy conditioned vertex = false :=
    fun vertex member =>
      G.blockedBy_false_of_directed_from_unactivated mutilation conditioned
        directed.walk unactivated member
  have uOpen : blockedBy conditioned (.observed u) = false := by
    rcases List.getLast?_eq_some_iff.mp directed.walk.nodes_getLast with
      ⟨_, split⟩
    exact directedOpen _ (by simp [split])
  have suffixActive :
      PathSpecification.InternalTriplesActive G mutilation conditioned
        (middle :: next :: after) :=
    PathSpecification.InternalTriplesActive.of_inactiveColliderCount_zero
      _ suffixInactive
  have joinEdge : PathSpecification.Adjacent G mutilation middle next :=
    suffixAdjacent.1
  rcases directed with ⟨_length, walk, walkSimple⟩
  cases walk with
  | refl _node =>
      exact ⟨G.activePath_of_adjacent_nodes mutilation conditioned
        (.observed u :: next :: after) (by simp) suffixFinishes suffixSimple
        suffixAdjacent suffixInactive uOpen targetOpen⟩
  | @step restLength src child tgt firstEdge restWalk =>
      let front := (middle :: restWalk.nodes).reverse
      let back := next :: after
      have frontSimple : front.Nodup :=
        nodup_reverse_of (by
          simpa [FiniteReachability.ExactWalk.nodes] using walkSimple)
      have frontCons : PathSpecification.Consecutive
          (PathSpecification.Adjacent G mutilation) front :=
        PathSpecification.Consecutive.reverse
          (fun _ _ adj => PathSpecification.Adjacent.symm adj)
          (middle :: restWalk.nodes)
          (G.consecutive_adjacent_of_directedWalk mutilation
            (.step firstEdge restWalk))
      have directedActive :
          PathSpecification.InternalTriplesActive G mutilation conditioned
            (middle :: restWalk.nodes) := by
        simpa [FiniteReachability.ExactWalk.nodes] using
          G.internal_active_of_directed_open mutilation conditioned
            (.step firstEdge restWalk) directedOpen
      have frontActive :
          PathSpecification.InternalTriplesActive G mutilation conditioned
            front := by
        simpa [front] using
          PathSpecification.InternalTriplesActive.reverse
            (middle :: restWalk.nodes) directedActive
      have lastFront : front.getLast? = some middle := by
        simp [front, List.getLast?_reverse,
          FiniteReachability.ExactWalk.nodes_head]
      have startsFront : front.head? = some (.observed u) := by
        have lastDirected : (middle :: restWalk.nodes).getLast? =
            some (.observed u) :=
          FiniteReachability.ExactWalk.nodes_getLast
            (.step firstEdge restWalk)
        rw [head?_reverse_eq_getLast?]
        exact lastDirected
      have backSimple : back.Nodup :=
        (List.nodup_cons.mp suffixSimple).2
      have backCons : PathSpecification.Consecutive
          (PathSpecification.Adjacent G mutilation) back :=
        suffixAdjacent.2
      have backActive :
          PathSpecification.InternalTriplesActive G mutilation conditioned
            back := by
        simpa using suffixActive.tail
      have lastBack : back.getLast? = some (.observed targetIdx) :=
        getLast?_suffix_append (before := [middle]) (node := next)
          (after := after) (by
            simpa [List.cons_append] using suffixFinishes)
      cases hshare : firstSharedSeparation? front back with
      | none =>
          have disjoint : forall v, v ∈ front -> v ∈ back -> False :=
            firstSharedSeparation?_eq_none_disjoint hshare
          have gluedSimple : (front ++ back).Nodup :=
            nodup_append_of_disjoint frontSimple backSimple disjoint
          have gluedCons : PathSpecification.Consecutive
              (PathSpecification.Adjacent G mutilation) (front ++ back) :=
            PathSpecification.Consecutive.append front back frontCons backCons
              (fun prev nxt prevLast nextHead => by
                rw [lastFront] at prevLast
                cases prevLast
                simp [back] at nextHead
                cases nextHead
                exact joinEdge)
          rcases List.getLast?_eq_some_iff.mp lastFront with
            ⟨frontInit, frontEq⟩
          have gluedActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (front ++ back) := by
            have leftActive :
                PathSpecification.InternalTriplesActive G mutilation
                  conditioned (frontInit ++ [middle]) := by
              simpa [frontEq] using frontActive
            have fullEq : front ++ back =
                frontInit ++ middle :: next :: after := by
              simp [frontEq, back]
            rw [fullEq]
            exact PathSpecification.InternalTriplesActive.glue_at
              frontInit middle (next :: after) leftActive suffixActive
              (fun pred succ predLast succHead => by
                have succEq : succ = next := by
                  simp only [List.head?_cons, Option.some.injEq] at succHead
                  exact succHead.symm
                subst succ
                have predEq : pred = child := by
                  have revEq :
                      front = restWalk.nodes.reverse ++ [middle] := by
                    simp [front, List.reverse_cons]
                  have concatEq :
                      restWalk.nodes.reverse ++ [middle] =
                        frontInit ++ [middle] := by
                    rw [← revEq, frontEq]
                  have initEq : restWalk.nodes.reverse = frontInit := by
                    have lenEq : restWalk.nodes.reverse.length =
                        frontInit.length := by
                      have cong := congrArg List.length concatEq
                      simpa using cong
                    exact (List.append_inj concatEq lenEq).1
                  have lastChild : restWalk.nodes.reverse.getLast? =
                      some child := by
                    simpa [List.getLast?_reverse] using restWalk.nodes_head
                  rw [← initEq, lastChild] at predLast
                  cases predLast
                  rfl
                subst pred
                exact Or.inr
                  ⟨G.not_collider_of_outgoing_previous mutilation firstEdge,
                    middleOpen⟩)
          have gluedStarts : (front ++ back).head? = some (.observed u) := by
            rcases List.head?_eq_some_iff.mp startsFront with ⟨tail, split⟩
            simp [split]
          have gluedFinishes : (front ++ back).getLast? =
              some (.observed targetIdx) := by
            rcases List.getLast?_eq_some_iff.mp lastBack with ⟨pre, split⟩
            simp [split]
          exact ⟨G.activePath_of_adjacent_nodes mutilation conditioned
            (front ++ back) gluedStarts gluedFinishes gluedSimple gluedCons
            (PathSpecification.inactiveColliderCount_eq_zero_of_internal_active
              _ gluedActive)
            uOpen targetOpen⟩
      | some v =>
          rcases firstSharedSeparation?_eq_some_split hshare with
            ⟨frontBefore, frontAfter, frontSplit, beforeDisjoint, vBack⟩
          let splitBack := splitMemSeparation v back vBack
          let backBefore := splitBack.val.1
          let backAfter := splitBack.val.2
          have backSplit : back = backBefore ++ v :: backAfter :=
            splitBack.property
          have gluedSimple : (frontBefore ++ v :: backAfter).Nodup :=
            nodup_overlap_glue frontSimple backSimple frontSplit backSplit
              beforeDisjoint
          have gluedCons : PathSpecification.Consecutive
              (PathSpecification.Adjacent G mutilation)
              (frontBefore ++ v :: backAfter) :=
            PathSpecification.Consecutive.overlap_glue frontCons backCons
              frontSplit backSplit
          have leftActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (frontBefore ++ [v]) := by
            have takeEq := take_prefix_append frontBefore v frontAfter
            have taken := PathSpecification.InternalTriplesActive.take
              (by simpa [frontSplit] using frontActive)
              (frontBefore.length + 1)
            simpa [takeEq] using taken
          have rightActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (v :: backAfter) :=
            PathSpecification.InternalTriplesActive.suffix_append
              backBefore v backAfter (by simpa [backSplit] using backActive)
          have vOpen : blockedBy conditioned v = false :=
            directedOpen v (by
              have vFront : v ∈ front := by
                rw [frontSplit]
                exact List.mem_append.mpr
                  (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
              have vDirected : v ∈ (middle :: restWalk.nodes) := by
                rw [List.mem_reverse] at vFront
                simpa [front] using vFront
              exact vDirected)
          have gluedActive :
              PathSpecification.InternalTriplesActive G mutilation
                conditioned (frontBefore ++ v :: backAfter) :=
            PathSpecification.InternalTriplesActive.glue_at
              frontBefore v backAfter leftActive rightActive
              (fun pred succ predLast succHead => by
                have revCons :
                    PathSpecification.Consecutive
                      (fun left right =>
                        G.expandedMutilatedEdge mutilation right left = true)
                      front := by
                  simpa [front, FiniteReachability.ExactWalk.nodes] using
                    FiniteReachability.ExactWalk.consecutive_reverse
                      (.step firstEdge restWalk)
                rcases List.getLast?_eq_some_iff.mp predLast with
                  ⟨init, initEq⟩
                have listEq :
                    frontBefore ++ v :: frontAfter =
                      init ++ pred :: v :: frontAfter := by
                  rw [initEq]
                  simp [List.append_assoc]
                rw [frontSplit, listEq] at revCons
                have out :
                    G.expandedMutilatedEdge mutilation v pred = true :=
                  PathSpecification.Consecutive.pair_of_append
                    init frontAfter pred v revCons
                exact Or.inr
                  ⟨G.not_collider_of_outgoing_previous mutilation out,
                    vOpen⟩)
          have gluedStarts : (frontBefore ++ v :: backAfter).head? =
              some (.observed u) := by
            have headFront : front.head? = some (.observed u) :=
              startsFront
            rw [frontSplit] at headFront
            cases hbefore : frontBefore with
            | nil =>
                rw [hbefore] at headFront
                simp only [List.nil_append, List.head?_cons,
                  Option.some.injEq] at headFront
                subst v
                simp
            | cons head tail =>
                rw [hbefore] at headFront
                simpa [hbefore, List.cons_append] using headFront
          have gluedFinishes : (frontBefore ++ v :: backAfter).getLast? =
              some (.observed targetIdx) := by
            have lastEq :
                (backBefore ++ v :: backAfter).getLast? =
                  some (.observed targetIdx) := by
              rw [← backSplit]
              exact lastBack
            have suffixLast : (v :: backAfter).getLast? =
                some (.observed targetIdx) :=
              getLast?_suffix_append lastEq
            rcases List.getLast?_eq_some_iff.mp suffixLast with ⟨pre, split⟩
            simp [split]
          exact ⟨G.activePath_of_adjacent_nodes mutilation conditioned
            (frontBefore ++ v :: backAfter) gluedStarts gluedFinishes
            gluedSimple gluedCons
            (PathSpecification.inactiveColliderCount_eq_zero_of_internal_active
              _ gluedActive)
            uOpen targetOpen⟩

/-- The inactive-zero prefix of a first-inactive split is a simple
DAG-adjacency trail: it is the prefix of a simple consecutive trail. -/
theorem prefix_adjacent_of_inactive_split (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    {before : List (SeparationNode S)}
    {previous middle next : SeparationNode S}
    {after : List (SeparationNode S)}
    (simple : (before ++ previous :: middle :: next :: after).Nodup)
    (adjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (before ++ previous :: middle :: next :: after)) :
    (before ++ previous :: [middle]).Nodup /\
      PathSpecification.Consecutive
        (PathSpecification.Adjacent G mutilation)
        (before ++ previous :: [middle]) := by
  have listEq :
      before ++ previous :: middle :: next :: after =
        (before ++ [previous]) ++ middle :: next :: after :=
    (List.append_assoc before [previous] (middle :: next :: after)).symm
  have prefixEq :
      (before ++ [previous]) ++ [middle] = before ++ previous :: [middle] := by
    rw [List.append_assoc]
    rfl
  have prefixSimple : (before ++ previous :: [middle]).Nodup := by
    have taken := nodup_prefix_append (before := before ++ [previous])
      (node := middle) (after := next :: after)
      (by rw [← listEq]; exact simple)
    rw [← prefixEq]
    exact taken
  have prefixAdjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (before ++ previous :: [middle]) := by
    have taken := PathSpecification.Consecutive.prefix_append
      (before ++ [previous]) middle (next :: after)
      (by rw [← listEq]; exact adjacent)
    rw [← prefixEq]
    exact taken
  exact ⟨prefixSimple, prefixAdjacent⟩

/-- Head of the inactive-zero prefix is the head of the split trail. -/
theorem prefix_head_of_inactive_split {α}
    {before : List α} {previous middle next : α} {after : List α}
    {source : α}
    (starts : (before ++ previous :: middle :: next :: after).head? =
      some source) :
    (before ++ previous :: [middle]).head? = some source := by
  cases before with
  | nil =>
      simpa only [List.nil_append] using starts
  | cons head tail =>
      simpa only [List.cons_append, List.head?_cons] using starts

/-- The suffix from the collider of a first-inactive split remains
consecutive. -/
theorem suffix_adjacent_of_inactive_split {relation : α -> α -> Prop}
    {before : List α} {previous middle next : α} {after : List α}
    (adjacent : PathSpecification.Consecutive relation
      (before ++ previous :: middle :: next :: after)) :
    PathSpecification.Consecutive relation (middle :: next :: after) := by
  have dropped := PathSpecification.Consecutive.drop before.length
    (before ++ previous :: middle :: next :: after) adjacent
  have eq : (before ++ previous :: middle :: next :: after).drop
      before.length = previous :: middle :: next :: after :=
    drop_append_length before _
  have atPrevious : PathSpecification.Consecutive relation
      (previous :: middle :: next :: after) := by
    simpa [eq] using dropped
  exact PathSpecification.Consecutive.drop 1 _ atPrevious

/-- The suffix from the collider of a first-inactive split remains simple. -/
theorem suffix_nodup_of_inactive_split {α}
    {before : List α} {previous middle next : α} {after : List α}
    (simple : (before ++ previous :: middle :: next :: after).Nodup) :
    (middle :: next :: after).Nodup := by
  have listEq :
      before ++ previous :: middle :: next :: after =
        (before ++ [previous]) ++ middle :: next :: after :=
    (List.append_assoc before [previous] (middle :: next :: after)).symm
  have parts := nodup_of_split (before := before ++ [previous]) (node := middle)
      (after := next :: after)
      (by
        rw [show (before ++ [previous]) ++ middle :: next :: after =
              before ++ previous :: middle :: next :: after from listEq.symm]
        exact simple)
  exact List.nodup_cons.mpr ⟨parts.2.2.1, parts.2.2.2.1⟩

/-- Reassociating a suffix split through a displayed predecessor. -/
theorem cons_append_suffix_split {α}
    (front : List α) (previous middle next : α) (after : List α)
    (beforeS : List α) (prevS midS nextS : α) (afterS : List α)
    (suffixSplit : middle :: next :: after =
      beforeS ++ prevS :: midS :: nextS :: afterS) :
    front ++ previous :: middle :: next :: after =
      (front ++ previous :: beforeS) ++
        prevS :: midS :: nextS :: afterS := by
  have step :
      previous :: middle :: next :: after =
        (previous :: beforeS) ++ prevS :: midS :: nextS :: afterS := by
    simp [List.cons_append, suffixSplit]
  calc front ++ previous :: middle :: next :: after
      = front ++
          ((previous :: beforeS) ++ prevS :: midS :: nextS :: afterS) := by
        rw [step]
    _ = (front ++ previous :: beforeS) ++
          prevS :: midS :: nextS :: afterS := by
        simp [List.append_assoc, List.cons_append]

/-- Nested collider suffixes are strictly shorter than the trail they
split, so Oxford's left-endpoint recursion is well-founded on length. -/
theorem nested_suffix_length_lt {α}
    {nodes : List α} {before : List α}
    {previous middle next : α} {after : List α}
    (split : nodes = before ++ previous :: middle :: next :: after) :
    (middle :: next :: after).length < nodes.length := by
  rw [split]
  simp [List.length_append, List.length_cons]
  omega

/--
Oxford right-endpoint reroute on an expanded moral walk: the first inactive
window is an unactivated collider, and a directed descendant in `right`
yields an active path from the original left endpoint to that descendant.
-/
theorem exists_activePath_of_expanded_oxford_right (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (leftSelected : left sourceIdx = true)
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (simple : (G.expandMoralNodes mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned walk.walk).Nodup)
    (before : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (split : G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk =
      before ++ previous :: middle :: next :: after)
    (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false)
    (prefixZero : PathSpecification.inactiveColliderCount G mutilation
      conditioned (before ++ previous :: [middle]) = 0)
    (collider : PathSpecification.isColliderBool G mutilation
      previous middle next = true)
    {u : Fin S.count}
    (inRight : right u = true)
    (bounded : FiniteReachability.BoundedWalk
      (G.expandedMutilatedEdge mutilation)
      G.separationNodes.length middle (.observed u)) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        (.observed sourceIdx) (.observed u)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let _ := leftSelected
  let _ := inRight
  have adjFull : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (before ++ previous :: middle :: next :: after) := by
    have adjExpanded :=
      G.expandMoralNodes_consecutive_adjacent mutilation targets
        conditioned walk.walk
    rw [split] at adjExpanded
    exact adjExpanded
  have simpleFull : (before ++ previous :: middle :: next :: after).Nodup := by
    rw [← split]
    exact simple
  have prefixFacts := G.prefix_adjacent_of_inactive_split mutilation
    simpleFull adjFull
  have prefixStarts : (before ++ previous :: [middle]).head? =
      some (.observed sourceIdx) :=
    prefix_head_of_inactive_split (by
      have headExpanded :=
        G.expandMoralNodes_head mutilation targets conditioned walk.walk
      rw [split] at headExpanded
      exact headExpanded)
  have intoMiddle : G.expandedMutilatedEdge mutilation previous middle =
      true :=
    ((PathSpecification.IsCollider_iff_isColliderBool G mutilation
      previous middle next).mpr collider).1
  have unactivated : G.ancestorOf mutilation conditioned middle = false :=
    G.unactivated_of_inactive_collider mutilation conditioned collider
      inactiveTriple
  rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
      SeparationNode.beq G.separationNodes
      (G.expandedMutilatedEdge mutilation)
      SeparationNode.beq_eq_true_iff SeparationNode.mem_all bounded with
    ⟨directed⟩
  exact G.exists_activePath_oxford_right mutilation conditioned
    before previous middle prefixStarts prefixFacts.1 prefixFacts.2
    prefixZero sourceOpen intoMiddle unactivated directed

/--
From a simple expanded trail whose first inactive window is an unactivated
collider, a descendant in `left ∪ right` is constructed computationally.
The right-endpoint case is the Oxford reroute above.
-/
theorem exists_descendant_of_expanded_inactive_collider
    (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (leftSelected : left sourceIdx = true)
    (before : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (split : G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk =
      before ++ previous :: middle :: next :: after)
    (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false)
    (collider : PathSpecification.isColliderBool G mutilation
      previous middle next = true) :
    Exists fun u : Fin S.count =>
      (left u = true \/ right u = true) /\
        conditioned u = false /\
          FiniteReachability.BoundedWalk
            (G.expandedMutilatedEdge mutilation)
            G.separationNodes.length middle (.observed u) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  have sourceAncestor :
      G.ancestorOf mutilation targets (.observed sourceIdx) = true :=
    G.ancestorOf_of_left_selected mutilation left right conditioned
      leftSelected
  have middleMem : middle ∈ G.expandMoralNodes mutilation targets
      conditioned walk.walk := by
    rw [split]
    exact List.mem_append.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have inLarge : G.ancestorOf mutilation targets middle = true :=
    G.expandMoralNodes_mem_ancestor mutilation targets conditioned
      walk.walk sourceAncestor middleMem
  have unactivated : G.ancestorOf mutilation conditioned middle = false :=
    G.unactivated_of_inactive_collider mutilation conditioned collider
      inactiveTriple
  exact G.exists_descendant_in_left_or_right mutilation left right
    conditioned inLarge unactivated

/--
Oxford left-endpoint reroute on an expanded moral walk: reverse a directed
descendant in `left` and continue along an internally active suffix to the
original right endpoint.
-/
theorem exists_activePath_of_expanded_oxford_left (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (_leftSelected : left sourceIdx = true)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (simple : (G.expandMoralNodes mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned walk.walk).Nodup)
    (before : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (split : G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk =
      before ++ previous :: middle :: next :: after)
    (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false)
    (collider : PathSpecification.isColliderBool G mutilation
      previous middle next = true)
    (suffixInactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned (middle :: next :: after) = 0)
    {u : Fin S.count}
    (_uLeft : left u = true)
    (bounded : FiniteReachability.BoundedWalk
      (G.expandedMutilatedEdge mutilation)
      G.separationNodes.length middle (.observed u)) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        (.observed u) (.observed targetIdx)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  have adjFull : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (before ++ previous :: middle :: next :: after) := by
    have adjExpanded :=
      G.expandMoralNodes_consecutive_adjacent mutilation targets
        conditioned walk.walk
    rw [split] at adjExpanded
    exact adjExpanded
  have simpleFull : (before ++ previous :: middle :: next :: after).Nodup := by
    rw [← split]
    exact simple
  have suffixAdjacent := suffix_adjacent_of_inactive_split adjFull
  have suffixSimple := suffix_nodup_of_inactive_split simpleFull
  have suffixFinishes : (middle :: next :: after).getLast? =
      some (.observed targetIdx) := by
    have lastExpanded :=
      G.expandMoralNodes_getLast mutilation targets conditioned walk.walk
    rw [split] at lastExpanded
    exact getLast?_suffix_append (before := before ++ [previous])
      (node := middle) (after := next :: after) (by
        have listEq :
            before ++ previous :: middle :: next :: after =
              (before ++ [previous]) ++ middle :: next :: after :=
          (List.append_assoc before [previous] (middle :: next :: after)).symm
        rw [← listEq]
        exact lastExpanded)
  have unactivated : G.ancestorOf mutilation conditioned middle = false :=
    G.unactivated_of_inactive_collider mutilation conditioned collider
      inactiveTriple
  rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
      SeparationNode.beq G.separationNodes
      (G.expandedMutilatedEdge mutilation)
      SeparationNode.beq_eq_true_iff SeparationNode.mem_all bounded with
    ⟨directed⟩
  exact G.exists_activePath_oxford_left mutilation conditioned next after
    middle suffixFinishes suffixSimple suffixAdjacent suffixInactive
    targetOpen unactivated directed

/-- Glue a reverse directed walk from an unactivated collider onto an
already-constructed active continuation that starts at that collider. -/
theorem exists_activePath_oxford_left_of_activePath (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (conditioned : NodeSet S)
    {middle : SeparationNode S} {u targetIdx : Fin S.count}
    (path : PathSpecification.ActivePath G mutilation conditioned
      middle (.observed targetIdx))
    (unactivated : G.ancestorOf mutilation conditioned middle = false)
    (directed : FiniteReachability.SimpleWalk
      (G.expandedMutilatedEdge mutilation) middle (.observed u)) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        (.observed u) (.observed targetIdx)) := by
  have directedOpen : forall vertex, vertex ∈ directed.walk.nodes ->
      blockedBy conditioned vertex = false :=
    fun vertex member =>
      G.blockedBy_false_of_directed_from_unactivated mutilation conditioned
        directed.walk unactivated member
  rcases List.head?_eq_some_iff.mp path.starts with ⟨tail, nodesHead⟩
  cases tail with
  | nil =>
      have lastEq : path.nodes.getLast? = some (.observed targetIdx) :=
        path.finishes
      rw [nodesHead] at lastEq
      simp at lastEq
      have reversePath :=
        G.activePath_of_reverse_directed mutilation conditioned directed
          directedOpen
      cases lastEq
      exact ⟨reversePath⟩
  | cons next after =>
      have nodesEq : path.nodes = middle :: next :: after := nodesHead
      exact G.exists_activePath_oxford_left mutilation conditioned next after
        middle
        (by simpa [nodesEq] using path.finishes)
        (by simpa [nodesEq] using path.simple)
        (by simpa [nodesEq] using path.adjacent)
        (by
          simpa [nodesEq] using
            PathSpecification.inactiveColliderCount_eq_zero_of_internal_active
              path.nodes path.internal_active)
        path.target_open unactivated directed

/--
Oxford recursion on a collider suffix of a simple expansion.  The suffix
starts at an unactivated collider that has a directed descendant in
`left`.  If the suffix is internally active, left-endpoint glue reaches
the original right endpoint.  Otherwise the first inactive window of the
suffix is again a collider, a right descendant is preferred, and a
left-only nested collider is a strictly shorter suffix.
-/
theorem exists_activePath_of_collider_suffix (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (simple : (G.expandMoralNodes mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned walk.walk).Nodup)
    (leftSelected : left sourceIdx = true)
    (rightSelected : right targetIdx = true)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (front : List (SeparationNode S))
    (previous middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (expandEq : G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk =
      front ++ previous :: middle :: next :: after)
    (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
      conditioned previous middle next = false)
    (collider : PathSpecification.isColliderBool G mutilation
      previous middle next = true)
    {uLeft : Fin S.count}
    (inLeft : left uLeft = true)
    (boundedLeft : FiniteReachability.BoundedWalk
      (G.expandedMutilatedEdge mutilation)
      G.separationNodes.length middle (.observed uLeft)) :
    Exists fun s : Fin S.count =>
      Exists fun t : Fin S.count =>
        left s = true /\ right t = true /\
          Nonempty
            (PathSpecification.ActivePath G mutilation conditioned
              (.observed s) (.observed t)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let expanded :=
    G.expandMoralNodes mutilation targets conditioned walk.walk
  have unactivated : G.ancestorOf mutilation conditioned middle = false :=
    G.unactivated_of_inactive_collider mutilation conditioned collider
      inactiveTriple
  have adjFull : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (front ++ previous :: middle :: next :: after) := by
    have adjExpanded :=
      G.expandMoralNodes_consecutive_adjacent mutilation targets
        conditioned walk.walk
    rw [expandEq] at adjExpanded
    exact adjExpanded
  have simpleFull : (front ++ previous :: middle :: next :: after).Nodup := by
    rw [← expandEq]
    exact simple
  have suffixAdjacent := suffix_adjacent_of_inactive_split adjFull
  have suffixSimple := suffix_nodup_of_inactive_split simpleFull
  have suffixFinishes : (middle :: next :: after).getLast? =
      some (.observed targetIdx) := by
    have lastExpanded :=
      G.expandMoralNodes_getLast mutilation targets conditioned walk.walk
    rw [expandEq] at lastExpanded
    exact getLast?_suffix_append (before := front ++ [previous])
      (node := middle) (after := next :: after) (by
        have listEq :
            front ++ previous :: middle :: next :: after =
              (front ++ [previous]) ++ middle :: next :: after :=
          (List.append_assoc front [previous] (middle :: next :: after)).symm
        rw [← listEq]
        exact lastExpanded)
  rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
      SeparationNode.beq G.separationNodes
      (G.expandedMutilatedEdge mutilation)
      SeparationNode.beq_eq_true_iff SeparationNode.mem_all boundedLeft with
    ⟨directedLeft⟩
  cases hcount : PathSpecification.inactiveColliderCount G mutilation
      conditioned (middle :: next :: after) with
  | zero =>
      exact ⟨uLeft, targetIdx, inLeft, rightSelected,
        G.exists_activePath_oxford_left mutilation conditioned next after
          middle suffixFinishes suffixSimple suffixAdjacent hcount
          targetOpen unactivated directedLeft⟩
  | succ n =>
      have inactivePos :
          0 < PathSpecification.inactiveColliderCount G mutilation
            conditioned (middle :: next :: after) := by
        rw [hcount]
        exact Nat.succ_pos _
      rcases PathSpecification.exists_inactive_split
          (middle :: next :: after) inactivePos with
        ⟨beforeS, prevS, midS, nextS, afterS, splitS, inactiveS, prefixZeroS⟩
      have expandNested :
          G.expandMoralNodes mutilation targets conditioned walk.walk =
            (front ++ previous :: beforeS) ++
              prevS :: midS :: nextS :: afterS := by
        rw [expandEq]
        exact cons_append_suffix_split front previous middle next after
          beforeS prevS midS nextS afterS splitS
      have colliderS :
          PathSpecification.isColliderBool G mutilation prevS midS nextS =
            true :=
        G.isColliderBool_of_expanded_inactive mutilation targets
          conditioned walk.walk (front ++ previous :: beforeS) prevS midS
          nextS afterS expandNested inactiveS
      have unactivatedS :
          G.ancestorOf mutilation conditioned midS = false :=
        G.unactivated_of_inactive_collider mutilation conditioned colliderS
          inactiveS
      have sourceAncestor :
          G.ancestorOf mutilation targets (.observed sourceIdx) = true :=
        G.ancestorOf_of_left_selected mutilation left right conditioned
          leftSelected
      have midSMem : midS ∈ expanded := by
        change midS ∈
          G.expandMoralNodes mutilation targets conditioned walk.walk
        rw [expandNested]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr
            (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
      have inLargeS : G.ancestorOf mutilation targets midS = true :=
        G.expandMoralNodes_mem_ancestor mutilation targets conditioned
          walk.walk sourceAncestor midSMem
      have prefixFacts :=
        G.prefix_adjacent_of_inactive_split mutilation
          (by simpa [splitS] using suffixSimple)
          (by simpa [splitS] using suffixAdjacent)
      have prefixStarts : (beforeS ++ prevS :: [midS]).head? =
          some middle :=
        prefix_head_of_inactive_split (before := beforeS) (previous := prevS)
          (middle := midS) (next := nextS) (after := afterS) (source := middle)
          (by
            have h : (middle :: next :: after).head? = some middle := by
              simp
            simpa [splitS] using h)
      have middleOpen : blockedBy conditioned middle = false :=
        G.blockedBy_false_of_unactivated mutilation conditioned unactivated
      have intoMidS : G.expandedMutilatedEdge mutilation prevS midS = true :=
        ((PathSpecification.IsCollider_iff_isColliderBool G mutilation
          prevS midS nextS).mpr colliderS).1
      cases hrightS : G.ancestorOf mutilation right midS with
      | true =>
          rcases (G.ancestorOf_eq_true_iff mutilation right midS).mp
              hrightS with ⟨uRight, inRight, boundedRight⟩
          cases condVal : conditioned uRight with
          | true =>
              have activated :
                  G.ancestorOf mutilation conditioned midS = true :=
                (G.ancestorOf_eq_true_iff mutilation conditioned midS).mpr
                  ⟨uRight, condVal, boundedRight⟩
              rw [activated] at unactivatedS
              contradiction
          | false =>
              rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
                  SeparationNode.beq G.separationNodes
                  (G.expandedMutilatedEdge mutilation)
                  SeparationNode.beq_eq_true_iff SeparationNode.mem_all
                  boundedRight with ⟨directedRight⟩
              rcases G.exists_activePath_oxford_right mutilation
                  conditioned beforeS prevS midS prefixStarts prefixFacts.1
                  prefixFacts.2 prefixZeroS middleOpen intoMidS unactivatedS
                  directedRight with ⟨pathMid⟩
              exact ⟨uLeft, uRight, inLeft, inRight,
                G.exists_activePath_oxford_left_of_activePath mutilation
                  conditioned pathMid unactivated directedLeft⟩
      | false =>
          rcases G.exists_descendant_in_left_or_right mutilation left right
              conditioned inLargeS unactivatedS with
            ⟨uS, side, _uncond, boundedS⟩
          rcases side with inLeftS | inRightS
          · exact G.exists_activePath_of_collider_suffix mutilation left
              right conditioned walk simple leftSelected rightSelected
              targetOpen (front ++ previous :: beforeS) prevS midS nextS
              afterS expandNested inactiveS colliderS inLeftS boundedS
          · have ancestorRight :
                G.ancestorOf mutilation right midS = true :=
              (G.ancestorOf_eq_true_iff mutilation right midS).mpr
                ⟨uS, inRightS, boundedS⟩
            rw [hrightS] at ancestorRight
            contradiction
termination_by (middle :: next :: after).length
decreasing_by
  exact nested_suffix_length_lt splitS

/--
The three Oxford/zero cases in which a simple expansion of a moral walk
already yields an active path between some pair of `left` and `right`.
Remaining inactive suffixes and non-collider first windows are excluded
until those reroutes are inhabited.
-/
inductive ExpandedActiveCase (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx)) : Type
  | internallyActive
      (simple : (G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk).Nodup)
      (inactive : PathSpecification.inactiveColliderCount G mutilation
        conditioned
        (G.expandMoralNodes mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          conditioned walk.walk) = 0) :
      ExpandedActiveCase G mutilation left right conditioned walk
  | oxfordRight
      (simple : (G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk).Nodup)
      (before : List (SeparationNode S))
      (previous middle next : SeparationNode S)
      (after : List (SeparationNode S))
      (split : G.expandMoralNodes mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          conditioned walk.walk =
        before ++ previous :: middle :: next :: after)
      (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
        conditioned previous middle next = false)
      (prefixZero : PathSpecification.inactiveColliderCount G mutilation
        conditioned (before ++ previous :: [middle]) = 0)
      (collider : PathSpecification.isColliderBool G mutilation
        previous middle next = true)
      (u : Fin S.count)
      (inRight : right u = true)
      (bounded : FiniteReachability.BoundedWalk
        (G.expandedMutilatedEdge mutilation)
        G.separationNodes.length middle (.observed u)) :
      ExpandedActiveCase G mutilation left right conditioned walk
  | oxfordLeft
      (simple : (G.expandMoralNodes mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned walk.walk).Nodup)
      (before : List (SeparationNode S))
      (previous middle next : SeparationNode S)
      (after : List (SeparationNode S))
      (split : G.expandMoralNodes mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          conditioned walk.walk =
        before ++ previous :: middle :: next :: after)
      (inactiveTriple : PathSpecification.tripleActiveBool G mutilation
        conditioned previous middle next = false)
      (collider : PathSpecification.isColliderBool G mutilation
        previous middle next = true)
      (suffixInactive : PathSpecification.inactiveColliderCount G mutilation
        conditioned (middle :: next :: after) = 0)
      (u : Fin S.count)
      (inLeft : left u = true)
      (bounded : FiniteReachability.BoundedWalk
        (G.expandedMutilatedEdge mutilation)
        G.separationNodes.length middle (.observed u)) :
      ExpandedActiveCase G mutilation left right conditioned walk

/-- Extract an active-path witness in `left × right` from any of the three
inhabited Oxford/zero cases. -/
theorem exists_activePath_of_expanded_active_case (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (leftSelected : left sourceIdx = true)
    (rightSelected : right targetIdx = true)
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (c : ExpandedActiveCase G mutilation left right conditioned walk) :
    Exists fun s : Fin S.count =>
      Exists fun t : Fin S.count =>
        left s = true /\ right t = true /\
          Nonempty
            (PathSpecification.ActivePath G mutilation conditioned
              (.observed s) (.observed t)) := by
  cases c with
  | internallyActive simple inactive =>
      exact ⟨sourceIdx, targetIdx, leftSelected, rightSelected,
        G.exists_activePath_of_expanded_zero mutilation left right
          conditioned walk sourceOpen targetOpen simple inactive⟩
  | oxfordRight simple before previous middle next after split
      inactiveTriple prefixZero collider u inRight bounded =>
      exact ⟨sourceIdx, u, leftSelected, inRight,
        G.exists_activePath_of_expanded_oxford_right mutilation left right
          conditioned walk leftSelected sourceOpen simple before previous
          middle next after split inactiveTriple prefixZero collider
          inRight bounded⟩
  | oxfordLeft simple before previous middle next after split
      inactiveTriple collider suffixInactive u inLeft bounded =>
      exact ⟨u, targetIdx, inLeft, rightSelected,
        G.exists_activePath_of_expanded_oxford_left mutilation left right
          conditioned walk leftSelected targetOpen simple before previous
          middle next after split inactiveTriple collider suffixInactive
          inLeft bounded⟩

/-- From a simple expansion, the first inactive split (if any) is computed
without choice.  Combined with a collider descendant in `right`, or in
`left` with an active suffix, this inhabits `ExpandedActiveCase`. -/
theorem expandedActiveCase_of_simple_split (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (_simple : (G.expandMoralNodes mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned walk.walk).Nodup) :
    PathSpecification.inactiveColliderCount G mutilation conditioned
        (G.expandMoralNodes mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          conditioned walk.walk) = 0 ∨
      Exists fun before : List (SeparationNode S) =>
        Exists fun previous : SeparationNode S =>
          Exists fun middle : SeparationNode S =>
            Exists fun next : SeparationNode S =>
              Exists fun after : List (SeparationNode S) =>
                G.expandMoralNodes mutilation
                    (NodeSet.union left (NodeSet.union right conditioned))
                    conditioned walk.walk =
                  before ++ previous :: middle :: next :: after /\
                  PathSpecification.tripleActiveBool G mutilation
                    conditioned previous middle next = false /\
                    PathSpecification.inactiveColliderCount G mutilation
                      conditioned (before ++ previous :: [middle]) = 0 := by
  let expanded :=
    G.expandMoralNodes mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned walk.walk
  cases hcount : PathSpecification.inactiveColliderCount G mutilation
      conditioned expanded with
  | zero =>
      exact Or.inl (by simp)
  | succ n =>
      have inactivePos :
          0 < PathSpecification.inactiveColliderCount G mutilation
            conditioned expanded := by
        rw [hcount]
        exact Nat.succ_pos _
      rcases PathSpecification.exists_inactive_split expanded inactivePos with
        ⟨before, previous, middle, next, after, split, inactiveTriple,
          prefixZero⟩
      exact Or.inr ⟨before, previous, middle, next, after, split,
        inactiveTriple, prefixZero⟩

/--
A simple expansion yields an active-path witness in `left × right`.
Zero-inactive expansions and first-inactive colliders with a directed
descendant in `right` are handled directly.  A left-only first collider
is Oxford recursion on its suffix, well-founded on suffix length.
-/
theorem exists_activePath_of_simple_expanded (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (leftSelected : left sourceIdx = true)
    (rightSelected : right targetIdx = true)
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (simple : (G.expandMoralNodes mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned walk.walk).Nodup) :
    Exists fun s : Fin S.count =>
      Exists fun t : Fin S.count =>
        left s = true /\ right t = true /\
          Nonempty
            (PathSpecification.ActivePath G mutilation conditioned
              (.observed s) (.observed t)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let expanded :=
    G.expandMoralNodes mutilation targets conditioned walk.walk
  rcases G.expandedActiveCase_of_simple_split mutilation left right
      conditioned walk simple with inactive0 | splitExists
  · exact G.exists_activePath_of_expanded_active_case mutilation left
      right conditioned walk leftSelected rightSelected sourceOpen
      targetOpen (.internallyActive simple inactive0)
  · rcases splitExists with
      ⟨before, previous, middle, next, after, split, inactiveTriple,
        prefixZero⟩
    have collider :
        PathSpecification.isColliderBool G mutilation previous middle
          next = true :=
      G.isColliderBool_of_expanded_inactive mutilation targets
        conditioned walk.walk before previous middle next after split
        inactiveTriple
    have unactivated :
        G.ancestorOf mutilation conditioned middle = false :=
      G.unactivated_of_inactive_collider mutilation conditioned collider
        inactiveTriple
    have sourceAncestor :
        G.ancestorOf mutilation targets (.observed sourceIdx) = true :=
      G.ancestorOf_of_left_selected mutilation left right conditioned
        leftSelected
    have middleMem : middle ∈ expanded := by
      change middle ∈
        G.expandMoralNodes mutilation targets conditioned walk.walk
      rw [split]
      exact List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr
          (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
    have inLarge : G.ancestorOf mutilation targets middle = true :=
      G.expandMoralNodes_mem_ancestor mutilation targets conditioned
        walk.walk sourceAncestor middleMem
    cases hright : G.ancestorOf mutilation right middle with
    | true =>
        rcases (G.ancestorOf_eq_true_iff mutilation right middle).mp
            hright with ⟨u, inRight, bounded⟩
        cases condVal : conditioned u with
        | true =>
            have activated :
                G.ancestorOf mutilation conditioned middle = true :=
              (G.ancestorOf_eq_true_iff mutilation conditioned
                middle).mpr ⟨u, condVal, bounded⟩
            rw [activated] at unactivated
            contradiction
        | false =>
            exact G.exists_activePath_of_expanded_active_case
              mutilation left right conditioned walk leftSelected
              rightSelected sourceOpen targetOpen
              (.oxfordRight simple before previous middle next after
                split inactiveTriple prefixZero collider u inRight
                bounded)
    | false =>
        rcases G.exists_descendant_in_left_or_right mutilation left
            right conditioned inLarge unactivated with
          ⟨u, side, _uncond, bounded⟩
        rcases side with inLeft | inRight
        · exact G.exists_activePath_of_collider_suffix mutilation left
            right conditioned walk simple leftSelected rightSelected
            targetOpen before previous middle next after split
            inactiveTriple collider inLeft bounded
        · have ancestorRight :
              G.ancestorOf mutilation right middle = true :=
            (G.ancestorOf_eq_true_iff mutilation right middle).mpr
              ⟨u, inRight, bounded⟩
          rw [hright] at ancestorRight
          contradiction

/--
Cycle deletion on an expansion preserves endpoints and DAG adjacency.
When the resulting simple trail is internally active, it is already an
active path on the original observed endpoints.  `cutCycle` need not
preserve the inactive count: a splice triple at a repeated vertex can
be inactive even if every original window was active.
-/
theorem exists_activePath_of_simplified_zero (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (inactive : PathSpecification.inactiveColliderCount G mutilation
      conditioned
      (simplifySeparation
        (G.expandMoralNodes mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          conditioned walk.walk)) = 0) :
    Nonempty
      (PathSpecification.ActivePath G mutilation conditioned
        (.observed sourceIdx) (.observed targetIdx)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let expanded :=
    G.expandMoralNodes mutilation targets conditioned walk.walk
  let simplified := simplifySeparation expanded
  have ne := G.expandMoralNodes_ne_nil mutilation targets conditioned
    walk.walk
  have starts : simplified.head? = some (.observed sourceIdx) := by
    change (simplifySeparation expanded).head? = some (.observed sourceIdx)
    rw [simplifySeparation_head ne]
    exact G.expandMoralNodes_head mutilation targets conditioned walk.walk
  have finishes : simplified.getLast? = some (.observed targetIdx) := by
    change (simplifySeparation expanded).getLast? = some (.observed targetIdx)
    rw [simplifySeparation_getLast ne]
    exact G.expandMoralNodes_getLast mutilation targets conditioned walk.walk
  have adjacent :
      PathSpecification.Consecutive
        (PathSpecification.Adjacent G mutilation) simplified :=
    simplifySeparation_consecutive
      (G.expandMoralNodes_consecutive_adjacent mutilation targets
        conditioned walk.walk)
  exact ⟨G.activePath_of_adjacent_nodes mutilation conditioned simplified
    starts finishes (simplifySeparation_nodup expanded) adjacent inactive
    sourceOpen targetOpen⟩

/--
Oxford recursion on a collider suffix of any simple DAG-adjacent trail
that has collider-or-open middles.  Independent of how the trail was
produced (expansion, cycle deletion, or a nested suffix).
-/
theorem exists_activePath_of_open_or_collider_suffix (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {targetIdx : Fin S.count}
    (middle next : SeparationNode S)
    (after : List (SeparationNode S))
    (suffixSimple : (middle :: next :: after).Nodup)
    (suffixAdjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation)
      (middle :: next :: after))
    (suffixFinishes : (middle :: next :: after).getLast? =
      some (.observed targetIdx))
    (openOr : PathSpecification.TripleOpenOrCollider G mutilation
      conditioned (middle :: next :: after))
    (ancestors : forall vertex, vertex ∈ middle :: next :: after ->
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) vertex =
          true)
    (unactivated : G.ancestorOf mutilation conditioned middle = false)
    {uLeft : Fin S.count}
    (inLeft : left uLeft = true)
    (boundedLeft : FiniteReachability.BoundedWalk
      (G.expandedMutilatedEdge mutilation)
      G.separationNodes.length middle (.observed uLeft))
    (rightSelected : right targetIdx = true)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false) :
    Exists fun s : Fin S.count =>
      Exists fun t : Fin S.count =>
        left s = true /\ right t = true /\
          Nonempty
            (PathSpecification.ActivePath G mutilation conditioned
              (.observed s) (.observed t)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
      SeparationNode.beq G.separationNodes
      (G.expandedMutilatedEdge mutilation)
      SeparationNode.beq_eq_true_iff SeparationNode.mem_all boundedLeft with
    ⟨directedLeft⟩
  cases hcount : PathSpecification.inactiveColliderCount G mutilation
      conditioned (middle :: next :: after) with
  | zero =>
      exact ⟨uLeft, targetIdx, inLeft, rightSelected,
        G.exists_activePath_oxford_left mutilation conditioned next after
          middle suffixFinishes suffixSimple suffixAdjacent hcount
          targetOpen unactivated directedLeft⟩
  | succ n =>
      have inactivePos :
          0 < PathSpecification.inactiveColliderCount G mutilation
            conditioned (middle :: next :: after) := by
        rw [hcount]
        exact Nat.succ_pos _
      rcases PathSpecification.exists_inactive_split
          (middle :: next :: after) inactivePos with
        ⟨beforeS, prevS, midS, nextS, afterS, splitS, inactiveS, prefixZeroS⟩
      have colliderS :
          PathSpecification.isColliderBool G mutilation prevS midS nextS =
            true :=
        G.isColliderBool_of_inactive_openOrCollider mutilation conditioned
          openOr splitS inactiveS
      have unactivatedS :
          G.ancestorOf mutilation conditioned midS = false :=
        G.unactivated_of_inactive_collider mutilation conditioned colliderS
          inactiveS
      have midSMem : midS ∈ middle :: next :: after := by
        rw [splitS]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr
            (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
      have inLargeS : G.ancestorOf mutilation targets midS = true :=
        ancestors midS midSMem
      have prefixFacts :=
        G.prefix_adjacent_of_inactive_split mutilation
          (by simpa [splitS] using suffixSimple)
          (by simpa [splitS] using suffixAdjacent)
      have prefixStarts : (beforeS ++ prevS :: [midS]).head? =
          some middle :=
        prefix_head_of_inactive_split (before := beforeS) (previous := prevS)
          (middle := midS) (next := nextS) (after := afterS)
          (source := middle)
          (by
            have h : (middle :: next :: after).head? = some middle := by
              simp
            simpa [splitS] using h)
      have middleOpen : blockedBy conditioned middle = false :=
        G.blockedBy_false_of_unactivated mutilation conditioned unactivated
      have intoMidS : G.expandedMutilatedEdge mutilation prevS midS = true :=
        ((PathSpecification.IsCollider_iff_isColliderBool G mutilation
          prevS midS nextS).mpr colliderS).1
      have nestedSimple :=
        suffix_nodup_of_inactive_split
          (by simpa [splitS] using suffixSimple)
      have nestedAdjacent :=
        suffix_adjacent_of_inactive_split
          (by simpa [splitS] using suffixAdjacent)
      have nestedFinishes : (midS :: nextS :: afterS).getLast? =
          some (.observed targetIdx) := by
        have listEq :
            middle :: next :: after =
              (beforeS ++ [prevS]) ++ midS :: nextS :: afterS := by
          have : beforeS ++ prevS :: midS :: nextS :: afterS =
              (beforeS ++ [prevS]) ++ midS :: nextS :: afterS :=
            (List.append_assoc beforeS [prevS]
              (midS :: nextS :: afterS)).symm
          rw [← splitS] at this
          exact this
        exact getLast?_suffix_append (before := beforeS ++ [prevS])
          (node := midS) (after := nextS :: afterS)
          (by
            rw [← listEq]
            exact suffixFinishes)
      have nestedOpen :
          PathSpecification.TripleOpenOrCollider G mutilation
            conditioned (midS :: nextS :: afterS) :=
        PathSpecification.TripleOpenOrCollider.suffix_of_append
          (beforeS ++ [prevS]) midS (nextS :: afterS)
          (by
            have eq :
                middle :: next :: after =
                  (beforeS ++ [prevS]) ++ midS :: nextS :: afterS := by
              have : beforeS ++ prevS :: midS :: nextS :: afterS =
                  (beforeS ++ [prevS]) ++ midS :: nextS :: afterS :=
                (List.append_assoc beforeS [prevS]
                  (midS :: nextS :: afterS)).symm
              rw [← splitS] at this
              exact this
            rw [← eq]
            exact openOr)
      have nestedAncestors : forall vertex,
          vertex ∈ midS :: nextS :: afterS ->
            G.ancestorOf mutilation targets vertex = true := by
        intro vertex member
        apply ancestors
        rw [splitS]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr (Or.inr member)))
      cases hrightS : G.ancestorOf mutilation right midS with
      | true =>
          rcases (G.ancestorOf_eq_true_iff mutilation right midS).mp
              hrightS with ⟨uRight, inRight, boundedRight⟩
          cases condVal : conditioned uRight with
          | true =>
              have activated :
                  G.ancestorOf mutilation conditioned midS = true :=
                (G.ancestorOf_eq_true_iff mutilation conditioned midS).mpr
                  ⟨uRight, condVal, boundedRight⟩
              rw [activated] at unactivatedS
              contradiction
          | false =>
              rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
                  SeparationNode.beq G.separationNodes
                  (G.expandedMutilatedEdge mutilation)
                  SeparationNode.beq_eq_true_iff SeparationNode.mem_all
                  boundedRight with ⟨directedRight⟩
              rcases G.exists_activePath_oxford_right mutilation
                  conditioned beforeS prevS midS prefixStarts prefixFacts.1
                  prefixFacts.2 prefixZeroS middleOpen intoMidS unactivatedS
                  directedRight with ⟨pathMid⟩
              exact ⟨uLeft, uRight, inLeft, inRight,
                G.exists_activePath_oxford_left_of_activePath mutilation
                  conditioned pathMid unactivated directedLeft⟩
      | false =>
          rcases G.exists_descendant_in_left_or_right mutilation left right
              conditioned inLargeS unactivatedS with
            ⟨uS, side, _uncond, boundedS⟩
          rcases side with inLeftS | inRightS
          · exact G.exists_activePath_of_open_or_collider_suffix mutilation
              left right conditioned midS nextS afterS nestedSimple
              nestedAdjacent nestedFinishes nestedOpen nestedAncestors
              unactivatedS inLeftS boundedS rightSelected targetOpen
          · have ancestorRight :
                G.ancestorOf mutilation right midS = true :=
              (G.ancestorOf_eq_true_iff mutilation right midS).mpr
                ⟨uS, inRightS, boundedS⟩
            rw [hrightS] at ancestorRight
            contradiction
termination_by (middle :: next :: after).length
decreasing_by
  exact nested_suffix_length_lt splitS

/--
A simple DAG-adjacent trail whose every window is a collider or has an
open middle yields an active path in `left × right`.  Zero-inactive
trails are already active paths; a first inactive window is a collider
and Oxford reroutes to a descendant in `left` or `right`.
-/
theorem exists_activePath_of_open_or_collider_nodes (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (nodes : List (SeparationNode S))
    (starts : nodes.head? = some (.observed sourceIdx))
    (finishes : nodes.getLast? = some (.observed targetIdx))
    (simple : nodes.Nodup)
    (adjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation) nodes)
    (openOr : PathSpecification.TripleOpenOrCollider G mutilation
      conditioned nodes)
    (ancestors : forall vertex, vertex ∈ nodes ->
      G.ancestorOf mutilation
        (NodeSet.union left (NodeSet.union right conditioned)) vertex =
          true)
    (leftSelected : left sourceIdx = true)
    (rightSelected : right targetIdx = true)
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false) :
    Exists fun s : Fin S.count =>
      Exists fun t : Fin S.count =>
        left s = true /\ right t = true /\
          Nonempty
            (PathSpecification.ActivePath G mutilation conditioned
              (.observed s) (.observed t)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  cases hcount : PathSpecification.inactiveColliderCount G mutilation
      conditioned nodes with
  | zero =>
      exact ⟨sourceIdx, targetIdx, leftSelected, rightSelected,
        ⟨G.activePath_of_adjacent_nodes mutilation conditioned nodes
          starts finishes simple adjacent hcount sourceOpen targetOpen⟩⟩
  | succ n =>
      have inactivePos :
          0 < PathSpecification.inactiveColliderCount G mutilation
            conditioned nodes := by
        rw [hcount]
        exact Nat.succ_pos _
      rcases PathSpecification.exists_inactive_split nodes inactivePos with
        ⟨before, previous, middle, next, after, split, inactiveTriple,
          prefixZero⟩
      have collider :
          PathSpecification.isColliderBool G mutilation previous middle
            next = true :=
        G.isColliderBool_of_inactive_openOrCollider mutilation conditioned
          openOr split inactiveTriple
      have unactivated :
          G.ancestorOf mutilation conditioned middle = false :=
        G.unactivated_of_inactive_collider mutilation conditioned collider
          inactiveTriple
      have middleMem : middle ∈ nodes := by
        rw [split]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr
            (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
      have inLarge : G.ancestorOf mutilation targets middle = true :=
        ancestors middle middleMem
      have prefixFacts :=
        G.prefix_adjacent_of_inactive_split mutilation
          (by simpa [split] using simple)
          (by simpa [split] using adjacent)
      have prefixStarts : (before ++ previous :: [middle]).head? =
          some (.observed sourceIdx) :=
        prefix_head_of_inactive_split (before := before) (previous := previous)
          (middle := middle) (next := next) (after := after)
          (source := .observed sourceIdx)
          (by simpa [split] using starts)
      have intoMiddle : G.expandedMutilatedEdge mutilation previous middle =
          true :=
        ((PathSpecification.IsCollider_iff_isColliderBool G mutilation
          previous middle next).mpr collider).1
      have suffixSimple :=
        suffix_nodup_of_inactive_split (by simpa [split] using simple)
      have suffixAdjacent :=
        suffix_adjacent_of_inactive_split (by simpa [split] using adjacent)
      have suffixFinishes : (middle :: next :: after).getLast? =
          some (.observed targetIdx) := by
        have listEq :
            nodes = (before ++ [previous]) ++ middle :: next :: after := by
          have : before ++ previous :: middle :: next :: after =
              (before ++ [previous]) ++ middle :: next :: after :=
            (List.append_assoc before [previous]
              (middle :: next :: after)).symm
          rw [← split] at this
          exact this
        exact getLast?_suffix_append (before := before ++ [previous])
          (node := middle) (after := next :: after)
          (by
            rw [← listEq]
            exact finishes)
      have suffixOpen :
          PathSpecification.TripleOpenOrCollider G mutilation
            conditioned (middle :: next :: after) :=
        PathSpecification.TripleOpenOrCollider.suffix_of_append
          (before ++ [previous]) middle (next :: after)
          (by
            have eq :
                nodes =
                  (before ++ [previous]) ++ middle :: next :: after := by
              have : before ++ previous :: middle :: next :: after =
                  (before ++ [previous]) ++ middle :: next :: after :=
                (List.append_assoc before [previous]
                  (middle :: next :: after)).symm
              rw [← split] at this
              exact this
            rw [← eq]
            exact openOr)
      have suffixAncestors : forall vertex,
          vertex ∈ middle :: next :: after ->
            G.ancestorOf mutilation targets vertex = true := by
        intro vertex member
        apply ancestors
        rw [split]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr (Or.inr member)))
      cases hright : G.ancestorOf mutilation right middle with
      | true =>
          rcases (G.ancestorOf_eq_true_iff mutilation right middle).mp
              hright with ⟨u, inRight, bounded⟩
          cases condVal : conditioned u with
          | true =>
              have activated :
                  G.ancestorOf mutilation conditioned middle = true :=
                (G.ancestorOf_eq_true_iff mutilation conditioned middle).mpr
                  ⟨u, condVal, bounded⟩
              rw [activated] at unactivated
              contradiction
          | false =>
              rcases FiniteReachability.nonempty_simpleWalk_of_boundedWalk
                  SeparationNode.beq G.separationNodes
                  (G.expandedMutilatedEdge mutilation)
                  SeparationNode.beq_eq_true_iff SeparationNode.mem_all
                  bounded with ⟨directed⟩
              exact ⟨sourceIdx, u, leftSelected, inRight,
                G.exists_activePath_oxford_right mutilation conditioned
                  before previous middle prefixStarts prefixFacts.1
                  prefixFacts.2 prefixZero sourceOpen intoMiddle unactivated
                  directed⟩
      | false =>
          rcases G.exists_descendant_in_left_or_right mutilation left right
              conditioned inLarge unactivated with
            ⟨u, side, _uncond, bounded⟩
          rcases side with inLeft | inRight
          · exact G.exists_activePath_of_open_or_collider_suffix mutilation
              left right conditioned middle next after suffixSimple
              suffixAdjacent suffixFinishes suffixOpen suffixAncestors
              unactivated inLeft bounded rightSelected targetOpen
          · have ancestorRight :
                G.ancestorOf mutilation right middle = true :=
              (G.ancestorOf_eq_true_iff mutilation right middle).mpr
                ⟨u, inRight, bounded⟩
            rw [hright] at ancestorRight
            contradiction

/--
An expanded moral walk, simplified by cycle deletion, is a simple
DAG-adjacent collider-or-open trail on the original endpoints, so it
yields an active path in `left × right`.
-/
theorem exists_activePath_of_expanded (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (walk : FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned)
      (.observed sourceIdx) (.observed targetIdx))
    (leftSelected : left sourceIdx = true)
    (rightSelected : right targetIdx = true)
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false) :
    Exists fun s : Fin S.count =>
      Exists fun t : Fin S.count =>
        left s = true /\ right t = true /\
          Nonempty
            (PathSpecification.ActivePath G mutilation conditioned
              (.observed s) (.observed t)) := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let expanded :=
    G.expandMoralNodes mutilation targets conditioned walk.walk
  let simplified := simplifySeparation expanded
  have ne := G.expandMoralNodes_ne_nil mutilation targets conditioned
    walk.walk
  have starts : simplified.head? = some (.observed sourceIdx) := by
    rw [simplifySeparation_head ne]
    exact G.expandMoralNodes_head mutilation targets conditioned walk.walk
  have finishes : simplified.getLast? = some (.observed targetIdx) := by
    rw [simplifySeparation_getLast ne]
    exact G.expandMoralNodes_getLast mutilation targets conditioned walk.walk
  have adjacent :
      PathSpecification.Consecutive
        (PathSpecification.Adjacent G mutilation) expanded :=
    G.expandMoralNodes_consecutive_adjacent mutilation targets
      conditioned walk.walk
  have adjacentS := simplifySeparation_consecutive adjacent
  have openOr :=
    G.expandMoralNodes_tripleOpenOrCollider mutilation targets
      conditioned walk.walk
  have openOrS :=
    G.simplifySeparation_tripleOpenOrCollider mutilation conditioned
      adjacent openOr
  have sourceAncestor :
      G.ancestorOf mutilation targets (.observed sourceIdx) = true :=
    G.ancestorOf_of_left_selected mutilation left right conditioned
      leftSelected
  have ancestors : forall vertex, vertex ∈ simplified ->
      G.ancestorOf mutilation targets vertex = true := by
    intro vertex member
    exact G.expandMoralNodes_mem_ancestor mutilation targets conditioned
      walk.walk sourceAncestor (mem_simplifySeparation member)
  exact G.exists_activePath_of_open_or_collider_nodes mutilation left right
    conditioned simplified starts finishes (simplifySeparation_nodup expanded)
    adjacentS openOrS ancestors leftSelected rightSelected sourceOpen
    targetOpen

/--
Deleting conditioned internal vertices from an active path yields a walk in
the open ancestral moral graph.  A deleted vertex is necessarily a collider;
its two neighbours are joined by the corresponding moral edge.
-/
theorem open_filter_consecutive_moral (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    (nodes : List (SeparationNode S)) {source target : SeparationNode S}
    (starts : nodes.head? = some source)
    (finishes : nodes.getLast? = some target)
    (simple : nodes.Nodup)
    (adjacent : PathSpecification.Consecutive
      (PathSpecification.Adjacent G mutilation) nodes)
    (internalActive : PathSpecification.InternalTriplesActive
      G mutilation conditioned nodes)
    (sourceOpen : blockedBy conditioned source = false)
    (targetOpen : blockedBy conditioned target = false)
    (ancestor : forall node, node ∈ nodes ->
      G.ancestorOf mutilation targets node = true) :
    PathSpecification.Consecutive
      (fun left right =>
        G.MoralOpenEdge mutilation targets conditioned left right = true)
      (nodes.filter (fun node => !(blockedBy conditioned node))) := by
  cases nodes with
  | nil => simp at starts
  | cons first tail =>
      simp only [List.head?_cons, Option.some.injEq] at starts
      subst source
      cases tail with
      | nil => simp [List.filter, sourceOpen,
          PathSpecification.Consecutive]
      | cons middle rest =>
          have firstAncestor := ancestor first (by simp)
          have middleAncestor := ancestor middle (by simp)
          have firstMiddleAdjacent := adjacent.1
          have tailFinishes : (middle :: rest).getLast? = some target := by
            simpa using finishes
          have tailSimple : (middle :: rest).Nodup :=
            (List.nodup_cons.mp simple).2
          have tailAncestor : forall node, node ∈ middle :: rest ->
              G.ancestorOf mutilation targets node = true := by
            intro node member
            exact ancestor node (by simp [member])
          cases middleBlocked : blockedBy conditioned middle with
          | false =>
              have moralFirstMiddle := G.moralOpenEdge_of_ancestral
                mutilation targets conditioned sourceOpen middleBlocked
                (G.ancestralMoralEdge_of_adjacent mutilation targets
                  firstAncestor middleAncestor firstMiddleAdjacent)
              have tailMoral := G.open_filter_consecutive_moral
                mutilation targets conditioned (middle :: rest)
                (source := middle) (target := target) rfl tailFinishes
                tailSimple adjacent.2 internalActive.tail middleBlocked
                targetOpen tailAncestor
              simpa [List.filter, sourceOpen, middleBlocked] using
                And.intro moralFirstMiddle tailMoral
          | true =>
              cases rest with
              | nil =>
                  simp only [List.getLast?_cons_cons, List.getLast?_singleton,
                    Option.some.injEq] at finishes
                  subst target
                  rw [middleBlocked] at targetOpen
                  contradiction
              | cons next suffix =>
                  have nextAncestor := ancestor next (by simp)
                  have middleTriple : PathSpecification.TripleActive G
                      mutilation conditioned first middle next :=
                    PathSpecification.InternalTriplesActive.triple_of_append
                      [] suffix first middle next internalActive
                  have middleCollider :=
                    PathSpecification.TripleActive.collider_of_blocked
                      G mutilation conditioned first middle next middleTriple
                        middleBlocked
                  have nextOpen : blockedBy conditioned next = false := by
                    cases nextBlocked : blockedBy conditioned next with
                    | false => rfl
                    | true =>
                        cases suffix with
                        | nil =>
                            simp only [List.getLast?_cons_cons,
                              List.getLast?_singleton, Option.some.injEq]
                                at finishes
                            subst target
                            rw [nextBlocked] at targetOpen
                            contradiction
                        | cons after remaining =>
                            have nextTriple : PathSpecification.TripleActive G
                                mutilation conditioned middle next after :=
                              PathSpecification.InternalTriplesActive.triple_of_append
                                [first] remaining middle next after
                                  internalActive
                            have nextCollider :=
                              PathSpecification.TripleActive.collider_of_blocked
                                G mutilation conditioned middle next after
                                  nextTriple nextBlocked
                            have firstRank :=
                              G.expandedMutilatedEdge_rank_lt mutilation
                                middleCollider.2
                            have secondRank :=
                              G.expandedMutilatedEdge_rank_lt mutilation
                                nextCollider.1
                            omega
                  have firstNeNext : first ≠ next := by
                    intro same
                    subst next
                    have firstNotInTail := (List.nodup_cons.mp simple).1
                    exact firstNotInTail (by simp)
                  have moralFirstNext := G.moralOpenEdge_of_ancestral
                    mutilation targets conditioned sourceOpen nextOpen
                    (G.ancestralMoralEdge_of_collider mutilation targets
                      firstAncestor middleAncestor nextAncestor firstNeNext
                        middleCollider)
                  have afterMiddleFinishes :
                      (next :: suffix).getLast? = some target := by
                    simpa using finishes
                  have afterMiddleSimple : (next :: suffix).Nodup :=
                    (List.nodup_cons.mp tailSimple).2
                  have afterMiddleAdjacent :
                      PathSpecification.Consecutive
                        (PathSpecification.Adjacent G mutilation)
                        (next :: suffix) := adjacent.2.2
                  have afterMiddleActive :
                      PathSpecification.InternalTriplesActive
                        G mutilation conditioned (next :: suffix) :=
                    internalActive.tail.tail
                  have afterMiddleAncestor : forall node,
                      node ∈ next :: suffix ->
                        G.ancestorOf mutilation targets node = true := by
                    intro node member
                    exact ancestor node (by simp [member])
                  have afterMiddleMoral := G.open_filter_consecutive_moral
                    mutilation targets conditioned (next :: suffix)
                    (source := next) (target := target) rfl
                    afterMiddleFinishes afterMiddleSimple afterMiddleAdjacent
                    afterMiddleActive nextOpen targetOpen afterMiddleAncestor
                  simpa [List.filter, sourceOpen, middleBlocked, nextOpen]
                    using And.intro moralFirstNext afterMiddleMoral
termination_by nodes.length

theorem moralReachable_eq_true_iff (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    (source target : SeparationNode S) :
    G.moralReachable mutilation targets conditioned source target = true <->
      FiniteReachability.BoundedWalk
        (G.MoralOpenEdge mutilation targets conditioned)
        G.separationNodes.length source target := by
  unfold moralReachable
  change FiniteReachability.within SeparationNode.beq G.separationNodes
      (G.MoralOpenEdge mutilation targets conditioned)
      G.separationNodes.length source target = true <-> _
  apply FiniteReachability.within_eq_true_iff_boundedWalk
  · exact SeparationNode.beq_eq_true_iff
  · exact SeparationNode.mem_all

theorem moralReachable_of_activePath (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {source target : Fin S.count}
    (sourceSelected : left source = true)
    (targetSelected : right target = true)
    (path : PathSpecification.ActivePath G mutilation conditioned
      (.observed source) (.observed target)) :
    G.moralReachable mutilation
      (NodeSet.union left (NodeSet.union right conditioned)) conditioned
      (.observed source) (.observed target) = true := by
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  let retained := path.nodes.filter
    (fun node => !(blockedBy conditioned node))
  have retainedStarts : retained.head? = some (.observed source) := by
    rcases List.head?_eq_some_iff.mp path.starts with ⟨tail, split⟩
    apply List.head?_eq_some_iff.mpr
    refine ⟨tail.filter (fun node => !(blockedBy conditioned node)), ?_⟩
    simp [retained, split, path.source_open]
  have retainedFinishes : retained.getLast? = some (.observed target) := by
    rcases List.getLast?_eq_some_iff.mp path.finishes with
      ⟨before, split⟩
    apply List.getLast?_eq_some_iff.mpr
    refine ⟨before.filter (fun node => !(blockedBy conditioned node)), ?_⟩
    simp [retained, split, path.target_open]
  have allAncestors := G.activePath_nodes_ancestor mutilation
    left right conditioned sourceSelected targetSelected path
  have retainedConsecutive : PathSpecification.Consecutive
      (fun left right =>
        G.MoralOpenEdge mutilation targets conditioned left right = true)
      retained := by
    apply G.open_filter_consecutive_moral mutilation targets conditioned
      path.nodes path.starts path.finishes path.simple path.adjacent
      path.internal_active path.source_open path.target_open
    simpa [targets] using allAncestors
  have reachable : FiniteReachability.Reachable
      (G.MoralOpenEdge mutilation targets conditioned)
      (.observed source) (.observed target) :=
    FiniteReachability.Reachable.of_consecutive
      (G.MoralOpenEdge mutilation targets conditioned) retained
      retainedStarts retainedFinishes retainedConsecutive
  have bounded := FiniteReachability.boundedWalk_of_reachable
    SeparationNode.beq G.separationNodes
    (G.MoralOpenEdge mutilation targets conditioned)
    SeparationNode.beq_eq_true_iff SeparationNode.mem_all reachable
  exact (G.moralReachable_eq_true_iff mutilation targets conditioned
    (.observed source) (.observed target)).mpr bounded

theorem nonempty_simpleMoralWalk_of_reachable (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (targets conditioned : NodeSet S)
    {source target : SeparationNode S}
    (reachable :
      G.moralReachable mutilation targets conditioned source target = true) :
    Nonempty (FiniteReachability.SimpleWalk
      (G.MoralOpenEdge mutilation targets conditioned) source target) := by
  apply FiniteReachability.nonempty_simpleWalk_of_boundedWalk
    SeparationNode.beq G.separationNodes
    (G.MoralOpenEdge mutilation targets conditioned)
    SeparationNode.beq_eq_true_iff SeparationNode.mem_all
  exact (G.moralReachable_eq_true_iff mutilation targets conditioned
    source target).mp reachable

/--
Moral reachability yields an active-path witness: expand a simple moral
walk, delete cycles, and Oxford-reroute the resulting simple
collider-or-open trail.
-/
theorem exists_activePath_of_moralReachable (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    {sourceIdx targetIdx : Fin S.count}
    (leftSelected : left sourceIdx = true)
    (rightSelected : right targetIdx = true)
    (sourceOpen : blockedBy conditioned (.observed sourceIdx) = false)
    (targetOpen : blockedBy conditioned (.observed targetIdx) = false)
    (reachable :
      G.moralReachable mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned (.observed sourceIdx) (.observed targetIdx) = true) :
    Exists fun s : Fin S.count =>
      Exists fun t : Fin S.count =>
        left s = true /\ right t = true /\
          Nonempty
            (PathSpecification.ActivePath G mutilation conditioned
              (.observed s) (.observed t)) := by
  rcases G.nonempty_simpleMoralWalk_of_reachable mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned reachable with ⟨walk⟩
  exact G.exists_activePath_of_expanded mutilation left right conditioned
    walk leftSelected rightSelected sourceOpen targetOpen

/-- Unfold the outer finite searches in the executable separation test. -/
theorem dSeparated_eq_true_iff_no_moralReachable (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S) :
    G.dSeparated mutilation left right conditioned = true <->
      Not (Exists fun source : Fin S.count =>
        Exists fun target : Fin S.count =>
          left source = true /\ conditioned source = false /\
            right target = true /\ conditioned target = false /\
              G.moralReachable mutilation
                (NodeSet.union left (NodeSet.union right conditioned))
                conditioned (.observed source) (.observed target) = true) := by
  simp only [dSeparated]
  rw [bool_not_any_eq_true_iff]
  constructor
  · intro none
    rintro ⟨source, target, leftSelected, sourceOpen,
      rightSelected, targetOpen, reachable⟩
    apply none
    refine ⟨source, by simp [List.mem_ofFn], ?_⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨leftSelected, ?_⟩, ?_⟩
    · simp [sourceOpen]
    · apply List.any_eq_true.mpr
      refine ⟨target, by simp [List.mem_ofFn], ?_⟩
      exact Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr ⟨rightSelected, by simp [targetOpen]⟩,
          reachable⟩
  · intro none
    rintro ⟨source, _sourceMember, sourceHolds⟩
    rcases Bool.and_eq_true_iff.mp sourceHolds with
      ⟨leftAndOpen, targetExists⟩
    rcases Bool.and_eq_true_iff.mp leftAndOpen with
      ⟨leftSelected, sourceOpen⟩
    rcases List.any_eq_true.mp targetExists with
      ⟨target, _targetMember, targetHolds⟩
    rcases Bool.and_eq_true_iff.mp targetHolds with
      ⟨rightAndOpen, reachable⟩
    rcases Bool.and_eq_true_iff.mp rightAndOpen with
      ⟨rightSelected, targetOpen⟩
    apply none
    exact ⟨source, target, leftSelected, by simpa using sourceOpen,
      rightSelected, by simpa using targetOpen, reachable⟩

/--
The finite ancestral-moral algorithm is sound for the active-path
specification: whenever it reports separation, no active path exists.
-/
theorem dSeparated_implies_pathDSeparated (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    (separated : G.dSeparated mutilation left right conditioned = true) :
    PathSpecification.PathDSeparated G mutilation left right conditioned := by
  have noMoral :=
    (G.dSeparated_eq_true_iff_no_moralReachable mutilation
      left right conditioned).mp separated
  rintro ⟨source, target, sourceSelected, targetSelected, activePath⟩
  rcases activePath with ⟨activePath⟩
  apply noMoral
  refine ⟨source, target, sourceSelected, activePath.source_open,
    targetSelected, activePath.target_open, ?_⟩
  exact G.moralReachable_of_activePath mutilation left right conditioned
    sourceSelected targetSelected activePath

/--
The finite ancestral-moral algorithm is complete for the active-path
specification: whenever an active path exists, the search reports
dependence.
-/
theorem pathDSeparated_implies_dSeparated (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S)
    (separated : PathSpecification.PathDSeparated G mutilation left right
      conditioned) :
    G.dSeparated mutilation left right conditioned = true := by
  apply (G.dSeparated_eq_true_iff_no_moralReachable mutilation
    left right conditioned).mpr
  rintro ⟨source, target, leftSelected, sourceOpen, rightSelected,
    targetOpen, reachable⟩
  rcases G.exists_activePath_of_moralReachable mutilation left right
      conditioned leftSelected rightSelected sourceOpen targetOpen
      reachable with ⟨s, t, sSelected, tSelected, active⟩
  exact separated ⟨s, t, sSelected, tSelected, active⟩

/-- Algorithmic d-separation coincides with the active-path specification. -/
theorem dSeparated_iff_pathDSeparated (G : ObservedGraph S)
    (mutilation : GraphMutilation S) (left right conditioned : NodeSet S) :
    G.dSeparated mutilation left right conditioned = true <->
      PathSpecification.PathDSeparated G mutilation left right
        conditioned :=
  ⟨G.dSeparated_implies_pathDSeparated mutilation left right conditioned,
    G.pathDSeparated_implies_dSeparated mutilation left right conditioned⟩

/-!
## A constructive moral separator

The global-Markov argument needs an actual side of the ancestral moral graph,
not merely the proposition that no active path exists.  The Boolean set below
is the component reachable from an open vertex of `left`.  It is computed by
the already verified finite moral-reachability search, includes every open
left endpoint, excludes every open right endpoint under d-separation, and is
closed across moral edges.  These facts provide the canonical partition for
the remaining probability factorization in soundness.
-/

/-- Vertices morally reachable from an open member of `left` in the ancestral
moral graph generated by `left ∪ right ∪ conditioned`. -/
def moralLeftSide (G : ObservedGraph S)
    (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S) : SeparationNode S → Bool :=
  fun node =>
    (NodeSet.members left).any (fun source =>
      !(conditioned source) &&
        G.moralReachable mutilation
          (NodeSet.union left (NodeSet.union right conditioned))
          conditioned (.observed source) node)

/-- Every open selected left endpoint lies in the canonical moral side. -/
theorem moralLeftSide_of_left
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S) (source : Fin S.count)
    (selected : left source = true) (openSource : conditioned source = false) :
    G.moralLeftSide mutilation left right conditioned
      (.observed source) = true := by
  have reachable :
      G.moralReachable mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned (.observed source) (.observed source) = true :=
    (G.moralReachable_eq_true_iff mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned (.observed source) (.observed source)).mpr
        (FiniteReachability.BoundedWalk.refl _ _ _)
  unfold ObservedGraph.moralLeftSide
  exact List.any_eq_true.mpr
    ⟨source, (NodeSet.mem_members_iff left source).mpr selected,
      by simp [openSource, reachable]⟩

/-- Under path d-separation, every open selected right endpoint is outside
the canonical left moral side. -/
theorem moralLeftSide_not_of_right
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    (separated : PathSpecification.PathDSeparated G mutilation
      left right conditioned)
    (target : Fin S.count) (selected : right target = true)
    (openTarget : conditioned target = false) :
    G.moralLeftSide mutilation left right conditioned
      (.observed target) = false := by
  cases side : G.moralLeftSide mutilation left right conditioned
      (.observed target) with
  | false => rfl
  | true =>
      have anySource :
          (NodeSet.members left).any (fun source =>
            !(conditioned source) &&
              G.moralReachable mutilation
                (NodeSet.union left (NodeSet.union right conditioned))
                conditioned (.observed source) (.observed target)) = true := by
        simpa [ObservedGraph.moralLeftSide] using side
      rcases List.any_eq_true.mp anySource with
        ⟨source, sourceMember, sourceData⟩
      have sourceParts := Bool.and_eq_true_iff.mp sourceData
      have sourceSelected :=
        (NodeSet.mem_members_iff left source).mp sourceMember
      have sourceOpen : conditioned source = false := by
        simpa using sourceParts.1
      have noMoral :=
        (G.dSeparated_eq_true_iff_no_moralReachable mutilation
          left right conditioned).mp
          ((G.dSeparated_iff_pathDSeparated mutilation left right
            conditioned).mpr separated)
      exact False.elim (noMoral ⟨source, target, sourceSelected, sourceOpen,
        selected, openTarget, sourceParts.2⟩)

/-- The canonical left side is closed under every edge of the open ancestral
moral graph. -/
theorem moralLeftSide_closed
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    {source target : SeparationNode S}
    (sourceIn : G.moralLeftSide mutilation left right conditioned source =
      true)
    (edge : G.MoralOpenEdge mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned source target = true) :
    G.moralLeftSide mutilation left right conditioned target = true := by
  have anyStart :
      (NodeSet.members left).any (fun start =>
        !(conditioned start) &&
          G.moralReachable mutilation
            (NodeSet.union left (NodeSet.union right conditioned))
            conditioned (.observed start) source) = true := by
    simpa [ObservedGraph.moralLeftSide] using sourceIn
  rcases List.any_eq_true.mp anyStart with
    ⟨start, startMember, startData⟩
  have startParts := Bool.and_eq_true_iff.mp startData
  let moralEdge := G.MoralOpenEdge mutilation
    (NodeSet.union left (NodeSet.union right conditioned)) conditioned
  have leftWalk : FiniteReachability.BoundedWalk moralEdge
      G.separationNodes.length (.observed start) source := by
    simpa [moralEdge] using
      (G.moralReachable_eq_true_iff mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned (.observed start) source).mp startParts.2
  have rightWalk : FiniteReachability.BoundedWalk moralEdge 1 source target :=
    ⟨1, Nat.le_refl _,
      ⟨FiniteReachability.ExactWalk.step edge
        (FiniteReachability.ExactWalk.refl target)⟩⟩
  have reachable : FiniteReachability.Reachable moralEdge
      (.observed start) target :=
    FiniteReachability.Reachable.of_bounded (leftWalk.trans rightWalk)
  have bounded : FiniteReachability.BoundedWalk moralEdge
      G.separationNodes.length (.observed start) target :=
    FiniteReachability.boundedWalk_of_reachable SeparationNode.beq
      G.separationNodes moralEdge SeparationNode.beq_eq_true_iff
      SeparationNode.mem_all reachable
  have targetReachable :
      G.moralReachable mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        conditioned (.observed start) target = true :=
    (G.moralReachable_eq_true_iff mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned (.observed start) target).mpr (by
        simpa [moralEdge] using bounded)
  unfold ObservedGraph.moralLeftSide
  exact List.any_eq_true.mpr
    ⟨start, startMember,
      Bool.and_eq_true_iff.mpr ⟨startParts.1, targetReachable⟩⟩

/-- No open ancestral moral edge crosses from the canonical left side to its
Boolean complement. -/
theorem moralOpenEdge_crosses_moralLeftSide_false
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S)
    {source target : SeparationNode S}
    (sourceIn : G.moralLeftSide mutilation left right conditioned source =
      true)
    (targetOut : G.moralLeftSide mutilation left right conditioned target =
      false) :
    G.MoralOpenEdge mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned source target = false := by
  cases edge : G.MoralOpenEdge mutilation
      (NodeSet.union left (NodeSet.union right conditioned))
      conditioned source target with
  | false => rfl
  | true =>
      have targetIn := G.moralLeftSide_closed mutilation
        left right conditioned sourceIn edge
      rw [targetOut] at targetIn
      contradiction

def dSeparationCorrectness (G : ObservedGraph S) :
    DSeparationCorrectness G where
  algorithm_iff_active_path := G.dSeparated_iff_pathDSeparated

end ObservedGraph

/-- Compile an executable rule side condition to its path form using the
checked algorithm-path correspondence. -/
def DoRuleApplication.toPathChecked
    {G : ObservedGraph S} {left right : Kernel S}
    (application : DoRuleApplication G left right) :
    PathDoRuleApplication G left right :=
  DoRuleApplication.mapSeparation
    (source := executableRuleSeparation G)
    (target := pathRuleSeparation G)
    (fun mutilation first second conditioned separated =>
      G.dSeparated_implies_pathDSeparated mutilation first second conditioned
        separated)
    application

end Causality
end Thesis
