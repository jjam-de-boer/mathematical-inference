import Thesis.Causality.Derivation

namespace Thesis
namespace Causality

/-!
# Generic correctness of finite reachability

Exact and bounded walks, finite-search correctness, shortest/simple walk
construction and the finite carrier bound are shared structural mathematics.
They do not depend on d-separation, c-components or a causal model. Their
Boolean equality and explicit carrier enumeration remain supplied data, so
path shortening neither chooses a witness from an arbitrary proposition nor
uses a global decision principle.

These proofs formerly preceded the graph-specific development in
CausalTransport.DSeparationCorrectness. Moving the generic foundation here
allows both that development and the intrinsic component/rank layer to use
it without a dependency cycle. All public names, statements and proof bodies
are retained. The relation-parametric list predicate keeps its historical
PathSpecification.Consecutive name for the same compatibility reason.

Derivation supplies the original executable reachability operations. Only
their generic correctness is factored here; the active-path and moral-graph
theorems remain in the causal transport layer.
-/

namespace PathSpecification

/-- Consecutive vertices satisfy a supplied relation; this predicate itself
has no graph, endpoint, collider or probabilistic assumption. -/
def Consecutive {X : Type u} (relation : X -> X -> Prop) : List X -> Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      relation left right /\ Consecutive relation (right :: rest)

/-- Widen the edge relation of a consecutive list without changing its
vertices. This is relation-parametric list mathematics: hedge readout routes
use it to pass from a directed edge to strict topological increase. Keeping
the original proof beside `Consecutive` avoids importing active-path and
moral-graph correctness merely to obtain this implication. The old
`DSeparationCorrectness` import continues to expose the same declaration. -/
theorem Consecutive.mono {r s : α -> α -> Prop}
    (included : forall left right, r left right -> s left right) :
    forall nodes : List α,
      Consecutive r nodes -> Consecutive s nodes
  | [] => fun _ => by simp [Consecutive]
  | [_] => fun _ => by simp [Consecutive]
  | left :: right :: rest => fun consecutive =>
      ⟨included left right consecutive.1,
        Consecutive.mono included (right :: rest) consecutive.2⟩

end PathSpecification

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

end Causality
end Thesis
