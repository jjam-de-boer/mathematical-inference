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

end ExactWalk

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

end PathSpecification

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

end ObservedGraph

/-- Compile an executable rule side condition to its path form using the
proved (one-way) algorithm soundness theorem. -/
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
