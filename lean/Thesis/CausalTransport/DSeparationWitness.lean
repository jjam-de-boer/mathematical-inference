import Thesis.CausalTransport.DSeparationCorrectness

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

/-!
# Constructive data witnesses for failed d-separation tests

The moral-graph correctness theorem proves existence of an active path in
`Prop`.  A countermodel construction needs more: an actual finite list of
vertices, with its adjacency and collider certificates, in `Type`.  Eliminating
`Nonempty` into such data would require a choice principle, so this module
does not perform that elimination.

Instead, a bounded, depth-first search checks candidate paths and returns the
first certified one.  Repeated vertices, missing edges, and inactive internal
triples are rejected as soon as they occur.  The search does not materialize
the list of all paths.  Every simple path has at most as many vertices as the
explicit-latent alphabet; that finite bound proves the search complete.
This witness search can still be exponential in the worst case.  Ordinary
separation decisions should continue to use the existing moral-graph test;
the additional search is for callers that need the actual path data.

The existing moral-graph theorem is used only to refute the `none` branch in
`Prop`.  The returned data always comes from the executable search itself.
In particular, neither propositional excluded middle nor a selection from an
existential proof is hidden in the witness constructor.
-/

namespace PathSpecification

/-! ## Finite, constructive checking of a candidate list -/

/-- Equality is decided by the already verified finite vertex code.  This
instance is private to the checker; it is not a classical equality instance. -/
private instance separationNodeDecidableEq : DecidableEq (SeparationNode S) :=
  fun left right =>
    if equal : SeparationNode.beq left right = true then
      isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
    else
      isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

private instance adjacentDecidable (G : ObservedGraph S) (m : GraphMutilation S)
    (left right : SeparationNode S) : Decidable (Adjacent G m left right) := by
  unfold Adjacent
  infer_instance

private def consecutiveDecidable {α : Type _} (relation : α -> α -> Prop)
    [DecidableRel relation] : (nodes : List α) -> Decidable (Consecutive relation nodes)
  | [] => isTrue True.intro
  | [_] => isTrue True.intro
  | left :: right :: rest => by
      letI := consecutiveDecidable relation (right :: rest)
      exact inferInstanceAs (Decidable (relation left right ∧ Consecutive relation (right :: rest)))

private instance consecutiveInstance {α : Type _} (relation : α -> α -> Prop)
    [DecidableRel relation] (nodes : List α) : Decidable (Consecutive relation nodes) :=
  consecutiveDecidable relation nodes

private instance tripleActiveDecidable (G : ObservedGraph S)
    (m : GraphMutilation S) (conditioned : NodeSet S)
    (previous middle next : SeparationNode S) :
    Decidable (TripleActive G m conditioned previous middle next) := by
  unfold TripleActive IsCollider ColliderActivated NonColliderOpen
  infer_instance

private def internalTriplesDecidable (G : ObservedGraph S)
    (m : GraphMutilation S) (conditioned : NodeSet S) :
    (nodes : List (SeparationNode S)) -> Decidable (InternalTriplesActive G m conditioned nodes)
  | [] => isTrue .nil
  | [node] => isTrue (.singleton node)
  | [left, right] => isTrue (.pair left right)
  | previous :: middle :: next :: rest => by
      letI := internalTriplesDecidable G m conditioned (middle :: next :: rest)
      exact decidable_of_iff
        (TripleActive G m conditioned previous middle next ∧
          InternalTriplesActive G m conditioned (middle :: next :: rest))
        ⟨fun checked => .step checked.1 checked.2, fun active => by
          cases active with
          | step triple tail => exact ⟨triple, tail⟩⟩

private instance internalTriplesInstance (G : ObservedGraph S)
    (m : GraphMutilation S) (conditioned : NodeSet S)
    (nodes : List (SeparationNode S)) : Decidable (InternalTriplesActive G m conditioned nodes) :=
  internalTriplesDecidable G m conditioned nodes

/-- Every condition that can already be checked on an unfinished prefix.
Endpoint openness is checked by the decoder, not imposed on internal colliders. -/
private def PrefixChecked (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (nodes : List (SeparationNode S)) : Prop :=
  nodes.Nodup ∧ Consecutive (Adjacent G m) nodes ∧ InternalTriplesActive G m conditioned nodes

private instance prefixCheckedDecidable (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (nodes : List (SeparationNode S)) :
    Decidable (PrefixChecked G m conditioned nodes) := by
  unfold PrefixChecked
  infer_instance

private def CandidateChecked (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (nodes : List (SeparationNode S)) : Prop :=
  nodes.head? = some source ∧ nodes.getLast? = some target ∧
    PrefixChecked G m conditioned nodes ∧
    ObservedGraph.blockedBy conditioned source = false ∧
    ObservedGraph.blockedBy conditioned target = false

private instance candidateCheckedDecidable (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (nodes : List (SeparationNode S)) :
    Decidable (CandidateChecked G m conditioned source target nodes) := by
  unfold CandidateChecked
  infer_instance

/-- Decode only a completely checked list.  Proof fields certify the exact
returned list, rather than an independently asserted existence of a path. -/
private def decodeActivePath? (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (nodes : List (SeparationNode S)) : Option (ActivePath G m conditioned source target) :=
  if checked : CandidateChecked G m conditioned source target nodes then
    some {
      nodes := nodes
      starts := checked.1
      finishes := checked.2.1
      simple := checked.2.2.1.1
      adjacent := checked.2.2.1.2.1
      internal_active := checked.2.2.1.2.2
      source_open := checked.2.2.2.1
      target_open := checked.2.2.2.2
    }
  else none

private theorem decodeActivePath?_ne_none (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (path : ActivePath G m conditioned source target) :
    decodeActivePath? G m conditioned source target path.nodes ≠ none := by
  have checked : CandidateChecked G m conditioned source target path.nodes :=
    ⟨path.starts, path.finishes, ⟨path.simple, path.adjacent, path.internal_active⟩,
      path.source_open, path.target_open⟩
  simp only [decodeActivePath?, dif_pos checked, ne_eq, reduceCtorEq, not_false_eq_true]

/-! ## Bounded depth-first search and its completeness invariant -/

/-- Try the current prefix before extending it.  The structural fuel counts
additional vertices, and `findSome?` stops on the first successful branch.
Invalid prefixes are never extended: a future suffix cannot repair a repeated
vertex, a missing adjacency, or an already inactive internal triple. -/
private def activePathSearchFrom? (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S) :
    Nat -> List (SeparationNode S) -> Option (ActivePath G m conditioned source target)
  | fuel, front =>
      match decodeActivePath? G m conditioned source target front with
      | some path => some path
      | none =>
          match fuel with
          | 0 => none
          | remaining + 1 =>
              G.separationNodes.findSome? (fun next =>
                if PrefixChecked G m conditioned (front ++ [next]) then
                  activePathSearchFrom? G m conditioned source target remaining (front ++ [next])
                else none)

/-- Every nonempty prefix of an active path passes the pruning checks.  This
is the key reason pruning cannot discard a valid witness. -/
private theorem prefixChecked_of_activePath (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (path : ActivePath G m conditioned source target)
    (before : List (SeparationNode S)) (node : SeparationNode S)
    (after : List (SeparationNode S)) (split : path.nodes = before ++ node :: after) :
    PrefixChecked G m conditioned (before ++ [node]) := by
  have simple : ((before ++ [node]) ++ after).Nodup := by
    simpa only [List.append_assoc, List.singleton_append] using split ▸ path.simple
  refine ⟨(List.nodup_append.mp simple).1,
    Consecutive.prefix_append before node after (split ▸ path.adjacent), ?_⟩
  have active := path.internal_active.take (before ++ [node]).length
  have same : path.nodes = (before ++ [node]) ++ after := by
    simpa only [List.append_assoc, List.singleton_append] using split
  rw [same, List.take_left] at active
  exact active

/-- A certified continuation of length at most `fuel` rules out failure of
the search from its prefix.  The witness used in this proof is only a proof
argument; the search is still responsible for producing the eventual data. -/
private theorem activePathSearchFrom?_ne_none (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (path : ActivePath G m conditioned source target) (fuel : Nat)
    (front suffix : List (SeparationNode S))
    (split : path.nodes = front ++ suffix) (bound : suffix.length ≤ fuel) :
    activePathSearchFrom? G m conditioned source target fuel front ≠ none := by
  induction fuel generalizing front suffix with
  | zero =>
      cases suffix with
      | nil =>
          have same : path.nodes = front := by simpa only [List.append_nil] using split
          have found := decodeActivePath?_ne_none G m conditioned source target path
          rw [same] at found
          cases decoded : decodeActivePath? G m conditioned source target front with
          | none => exact False.elim (found decoded)
          | some result => simp only [activePathSearchFrom?, decoded, ne_eq, reduceCtorEq,
              not_false_eq_true]
      | cons next rest => simp only [List.length_cons] at bound; omega
  | succ fuel inductionHypothesis =>
      cases decoded : decodeActivePath? G m conditioned source target front with
      | some result => simp only [activePathSearchFrom?, decoded, ne_eq, reduceCtorEq,
          not_false_eq_true]
      | none =>
          cases suffix with
          | nil =>
              have same : path.nodes = front := by simpa only [List.append_nil] using split
              have found := decodeActivePath?_ne_none G m conditioned source target path
              rw [same] at found
              exact False.elim (found decoded)
          | cons next rest =>
              intro exhausted
              have nextMember : next ∈ G.separationNodes := SeparationNode.mem_all next
              have noneAtNext := (List.findSome?_eq_none_iff.mp
                (show G.separationNodes.findSome? (fun next =>
                  if PrefixChecked G m conditioned (front ++ [next]) then
                    activePathSearchFrom? G m conditioned source target fuel (front ++ [next])
                  else none) = none by
                    simpa only [activePathSearchFrom?, decoded] using exhausted)) next nextMember
              have checked := prefixChecked_of_activePath G m conditioned source target
                path front next rest split
              rw [if_pos checked] at noneAtNext
              apply inductionHypothesis (front ++ [next]) rest
              · simpa only [List.append_assoc, List.singleton_append] using split
              · simp only [List.length_cons] at bound
                omega
              · exact noneAtNext

/-- Search for an actual active path between two specified expanded vertices.
The explicit-latent alphabet gives a sufficient bound for every simple path,
including singleton paths when the two open endpoints coincide. -/
def activePath? (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S) :
    Option (ActivePath G m conditioned source target) :=
  activePathSearchFrom? G m conditioned source target G.separationNodes.length [source]

/-- Existence is sufficient to prove that the executable search succeeds;
it is not sufficient to select its result without running that search. -/
theorem activePath?_ne_none_of_nonempty (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (existsPath : Nonempty (ActivePath G m conditioned source target)) :
    activePath? G m conditioned source target ≠ none := by
  rcases existsPath with ⟨path⟩
  rcases path.nodes_cons with ⟨tail, split⟩
  have lengthBound := nodup_length_le_of_subset
    SeparationNode.beq SeparationNode.beq_eq_true_iff path.nodes G.separationNodes
    path.simple (fun node _member => SeparationNode.mem_all node)
  apply activePathSearchFrom?_ne_none G m conditioned source target path
    G.separationNodes.length [source] tail
  · simpa only [List.singleton_append] using split
  · rw [split, List.length_cons] at lengthBound
    omega

/-! ## Selecting observed endpoints and returning the certified data -/

/-- An active connection retains both selected observed endpoints and the
whole expanded path.  Latent-pair vertices remain visible in `path.nodes`;
they are not collapsed into an unproved observed-edge shorthand. -/
structure ActiveConnection (G : ObservedGraph S) (m : GraphMutilation S)
    (left right conditioned : NodeSet S) : Type where
  source : Fin S.count
  target : Fin S.count
  source_selected : left source = true
  target_selected : right target = true
  path : ActivePath G m conditioned (.observed source) (.observed target)

/-- Search only the two finite selected endpoint families.  The Boolean
guards retain selection proofs in the returned dependent record. -/
def activeConnection? (G : ObservedGraph S) (m : GraphMutilation S)
    (left right conditioned : NodeSet S) : Option (ActiveConnection G m left right conditioned) :=
  (NodeSet.members left).findSome? (fun source =>
    if sourceSelected : left source = true then
      (NodeSet.members right).findSome? (fun target =>
        if targetSelected : right target = true then
          (activePath? G m conditioned (.observed source) (.observed target)).map (fun path => {
            source := source
            target := target
            source_selected := sourceSelected
            target_selected := targetSelected
            path := path
          })
        else none)
    else none)

/-- A propositional active-path existence proof can refute search failure.
Elimination of that proof stays in `Prop`, where it is constructive. -/
private theorem activeConnection?_ne_none_of_exists (G : ObservedGraph S)
    (m : GraphMutilation S) (left right conditioned : NodeSet S)
    (existsPath : Exists fun source : Fin S.count => Exists fun target : Fin S.count =>
      left source = true ∧ right target = true ∧
        Nonempty (ActivePath G m conditioned (.observed source) (.observed target))) :
    activeConnection? G m left right conditioned ≠ none := by
  rcases existsPath with ⟨source, target, sourceSelected, targetSelected, path⟩
  intro exhausted
  have noneAtSource := (List.findSome?_eq_none_iff.mp exhausted) source
    ((NodeSet.mem_members_iff left source).mpr sourceSelected)
  rw [dif_pos sourceSelected] at noneAtSource
  have noneAtTarget := (List.findSome?_eq_none_iff.mp noneAtSource) target
    ((NodeSet.mem_members_iff right target).mpr targetSelected)
  rw [dif_pos targetSelected] at noneAtTarget
  exact activePath?_ne_none_of_nonempty G m conditioned (.observed source) (.observed target)
    path (Option.map_eq_none_iff.mp noneAtTarget)

/-- Read a failed Boolean separation test positively: its finite `any`
search found open endpoints and a moral connection.  The proof does not
replace `¬¬ ∃ path` by `∃ path`, which would be an invalid constructive step. -/
theorem exists_activePath_of_dSeparated_false (G : ObservedGraph S)
    (m : GraphMutilation S) (left right conditioned : NodeSet S)
    (dependent : G.dSeparated m left right conditioned = false) :
    Exists fun source : Fin S.count => Exists fun target : Fin S.count =>
      left source = true ∧ right target = true ∧
        Nonempty (ActivePath G m conditioned (.observed source) (.observed target)) := by
  have found : (List.ofFn (fun i : Fin S.count => i)).any (fun source =>
      left source && !(conditioned source) &&
        (List.ofFn (fun i : Fin S.count => i)).any (fun target =>
          right target && !(conditioned target) &&
            G.moralReachable m (NodeSet.union left (NodeSet.union right conditioned))
              conditioned (.observed source) (.observed target))) = true := by
    simpa only [ObservedGraph.dSeparated, Bool.not_eq_false'] using dependent
  rcases List.any_eq_true.mp found with ⟨source, _sourceMember, sourceHolds⟩
  rcases Bool.and_eq_true_iff.mp sourceHolds with ⟨sourceAndOpen, targetExists⟩
  rcases Bool.and_eq_true_iff.mp sourceAndOpen with ⟨sourceSelected, sourceOpen⟩
  rcases List.any_eq_true.mp targetExists with ⟨target, _targetMember, targetHolds⟩
  rcases Bool.and_eq_true_iff.mp targetHolds with ⟨targetAndOpen, reachable⟩
  rcases Bool.and_eq_true_iff.mp targetAndOpen with ⟨targetSelected, targetOpen⟩
  exact G.exists_activePath_of_moralReachable m left right conditioned
    sourceSelected targetSelected
    (by simpa only [ObservedGraph.blockedBy, Bool.not_eq_true'] using sourceOpen)
    (by simpa only [ObservedGraph.blockedBy, Bool.not_eq_true'] using targetOpen) reachable

/-- Every negative separation answer has a successful data-witness search. -/
theorem activeConnection?_ne_none_of_dSeparated_false (G : ObservedGraph S)
    (m : GraphMutilation S) (left right conditioned : NodeSet S)
    (dependent : G.dSeparated m left right conditioned = false) :
    activeConnection? G m left right conditioned ≠ none :=
  activeConnection?_ne_none_of_exists G m left right conditioned
    (exists_activePath_of_dSeparated_false G m left right conditioned dependent)

/-- The data search fails exactly when the existing moral-graph decision
procedure reports separation.  Thus the new witness API uses the same path
semantics as the public graph test, rather than a stronger path criterion. -/
theorem activeConnection?_eq_none_iff_dSeparated (G : ObservedGraph S)
    (m : GraphMutilation S) (left right conditioned : NodeSet S) :
    activeConnection? G m left right conditioned = none ↔
      G.dSeparated m left right conditioned = true := by
  constructor
  · intro exhausted
    cases result : G.dSeparated m left right conditioned with
    | true => rfl
    | false =>
        exact False.elim
          (activeConnection?_ne_none_of_dSeparated_false G m left right conditioned result exhausted)
  · intro separated
    cases found : activeConnection? G m left right conditioned with
    | none => rfl
    | some connection =>
        exact False.elim ((G.dSeparated_implies_pathDSeparated m left right conditioned separated)
          ⟨connection.source, connection.target, connection.source_selected,
            connection.target_selected, ⟨connection.path⟩⟩)

/-- Return an actual path from a negative separation answer.  The `some`
branch supplies all data; the `none` branch is eliminated by search
completeness.  No inhabitant is selected from a `Nonempty` proposition. -/
def activeConnectionOfDSeparatedFalse (G : ObservedGraph S)
    (m : GraphMutilation S) (left right conditioned : NodeSet S)
    (dependent : G.dSeparated m left right conditioned = false) :
    ActiveConnection G m left right conditioned :=
  match found : activeConnection? G m left right conditioned with
  | some connection => connection
  | none => False.elim
      (activeConnection?_ne_none_of_dSeparated_false G m left right conditioned dependent found)

end PathSpecification

end Causality
end Thesis
