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

/-! ## Constructive least-score witnesses

The first successful path need not be suitable for a later graph surgery.
For example, removing an activation/path intersection can replace an earlier
collider by a later collider without changing the number of colliders.  A
normalization proof therefore needs a path which minimizes a specified finite
score, not a caller-supplied assertion that the first witness is optimal.

The following search visits the same checked prefixes but retains the better
of their certified results.  Its score is an executable natural-number
function of the vertex list.  Nothing is selected from an existential proof:
the finite search returns the data, and the coverage invariant proves that
its result is at least as good as every simple active path.

Unlike the earlier first-success search, this search does not stop at the
first successful branch.  It can explore exponentially many prefixes.  Use it
only where a proof really needs a normal form; ordinary d-separation decisions and
ordinary witness extraction should keep their existing, cheaper APIs.
-/

/-- Keep a least-score candidate.  Ties keep the left result, making the
selection deterministic without imposing an order on proof-bearing paths. -/
private def preferLowerScore {α : Type _} (score : α -> Nat) : Option α -> Option α -> Option α
  | none, right => right
  | left, none => left
  | some left, some right => if score left ≤ score right then some left else some right

/-- A proof-only coverage invariant.  The selected object is still the
object returned by the executable option, not data extracted from this `Prop`. -/
private def ScoreCovers {α : Type _} (score : α -> Nat) (result : Option α) (candidate : α) : Prop :=
  Exists fun selected => result = some selected ∧ score selected ≤ score candidate

private theorem preferLowerScore_covers_left {α : Type _} (score : α -> Nat)
    (left right : Option α) (candidate : α) (covers : ScoreCovers score left candidate) :
    ScoreCovers score (preferLowerScore score left right) candidate := by
  rcases covers with ⟨selected, same, bound⟩
  rw [same]
  cases right with
  | none => exact ⟨selected, rfl, bound⟩
  | some other =>
      by_cases better : score selected ≤ score other
      · exact ⟨selected, by simp only [preferLowerScore, if_pos better], bound⟩
      · exact ⟨other, by simp only [preferLowerScore, if_neg better],
          Nat.le_trans (Nat.le_of_lt (Nat.lt_of_not_ge better)) bound⟩

private theorem preferLowerScore_covers_right {α : Type _} (score : α -> Nat)
    (left right : Option α) (candidate : α) (covers : ScoreCovers score right candidate) :
    ScoreCovers score (preferLowerScore score left right) candidate := by
  rcases covers with ⟨selected, same, bound⟩
  rw [same]
  cases left with
  | none => exact ⟨selected, rfl, bound⟩
  | some other =>
      by_cases better : score other ≤ score selected
      · exact ⟨other, by simp only [preferLowerScore, if_pos better], Nat.le_trans better bound⟩
      · exact ⟨selected, by simp only [preferLowerScore, if_neg better], bound⟩

/-- Fold over the finite branch list without constructing a list of all
successful paths.  Each branch can discard its inferior certified witnesses. -/
private def bestScoredResult? {α β : Type _} (score : β -> Nat) (branch : α -> Option β) :
    List α -> Option β
  | [] => none
  | head :: tail => preferLowerScore score (branch head) (bestScoredResult? score branch tail)

private theorem bestScoredResult?_covers {α β : Type _} (score : β -> Nat)
    (branch : α -> Option β) (nodes : List α) (node : α) (member : node ∈ nodes)
    (candidate : β) (covers : ScoreCovers score (branch node) candidate) :
    ScoreCovers score (bestScoredResult? score branch nodes) candidate := by
  induction nodes with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with same | later
      · subst node
        exact preferLowerScore_covers_left score _ _ candidate covers
      · exact preferLowerScore_covers_right score _ _ candidate
          (inductionHypothesis later)

/-- Decoding preserves the exact candidate list.  This equality is needed
for arbitrary list scores, not merely for existence of a decoded path. -/
private theorem decodeActivePath?_nodes (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (nodes : List (SeparationNode S)) (path : ActivePath G m conditioned source target)
    (decoded : decodeActivePath? G m conditioned source target nodes = some path) :
    path.nodes = nodes := by
  unfold decodeActivePath? at decoded
  split at decoded
  · cases decoded
    rfl
  · cases decoded

private theorem decodeActivePath?_covers (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat) (path : ActivePath G m conditioned source target) :
    ScoreCovers (fun candidate => score candidate.nodes)
      (decodeActivePath? G m conditioned source target path.nodes) path := by
  cases decoded : decodeActivePath? G m conditioned source target path.nodes with
  | none => exact False.elim (decodeActivePath?_ne_none G m conditioned source target path decoded)
  | some result =>
      refine ⟨result, rfl, ?_⟩
      change score result.nodes ≤ score path.nodes
      rw [decodeActivePath?_nodes G m conditioned source target path.nodes result decoded]
      exact Nat.le_refl _

/-- A simple active path cannot extend a prefix which already ends at its
target: its suffix would repeat that same target.  This permits stopping a
completed branch without discarding a better competing simple path. -/
private theorem activePath_suffix_nil_of_complete_prefix (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (path : ActivePath G m conditioned source target) (front suffix : List (SeparationNode S))
    (split : path.nodes = front ++ suffix) (complete : front.getLast? = some target) : suffix = [] := by
  cases suffix with
  | nil => rfl
  | cons head tail =>
      have simple : (front ++ head :: tail).Nodup := split ▸ path.simple
      have finishes : (front ++ head :: tail).getLast? = some target := split ▸ path.finishes
      have suffixFinishes := ObservedGraph.getLast?_suffix_append finishes
      exact False.elim ((List.nodup_append.mp simple).2.2 target
        (List.mem_of_getLast? complete) target (List.mem_of_getLast? suffixFinishes) rfl)

/-- A bounded exhaustive search which retains only a least-score witness.
Every extension still passes the original constructive prefix checker.
A completed branch stops: no simple target-ending path can extend it.
Other branches are still compared.  Fuel bounds recursion; simple-path
coverage supplies the finite global bound. -/
private def leastScoreActivePathSearchFrom? (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat) :
    Nat -> List (SeparationNode S) -> Option (ActivePath G m conditioned source target)
  | 0, front => decodeActivePath? G m conditioned source target front
  | remaining + 1, front =>
      match decodeActivePath? G m conditioned source target front with
      | some path => some path
      | none =>
          bestScoredResult? (fun candidate => score candidate.nodes) (fun next =>
            if PrefixChecked G m conditioned (front ++ [next]) then
              leastScoreActivePathSearchFrom? G m conditioned source target score remaining (front ++ [next])
            else none) G.separationNodes

/-- Every sufficiently short certified continuation is covered by the
search from its prefix.  Only the proof is inductive over the supplied path;
the returned data are generated by exploring the finite vertex alphabet. -/
private theorem leastScoreActivePathSearchFrom?_covers (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat) (path : ActivePath G m conditioned source target)
    (fuel : Nat) (front suffix : List (SeparationNode S))
    (split : path.nodes = front ++ suffix) (bound : suffix.length ≤ fuel) :
    ScoreCovers (fun candidate => score candidate.nodes)
      (leastScoreActivePathSearchFrom? G m conditioned source target score fuel front) path := by
  induction fuel generalizing front suffix with
  | zero =>
      cases suffix with
      | nil =>
          have same : path.nodes = front := by simpa only [List.append_nil] using split
          simpa only [leastScoreActivePathSearchFrom?, same] using
            decodeActivePath?_covers G m conditioned source target score path
      | cons next rest =>
          -- Refute the impossible arithmetic branch in `False` explicitly.
          -- Applying arithmetic contradiction directly to the existential
          -- coverage goal would invoke classical double-negation elimination.
          apply False.elim
          simp only [List.length_cons] at bound
          omega
  | succ fuel inductionHypothesis =>
      cases decoded : decodeActivePath? G m conditioned source target front with
      | some result =>
          have resultNodes := decodeActivePath?_nodes G m conditioned source target front result decoded
          have complete : front.getLast? = some target := resultNodes ▸ result.finishes
          have emptySuffix := activePath_suffix_nil_of_complete_prefix G m conditioned source target
            path front suffix split complete
          have same : path.nodes = front := by rw [emptySuffix, List.append_nil] at split; exact split
          refine ⟨result, ?_, ?_⟩
          · simp only [leastScoreActivePathSearchFrom?, decoded]
          · change score result.nodes ≤ score path.nodes
            rw [resultNodes, same]
            exact Nat.le_refl _
      | none =>
          cases suffix with
          | nil =>
              have same : path.nodes = front := by simpa only [List.append_nil] using split
              have found := decodeActivePath?_ne_none G m conditioned source target path
              rw [same] at found
              exact False.elim (found decoded)
          | cons next rest =>
              simp only [leastScoreActivePathSearchFrom?, decoded]
              apply bestScoredResult?_covers (fun candidate => score candidate.nodes) _ _ next
                (SeparationNode.mem_all next) path
              have checked := prefixChecked_of_activePath G m conditioned source target path front next rest split
              rw [if_pos checked]
              apply inductionHypothesis (front ++ [next]) rest
              · simpa only [List.append_assoc, List.singleton_append] using split
              · simp only [List.length_cons] at bound
                omega

/-- Return a certified active path of least score among all simple active
paths with the specified endpoints.  The list score is supplied as code,
not as a semantic decision oracle.  This is an exhaustive witness search,
not a replacement for the moral-graph separation algorithm. -/
def leastScoreActivePath? (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat) : Option (ActivePath G m conditioned source target) :=
  leastScoreActivePathSearchFrom? G m conditioned source target score G.separationNodes.length [source]

/-- The actual result's score is bounded by every certified competitor.
In particular a competitor rules out `none`, constructively and in `Prop`. -/
theorem leastScoreActivePath?_covers (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat) (path : ActivePath G m conditioned source target) :
    Exists fun selected => leastScoreActivePath? G m conditioned source target score = some selected ∧
      score selected.nodes ≤ score path.nodes := by
  rcases path.nodes_cons with ⟨tail, split⟩
  have lengthBound := nodup_length_le_of_subset
    SeparationNode.beq SeparationNode.beq_eq_true_iff path.nodes G.separationNodes
    path.simple (fun node _member => SeparationNode.mem_all node)
  apply leastScoreActivePathSearchFrom?_covers G m conditioned source target score path
    G.separationNodes.length [source] tail
  · simpa only [List.singleton_append] using split
  · rw [split, List.length_cons] at lengthBound
    omega

/-- An inhabited path type suffices to certify that the finite least-score
search succeeds.  The existence proof is eliminated only into a contradiction. -/
theorem leastScoreActivePath?_ne_none_of_nonempty (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat)
    (existsPath : Nonempty (ActivePath G m conditioned source target)) :
    leastScoreActivePath? G m conditioned source target score ≠ none := by
  rcases existsPath with ⟨path⟩
  rcases leastScoreActivePath?_covers G m conditioned source target score path with ⟨selected, same, _bound⟩
  intro exhausted
  rw [exhausted] at same
  cases same

/-- Produce least-score path data from certified existence without invoking
choice.  The data branch runs the finite search; the `none` branch is impossible. -/
def leastScoreActivePathOfNonempty (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat)
    (existsPath : Nonempty (ActivePath G m conditioned source target)) :
    ActivePath G m conditioned source target :=
  match found : leastScoreActivePath? G m conditioned source target score with
  | some path => path
  | none => False.elim (leastScoreActivePath?_ne_none_of_nonempty G m conditioned source target score existsPath found)

/-- Optimality is a theorem of the returned search data.  No minimality
certificate, readiness flag, or excluded-middle assumption is requested. -/
theorem leastScoreActivePathOfNonempty_minimal (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source target : SeparationNode S)
    (score : List (SeparationNode S) -> Nat)
    (existsPath : Nonempty (ActivePath G m conditioned source target))
    (competitor : ActivePath G m conditioned source target) :
    score (leastScoreActivePathOfNonempty G m conditioned source target score existsPath).nodes ≤
      score competitor.nodes := by
  unfold leastScoreActivePathOfNonempty
  split
  · rename_i selected found
    rcases leastScoreActivePath?_covers G m conditioned source target score competitor with ⟨other, same, bound⟩
    rw [found] at same
    cases same
    exact bound
  · rename_i exhausted
    exact False.elim
      (leastScoreActivePath?_ne_none_of_nonempty G m conditioned source target score existsPath exhausted)

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
