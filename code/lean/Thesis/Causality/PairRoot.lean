import Thesis.Causality.Reductions

namespace Thesis
namespace Causality

/-!
# Canonical pair-root expansion

The construction of `prop:pair-root-expansion` is graph-only.  From a finite
observed directed-and-bidirected graph it introduces one hidden root for every
ordered bidirected pair `(i, j)` with `i.val < j.val`, and it gives that root
precisely the two outgoing arrows `Uᵢⱼ → i` and `Uᵢⱼ → j`.  The directed
observed arrows are retained.

Two packages are produced:

* `pairRootExtension` is a `LatentExtension` whose projected bidirected
  classifier recovers the original one;
* `pairRootHiddenDAG` / `pairRootProjection` is the corresponding all-directed
  hidden DAG, with observed nodes embedded after the introduced roots, whose
  hidden-internal projection recovers both the directed and the bidirected
  classifiers.

No probability assignment and no structural mechanism are supplied.  The dummy
latent value type is `Unit`.  The construction therefore does not inhabit
`PublishedLatentProjection` and does not produce a `FiniteLatentSCM`.
-/

variable {S : ObservedSignature}

/-- An ordered bidirected pair is a bidirected edge written with increasing rank. -/
def isOrderedBidirected (G : ObservedGraph S)
    (i j : Fin S.count) : Bool :=
  decide (i.val < j.val) && G.bidirected i j

/-- The exhaustive finite enumeration of observed node pairs, in rank order. -/
def allObservedPairs (S : ObservedSignature) :
    List (Fin S.count × Fin S.count) :=
  (List.finRange S.count).flatMap fun i =>
    (List.finRange S.count).map fun j => (i, j)

/--
The canonical pair-root list: one entry for every bidirected edge, written
so that the first endpoint has strictly smaller rank.  Symmetry of the
bidirected classifier makes the ordered membership test exhaustive.
-/
def pairRoots (G : ObservedGraph S) : List (Fin S.count × Fin S.count) :=
  (allObservedPairs S).filter fun pair =>
    isOrderedBidirected G pair.1 pair.2

theorem mem_finRange_self {n : Nat} (i : Fin n) :
    i ∈ List.finRange n :=
  List.mem_finRange i

theorem mem_allObservedPairs (S : ObservedSignature)
    (i j : Fin S.count) :
    (i, j) ∈ allObservedPairs S := by
  refine List.mem_flatMap.mpr ?_
  refine ⟨i, mem_finRange_self i, ?_⟩
  exact List.mem_map.mpr ⟨j, mem_finRange_self j, rfl⟩

/-- Membership in the pair-root list is exactly the ordered-bidirected test. -/
theorem mem_pairRoots (G : ObservedGraph S) (i j : Fin S.count) :
    (i, j) ∈ pairRoots G ↔
      i.val < j.val ∧ G.bidirected i j = true := by
  constructor
  · intro hmem
    have hfilter := (List.mem_filter.mp hmem).2
    simp [isOrderedBidirected, Bool.and_eq_true] at hfilter
    exact hfilter
  · intro h
    refine List.mem_filter.mpr ?_
    refine ⟨mem_allObservedPairs S i j, ?_⟩
    simp [isOrderedBidirected, h.1, h.2]

/-- The number of introduced hidden roots. -/
def pairRootCount (G : ObservedGraph S) : Nat :=
  (pairRoots G).length

/-- The unique root introduced for an ordered bidirected pair. -/
def pairRootOf (G : ObservedGraph S) {i j : Fin S.count}
    (hord : i.val < j.val) (hedge : G.bidirected i j = true) :
    Fin (pairRootCount G) :=
  ⟨(pairRoots G).idxOf (i, j),
    List.idxOf_lt_length_of_mem ((mem_pairRoots G i j).mpr ⟨hord, hedge⟩)⟩

theorem pairRoots_get_of (G : ObservedGraph S) {i j : Fin S.count}
    (hord : i.val < j.val) (hedge : G.bidirected i j = true) :
    (pairRoots G).get (pairRootOf G hord hedge) = (i, j) := by
  have hmem : (i, j) ∈ pairRoots G :=
    (mem_pairRoots G i j).mpr ⟨hord, hedge⟩
  apply beq_iff_eq.mp
  change ((pairRoots G).get (pairRootOf G hord hedge) == (i, j)) = true
  simpa [List.get_eq_getElem, pairRootOf, List.idxOf] using
    (List.findIdx_getElem
      (p := fun value => value == (i, j))
      (xs := pairRoots G)
      (w := List.idxOf_lt_length_of_mem hmem))

/-- A pair-root is incident exactly to its two recorded endpoints. -/
def pairRootIncident (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) (node : Fin S.count) : Bool :=
  let pair := (pairRoots G).get root
  decide (node = pair.1) || decide (node = pair.2)

theorem pairRootIncident_iff (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) (node : Fin S.count) :
    pairRootIncident G root node = true ↔
      node = ((pairRoots G).get root).1 ∨
        node = ((pairRoots G).get root).2 := by
  simp [pairRootIncident, Bool.or_eq_true]

theorem pairRoots_get_mem (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    (pairRoots G).get root ∈ pairRoots G :=
  List.get_mem (pairRoots G) root

theorem pairRoots_get_spec (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    ((pairRoots G).get root).1.val < ((pairRoots G).get root).2.val ∧
      G.bidirected ((pairRoots G).get root).1 ((pairRoots G).get root).2 =
        true :=
  (mem_pairRoots G _ _).mp (pairRoots_get_mem G root)

theorem pairRootIncident_of (G : ObservedGraph S) {i j : Fin S.count}
    (hord : i.val < j.val) (hedge : G.bidirected i j = true) :
    pairRootIncident G (pairRootOf G hord hedge) i = true ∧
      pairRootIncident G (pairRootOf G hord hedge) j = true := by
  have hget := pairRoots_get_of G hord hedge
  constructor
  · exact (pairRootIncident_iff G _ i).mpr (Or.inl (by rw [hget]))
  · exact (pairRootIncident_iff G _ j).mpr (Or.inr (by rw [hget]))

/-- A bidirected edge cannot join a vertex to itself. -/
theorem val_ne_of_bidirected (G : ObservedGraph S) {i j : Fin S.count}
    (edge : G.bidirected i j = true) : i.val ≠ j.val := by
  intro equal
  have same : i = j := Fin.ext equal
  subst same
  rw [G.bidirected_irreflexive] at edge
  exact Bool.false_ne_true edge

/--
The canonical pair-root of an unoriented bidirected edge.

`pairRootOf` expects its endpoints in increasing rank order.  This wrapper
performs that finite comparison and reverses the edge when necessary.  It is
data in `Type`, so later parity constructions can name the root of a path edge
without eliminating an existential witness or invoking choice.
-/
def pairRootBetween (G : ObservedGraph S) {i j : Fin S.count}
    (edge : G.bidirected i j = true) : Fin (pairRootCount G) :=
  if ordered : i.val < j.val then
    pairRootOf G ordered edge
  else
    have reverseOrdered : j.val < i.val := by
      rcases Nat.lt_or_gt_of_ne (val_ne_of_bidirected G edge) with
        forward | reverse
      · exact False.elim (ordered forward)
      · exact reverse
    pairRootOf G reverseOrdered (G.bidirected_symmetric edge)

/-- The root selected for an unoriented edge is incident to its left endpoint. -/
theorem pairRootIncident_between_left
    (G : ObservedGraph S) {i j : Fin S.count}
    (edge : G.bidirected i j = true) :
    pairRootIncident G (pairRootBetween G edge) i = true := by
  unfold pairRootBetween
  split
  · next ordered =>
      exact (pairRootIncident_of G ordered edge).1
  · next notOrdered =>
      have reverseOrdered : j.val < i.val := by
        rcases Nat.lt_or_gt_of_ne (val_ne_of_bidirected G edge) with
          forward | reverse
        · exact False.elim (notOrdered forward)
        · exact reverse
      exact (pairRootIncident_of G reverseOrdered
        (G.bidirected_symmetric edge)).2

/-- The root selected for an unoriented edge is incident to its right endpoint. -/
theorem pairRootIncident_between_right
    (G : ObservedGraph S) {i j : Fin S.count}
    (edge : G.bidirected i j = true) :
    pairRootIncident G (pairRootBetween G edge) j = true := by
  unfold pairRootBetween
  split
  · next ordered =>
      exact (pairRootIncident_of G ordered edge).2
  · next notOrdered =>
      have reverseOrdered : j.val < i.val := by
        rcases Nat.lt_or_gt_of_ne (val_ne_of_bidirected G edge) with
          forward | reverse
        · exact False.elim (notOrdered forward)
        · exact reverse
      exact (pairRootIncident_of G reverseOrdered
        (G.bidirected_symmetric edge)).1

/-- The unoriented edge root is incident exactly to the edge's two endpoints. -/
theorem pairRootIncident_between
    (G : ObservedGraph S) {i j : Fin S.count}
    (edge : G.bidirected i j = true) (node : Fin S.count) :
    pairRootIncident G (pairRootBetween G edge) node =
      (decide (node = i) || decide (node = j)) := by
  unfold pairRootBetween
  split
  · next ordered =>
      rw [pairRootIncident, pairRoots_get_of G ordered edge]
  · next notOrdered =>
      have reverseOrdered : j.val < i.val := by
        rcases Nat.lt_or_gt_of_ne (val_ne_of_bidirected G edge) with
          forward | reverse
        · exact False.elim (notOrdered forward)
        · exact reverse
      rw [pairRootIncident,
        pairRoots_get_of G reverseOrdered (G.bidirected_symmetric edge)]
      simp [Bool.or_comm]

/--
The graph-only latent extension.  Each introduced root has dummy value type
`Unit`; the only structural data are the two incidence bits.
-/
def pairRootExtension (G : ObservedGraph S) : LatentExtension S where
  count := pairRootCount G
  Value := fun _ => Unit
  valueEnumeration := fun _ => [()]
  value_complete := fun _ u => by
    cases u
    simp
  valueDecidableEq := fun _ => inferInstance
  incident := pairRootIncident G

theorem pairRootExtension_incident (G : ObservedGraph S) :
    (pairRootExtension G).incident = pairRootIncident G :=
  rfl

private theorem val_ne_of_beq_false {n : Nat} {i j : Fin n}
    (h : Nat.beq i.val j.val = false) : i ≠ j := by
  intro equal
  cases equal
  simp at h

private theorem lt_or_gt_of_val_ne {n : Nat} {i j : Fin n}
    (h : i.val ≠ j.val) : i.val < j.val ∨ j.val < i.val :=
  Nat.lt_or_gt_of_ne h

/--
Hiding the introduced pair-roots recovers the original bidirected classifier.
The two directions are the two paragraphs of the prose argument: every
bidirected edge is witnessed by its ordered root, and every projected
bidirected edge comes from such a root and therefore from an original edge.
-/
theorem pairRootExtension_projected (G : ObservedGraph S)
    (i j : Fin S.count) :
    (pairRootExtension G).projectedBidirected i j = G.bidirected i j := by
  unfold LatentExtension.projectedBidirected pairRootExtension
  cases hbeq : Nat.beq i.val j.val with
  | true =>
      have hij : i = j := by
        apply Fin.ext
        exact Nat.eq_of_beq_eq_true hbeq
      cases hij
      simp [G.bidirected_irreflexive i]
  | false =>
      have hne : i ≠ j := val_ne_of_beq_false hbeq
      have hvalne : i.val ≠ j.val := fun h => hne (Fin.ext h)
      cases hedge : G.bidirected i j with
      | true =>
          have hany :
              finAny (pairRootCount G)
                  (fun latent =>
                    pairRootIncident G latent i &&
                      pairRootIncident G latent j) = true := by
            rcases lt_or_gt_of_val_ne hvalne with hlt | hgt
            · have hinc := pairRootIncident_of G hlt hedge
              exact finAny_eq_true_of _
                (pairRootOf G hlt hedge)
                (by simp [hinc.1, hinc.2])
            · have hedge' : G.bidirected j i = true :=
                G.bidirected_symmetric hedge
              have hinc := pairRootIncident_of G hgt hedge'
              exact finAny_eq_true_of _
                (pairRootOf G hgt hedge')
                (by simp [hinc.1, hinc.2])
          simp [hany]
      | false =>
          have hany :
              finAny (pairRootCount G)
                  (fun latent =>
                    pairRootIncident G latent i &&
                      pairRootIncident G latent j) = false := by
            apply (finAny_eq_false_iff _).mpr
            intro latent
            cases hinc :
                pairRootIncident G latent i &&
                  pairRootIncident G latent j with
            | false => rfl
            | true =>
                have hparts := Bool.and_eq_true_iff.mp hinc
                have hi := (pairRootIncident_iff G latent i).mp hparts.1
                have hj := (pairRootIncident_iff G latent j).mp hparts.2
                have hspec := pairRoots_get_spec G latent
                let pair := (pairRoots G).get latent
                have hpair : G.bidirected pair.1 pair.2 = true := hspec.2
                have hcases :
                    (i = pair.1 ∧ j = pair.2) ∨
                      (i = pair.2 ∧ j = pair.1) := by
                  rcases hi with hi | hi <;> rcases hj with hj | hj
                  · exact False.elim (hne (hi.trans hj.symm))
                  · exact Or.inl ⟨hi, hj⟩
                  · exact Or.inr ⟨hi, hj⟩
                  · exact False.elim (hne (hi.trans hj.symm))
                cases hcases with
                | inl h =>
                    have : G.bidirected i j = true := by
                      simpa [h.1, h.2] using hpair
                    simp [hedge] at this
                | inr h =>
                    have : G.bidirected i j = true := by
                      simpa [h.1, h.2] using
                        G.bidirected_symmetric hpair
                    simp [hedge] at this
          simp [hany]

/--
Each introduced root has at most two observed children, namely its two
recorded endpoints.  The expansion is therefore canonically semi-Markovian.
-/
theorem pairRootExtension_canonical (G : ObservedGraph S) :
    (pairRootExtension G).CanonicalSemiMarkovian := by
  intro latent i j k hi hj hk
  have hi' := (pairRootIncident_iff G latent i).mp hi
  have hj' := (pairRootIncident_iff G latent j).mp hj
  have hk' := (pairRootIncident_iff G latent k).mp hk
  rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;>
    rcases hk' with hk' | hk'
  · exact Or.inl (hi'.trans hj'.symm)
  · exact Or.inl (hi'.trans hj'.symm)
  · exact Or.inr (Or.inl (hi'.trans hk'.symm))
  · exact Or.inr (Or.inr (hj'.trans hk'.symm))
  · exact Or.inr (Or.inr (hj'.trans hk'.symm))
  · exact Or.inr (Or.inl (hi'.trans hk'.symm))
  · exact Or.inl (hi'.trans hj'.symm)
  · exact Or.inl (hi'.trans hj'.symm)

/-- Embed a pair-root before every observed node. -/
def pairRootHiddenNode (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    Fin (pairRootCount G + S.count) :=
  root.castAdd S.count

/-- Embed an observed node after every introduced pair-root. -/
def pairRootObservedNode (G : ObservedGraph S)
    (node : Fin S.count) :
    Fin (pairRootCount G + S.count) :=
  node.natAdd (pairRootCount G)

/--
The all-directed edge classifier of the expanded graph: pair-roots point to
their two endpoints, and observed arrows are the original directed classifier.
There are no arrows into pair-roots.
-/
def pairRootHiddenEdge (G : ObservedGraph S)
    (src tgt : Fin (pairRootCount G + S.count)) : Bool :=
  if hsrc : src.val < pairRootCount G then
    if htgt : pairRootCount G ≤ tgt.val then
      pairRootIncident G
        ⟨src.val, hsrc⟩
        ⟨tgt.val - pairRootCount G,
          Nat.sub_lt_left_of_lt_add htgt tgt.isLt⟩
    else
      false
  else if hsrcObs : pairRootCount G ≤ src.val then
    if htgt : pairRootCount G ≤ tgt.val then
      S.directed
        ⟨src.val - pairRootCount G,
          Nat.sub_lt_left_of_lt_add hsrcObs src.isLt⟩
        ⟨tgt.val - pairRootCount G,
          Nat.sub_lt_left_of_lt_add htgt tgt.isLt⟩
    else
      false
  else
    false

theorem pairRootObservedNode_val (G : ObservedGraph S)
    (node : Fin S.count) :
    (pairRootObservedNode G node).val = pairRootCount G + node.val :=
  rfl

theorem pairRootHiddenNode_val (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    (pairRootHiddenNode G root).val = root.val :=
  rfl

theorem pairRootHidden_observed_edge (G : ObservedGraph S)
    (i j : Fin S.count) :
    pairRootHiddenEdge G
        (pairRootObservedNode G i) (pairRootObservedNode G j) =
      S.directed i j := by
  have hsrc :
      ¬ ((pairRootObservedNode G i).val < pairRootCount G) := by
    simp [pairRootObservedNode]
  have hsrcObs :
      pairRootCount G ≤ (pairRootObservedNode G i).val := by
    simp [pairRootObservedNode]
  have htgt :
      pairRootCount G ≤ (pairRootObservedNode G j).val := by
    simp [pairRootObservedNode]
  simp [pairRootHiddenEdge, hsrc, hsrcObs, htgt]
  congr 1
  · apply Fin.ext
    simp [pairRootObservedNode]
  · apply Fin.ext
    simp [pairRootObservedNode]

theorem pairRootHidden_root_edge (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) (node : Fin S.count) :
    pairRootHiddenEdge G
        (pairRootHiddenNode G root) (pairRootObservedNode G node) =
      pairRootIncident G root node := by
  have hsrc : (pairRootHiddenNode G root).val < pairRootCount G := by
    simp [pairRootHiddenNode]
  have htgt :
      pairRootCount G ≤ (pairRootObservedNode G node).val := by
    simp [pairRootObservedNode]
  simp [pairRootHiddenEdge, hsrc, htgt]
  apply congrArg (pairRootIncident G root)
  apply Fin.ext
  simp [pairRootObservedNode]

theorem pairRootHidden_no_to_hidden (G : ObservedGraph S)
    (src : Fin (pairRootCount G + S.count))
    (root : Fin (pairRootCount G)) :
    pairRootHiddenEdge G src (pairRootHiddenNode G root) = false := by
  have htgt :
      ¬ (pairRootCount G ≤ (pairRootHiddenNode G root).val) := by
    simp [pairRootHiddenNode]
  simp [pairRootHiddenEdge, htgt]

/--
The expanded all-directed graph.  Pair-roots occupy the initial ranks; observed
nodes keep their relative topological order.  Every expanded edge therefore
strictly increases rank.
-/
def pairRootHiddenDAG (G : ObservedGraph S) : FiniteHiddenDAG S where
  count := pairRootCount G + S.count
  observedNode := pairRootObservedNode G
  observedNode_injective := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    simp [pairRootObservedNode] at hval
    omega
  hidden := fun node => decide (node.val < pairRootCount G)
  observed_not_hidden := by
    intro i
    simp [pairRootObservedNode]
  node_classified := by
    intro node
    by_cases h : node.val < pairRootCount G
    · exact Or.inl (decide_eq_true_eq.mpr h)
    · refine Or.inr ⟨⟨node.val - pairRootCount G, by omega⟩, ?_⟩
      apply Fin.ext
      simp [pairRootObservedNode]
      exact Nat.add_sub_of_le (Nat.le_of_not_lt h)
  edge := pairRootHiddenEdge G
  rank := fun node => node.val
  edge_rank_lt := by
    intro i j hedge
    unfold pairRootHiddenEdge at hedge
    split at hedge
    · next hsrc =>
        split at hedge
        · next htgt =>
            exact Nat.lt_of_lt_of_le hsrc htgt
        · simp at hedge
    · next hsrc =>
        split at hedge
        · next hsrcObs =>
            split at hedge
            · next htgt =>
                have hdir :
                    S.directed
                        ⟨i.val - pairRootCount G,
                          Nat.sub_lt_left_of_lt_add hsrcObs i.isLt⟩
                        ⟨j.val - pairRootCount G,
                          Nat.sub_lt_left_of_lt_add htgt j.isLt⟩ = true :=
                  hedge
                have hlt := S.directed_earlier hdir
                have hi :
                    i.val = pairRootCount G +
                      (i.val - pairRootCount G) :=
                  (Nat.add_sub_of_le hsrcObs).symm
                have hj :
                    j.val = pairRootCount G +
                      (j.val - pairRootCount G) :=
                  (Nat.add_sub_of_le htgt).symm
                have hlt' :
                    i.val - pairRootCount G <
                      j.val - pairRootCount G := hlt
                rw [hi, hj]
                exact Nat.add_lt_add_left hlt' _
            · simp at hedge
        · simp at hedge

theorem pairRootHiddenDAG_hidden_iff (G : ObservedGraph S)
    (node : Fin (pairRootCount G + S.count)) :
    (pairRootHiddenDAG G).hidden node = true ↔
      node.val < pairRootCount G := by
  simp [pairRootHiddenDAG]

/--
A hidden-internal path that begins at an observed node can never reach a
hidden node: there are no arrows into pair-roots.  Consequently the only
observed-to-observed hidden-internal paths are the original directed edges.
-/
theorem not_hidden_of_path_from_observed (G : ObservedGraph S)
    {i : Fin S.count}
    {node : Fin (pairRootHiddenDAG G).count}
    (path : (pairRootHiddenDAG G).HiddenInternalPath
      ((pairRootHiddenDAG G).observedNode i) node) :
    (pairRootHiddenDAG G).hidden node = false := by
  match path with
  | .direct edge =>
      cases hhid : (pairRootHiddenDAG G).hidden node with
      | false => rfl
      | true =>
          have hlt : node.val < pairRootCount G :=
            (pairRootHiddenDAG_hidden_iff G node).mp hhid
          have hedge :
              pairRootHiddenEdge G (pairRootObservedNode G i) node = true := by
            simpa [pairRootHiddenDAG] using edge
          have hfalse :
              pairRootHiddenEdge G (pairRootObservedNode G i)
                (pairRootHiddenNode G ⟨node.val, hlt⟩) = false :=
            pairRootHidden_no_to_hidden G _ _
          have heq :
              node = pairRootHiddenNode G ⟨node.val, hlt⟩ := by
            apply Fin.ext
            simp [pairRootHiddenNode]
          rw [heq] at hedge
          simp [hedge] at hfalse
  | .tail path' hhidden edge =>
      have ih := not_hidden_of_path_from_observed G path'
      simp [ih] at hhidden

/--
A hidden-internal path that begins at a pair-root is a single outgoing arrow
to one of that root's two observed endpoints.  Pair-roots have no hidden
children, so the path cannot be extended.
-/
theorem path_from_hidden_is_incident (G : ObservedGraph S)
    {rootNode node : Fin (pairRootHiddenDAG G).count}
    (hroot : (pairRootHiddenDAG G).hidden rootNode = true)
    (path : (pairRootHiddenDAG G).HiddenInternalPath rootNode node) :
    (pairRootHiddenDAG G).hidden node = false ∧
      ∃ obs : Fin S.count,
        node = pairRootObservedNode G obs ∧
          pairRootIncident G
              ⟨rootNode.val,
                (pairRootHiddenDAG_hidden_iff G rootNode).mp hroot⟩
              obs = true := by
  match path with
  | .direct edge =>
      have hsrc : rootNode.val < pairRootCount G :=
        (pairRootHiddenDAG_hidden_iff G rootNode).mp hroot
      have hedge : pairRootHiddenEdge G rootNode node = true := by
        simpa [pairRootHiddenDAG] using edge
      unfold pairRootHiddenEdge at hedge
      split at hedge
      · next hsrc' =>
          split at hedge
          · next htgt =>
              let obs : Fin S.count :=
                ⟨node.val - pairRootCount G,
                  Nat.sub_lt_left_of_lt_add htgt node.isLt⟩
              have hnode : node = pairRootObservedNode G obs := by
                apply Fin.ext
                simp [pairRootObservedNode, obs]
                exact (Nat.add_sub_cancel' htgt).symm
              have hnot : (pairRootHiddenDAG G).hidden node = false := by
                refine decide_eq_false ?_
                exact Nat.not_lt.mpr htgt
              exact ⟨hnot, obs, hnode, hedge⟩
          · simp at hedge
      · next hsrc' =>
          exact (hsrc' hsrc).elim
  | .tail path' hhidden edge =>
      have ih := path_from_hidden_is_incident G hroot path'
      simp [ih.1] at hhidden

/--
Directed projection recovers the original directed classifier.  The converse
uses that an observed-to-observed hidden-internal path cannot pass through a
pair-root.
-/
theorem pairRootHiddenDAG_directed (G : ObservedGraph S)
    (i j : Fin S.count) :
    S.directed i j = true ↔
      (pairRootHiddenDAG G).projectedDirected i j := by
  constructor
  · intro hedge
    refine FiniteHiddenDAG.HiddenInternalPath.direct ?_
    change pairRootHiddenEdge G
        (pairRootObservedNode G i) (pairRootObservedNode G j) = true
    rwa [pairRootHidden_observed_edge]
  · intro path
    cases path with
    | direct edge =>
        have hedge :
            pairRootHiddenEdge G
                (pairRootObservedNode G i) (pairRootObservedNode G j) =
              true := by
          simpa [pairRootHiddenDAG] using edge
        simpa [pairRootHidden_observed_edge] using hedge
    | tail path' hhidden edge =>
        have hnot := not_hidden_of_path_from_observed G path'
        simp [hnot] at hhidden

/--
Bidirected projection recovers the original bidirected classifier.  A projected
bidirected edge is witnessed by a pair-root with direct arrows to both
endpoints, and every original bidirected edge supplies such a root.
-/
theorem pairRootHiddenDAG_bidirected (G : ObservedGraph S)
    (i j : Fin S.count) :
    G.bidirected i j = true ↔
      (pairRootHiddenDAG G).projectedBidirected i j := by
  constructor
  · intro hedge
    have hne : i ≠ j := by
      intro hij
      cases hij
      simp [G.bidirected_irreflexive i] at hedge
    have hvalne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    refine ⟨hne, ?_⟩
    rcases lt_or_gt_of_val_ne hvalne with hlt | hgt
    · let root := pairRootOf G hlt hedge
      have hhidden :
          (pairRootHiddenDAG G).hidden (pairRootHiddenNode G root) = true :=
        (pairRootHiddenDAG_hidden_iff G _).mpr
          (by simp [pairRootHiddenNode])
      have hleft :
          (pairRootHiddenDAG G).HiddenInternalPath
            (pairRootHiddenNode G root)
            ((pairRootHiddenDAG G).observedNode i) := by
        refine FiniteHiddenDAG.HiddenInternalPath.direct ?_
        change pairRootHiddenEdge G
            (pairRootHiddenNode G root) (pairRootObservedNode G i) = true
        rw [pairRootHidden_root_edge]
        exact (pairRootIncident_of G hlt hedge).1
      have hright :
          (pairRootHiddenDAG G).HiddenInternalPath
            (pairRootHiddenNode G root)
            ((pairRootHiddenDAG G).observedNode j) := by
        refine FiniteHiddenDAG.HiddenInternalPath.direct ?_
        change pairRootHiddenEdge G
            (pairRootHiddenNode G root) (pairRootObservedNode G j) = true
        rw [pairRootHidden_root_edge]
        exact (pairRootIncident_of G hlt hedge).2
      exact ⟨pairRootHiddenNode G root, hhidden, hleft, hright⟩
    · have hedge' : G.bidirected j i = true :=
        G.bidirected_symmetric hedge
      let root := pairRootOf G hgt hedge'
      have hhidden :
          (pairRootHiddenDAG G).hidden (pairRootHiddenNode G root) = true :=
        (pairRootHiddenDAG_hidden_iff G _).mpr
          (by simp [pairRootHiddenNode])
      have hleft :
          (pairRootHiddenDAG G).HiddenInternalPath
            (pairRootHiddenNode G root)
            ((pairRootHiddenDAG G).observedNode i) := by
        refine FiniteHiddenDAG.HiddenInternalPath.direct ?_
        change pairRootHiddenEdge G
            (pairRootHiddenNode G root) (pairRootObservedNode G i) = true
        rw [pairRootHidden_root_edge]
        exact (pairRootIncident_of G hgt hedge').2
      have hright :
          (pairRootHiddenDAG G).HiddenInternalPath
            (pairRootHiddenNode G root)
            ((pairRootHiddenDAG G).observedNode j) := by
        refine FiniteHiddenDAG.HiddenInternalPath.direct ?_
        change pairRootHiddenEdge G
            (pairRootHiddenNode G root) (pairRootObservedNode G j) = true
        rw [pairRootHidden_root_edge]
        exact (pairRootIncident_of G hgt hedge').1
      exact ⟨pairRootHiddenNode G root, hhidden, hleft, hright⟩
  · intro hproj
    rcases hproj with ⟨hne, rootNode, hhidden, left, right⟩
    have hsrc : rootNode.val < pairRootCount G :=
      (pairRootHiddenDAG_hidden_iff G rootNode).mp hhidden
    have hleft := path_from_hidden_is_incident G hhidden left
    have hright := path_from_hidden_is_incident G hhidden right
    rcases hleft with ⟨_, obsi, hnodei, hinci⟩
    rcases hright with ⟨_, obsj, hnodej, hincj⟩
    have hi : i = obsi :=
      (pairRootHiddenDAG G).observedNode_injective (by
        simpa [pairRootHiddenDAG] using hnodei)
    have hj : j = obsj :=
      (pairRootHiddenDAG G).observedNode_injective (by
        simpa [pairRootHiddenDAG] using hnodej)
    have hspec := pairRoots_get_spec G ⟨rootNode.val, hsrc⟩
    let pair := (pairRoots G).get ⟨rootNode.val, hsrc⟩
    have hpair : G.bidirected pair.1 pair.2 = true := hspec.2
    have hi' := (pairRootIncident_iff G ⟨rootNode.val, hsrc⟩ obsi).mp hinci
    have hj' := (pairRootIncident_iff G ⟨rootNode.val, hsrc⟩ obsj).mp hincj
    have hcases :
        (obsi = pair.1 ∧ obsj = pair.2) ∨
          (obsi = pair.2 ∧ obsj = pair.1) := by
      rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
      · exact False.elim (hne (hi.trans (hi'.trans hj'.symm) |>.trans hj.symm))
      · exact Or.inl ⟨hi', hj'⟩
      · exact Or.inr ⟨hi', hj'⟩
      · exact False.elim (hne (hi.trans (hi'.trans hj'.symm) |>.trans hj.symm))
    cases hcases with
    | inl h =>
        simpa [hi, hj, h.1, h.2] using hpair
    | inr h =>
        simpa [hi, hj, h.1, h.2] using G.bidirected_symmetric hpair

/--
The packaged latent projection of the pair-root expansion.  Hiding the
introduced roots recovers the original directed and bidirected classifiers.
-/
def pairRootProjection (G : ObservedGraph S) : FiniteLatentProjection S where
  hiddenDAG := pairRootHiddenDAG G
  directed_matches := pairRootHiddenDAG_directed G
  bidirected := G.bidirected
  bidirected_matches := pairRootHiddenDAG_bidirected G

theorem pairRootProjection_directed (G : ObservedGraph S)
    (i j : Fin S.count) :
    (pairRootProjection G).hiddenDAG.projectedDirected i j ↔
      S.directed i j = true :=
  (pairRootHiddenDAG_directed G i j).symm

theorem pairRootProjection_bidirected (G : ObservedGraph S)
    (i j : Fin S.count) :
    (pairRootProjection G).hiddenDAG.projectedBidirected i j ↔
      G.bidirected i j = true :=
  (pairRootHiddenDAG_bidirected G i j).symm

theorem pairRootProjection_observedGraph (G : ObservedGraph S)
    (i j : Fin S.count) :
    (pairRootProjection G).observedGraph.bidirected i j = G.bidirected i j :=
  rfl

end Causality
end Thesis
