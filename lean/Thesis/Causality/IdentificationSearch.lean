import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
Executable Shpitser–Pearl ID on a finite observed ADMG.

The search is data, not a Prop-valued existence proof: c-components, ancestral
sets, and the ID recursion are computed by bounded reachability and structural
recursion on a fuel parameter.  No choice is used.

A successful run returns an action-free `ProbabilityTerm` built from
observational kernels, products, quotients, and marginals.  That syntactic
invariant is `identifyJoint_identified_actionFree`.  Failure is the
graphical hedge branch of ID (one c-component on `G` and on `G \ X`).
`unfinished` is reserved for exhausted fuel or an unmatched partition shape;
the fuel below is large enough for every finite signature, and completeness
will later prove that branch empty.

Conditional queries currently reduce by Bayes to two joint ID calls.  That is
sound whenever both joints identify, but it is not yet the full IDC insertion
of extra observations; those d-separation reductions belong in a subsequent
pass.

The intended completeness package (`Thesis.CausalTransport.Completeness`)
reads success as a certificate candidate and failure as a hedge to be
found by finite search over vertex selections and kept children inside
the failing c-component, then inhabited inside `GraphModelClass.positive`
under `ValueRich`.  That search is complete for enumerated candidates:
any selection inside `remaining` whose Boolean hedge tests pass is found.
-/

namespace ObservedGraph

/--
Induced ADMG on a selected vertex set: bidirected edges with an endpoint
outside the set are dropped.  Directed edges stay those of the signature and
are filtered by the search predicates below, so this restriction is only
needed to re-index bidirected connectivity.
-/
def restrict (G : ObservedGraph S) (nodes : NodeSet S) : ObservedGraph S where
  bidirected := fun i j => nodes i && nodes j && G.bidirected i j
  bidirected_symmetric := by
    intro i j h
    have joined :
        (nodes i && nodes j) = true ∧ G.bidirected i j = true :=
      Bool.and_eq_true_iff.mp h
    have both : nodes i = true ∧ nodes j = true :=
      Bool.and_eq_true_iff.mp joined.1
    have symmetric := G.bidirected_symmetric joined.2
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨both.2, both.1⟩, symmetric⟩
  bidirected_irreflexive := by
    intro i
    cases nodes i
    · rfl
    · exact G.bidirected_irreflexive i

/-- Directed edge of the mutilated graph that remains inside `nodes`. -/
def directedEdgeWithin (G : ObservedGraph S) (nodes : NodeSet S)
    (m : GraphMutilation S) (parent child : Fin S.count) : Bool :=
  nodes parent && nodes child && G.observedDirectedEdge m parent child

/--
Whether `source` can reach some selected target along directed edges that
stay inside `nodes` after mutilation.
-/
def ancestorOfWithin (G : ObservedGraph S) (nodes : NodeSet S)
    (m : GraphMutilation S) (targets : NodeSet S) (source : Fin S.count) :
    Bool :=
  nodes source &&
    (NodeSet.members (NodeSet.inter targets nodes)).any (fun target =>
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (G.directedEdgeWithin nodes m) S.count source target)

/-- Ancestral closure of `targets` inside `nodes` after mutilation. -/
def ancestralSet (G : ObservedGraph S) (nodes : NodeSet S)
    (m : GraphMutilation S) (targets : NodeSet S) : NodeSet S :=
  fun i => G.ancestorOfWithin nodes m targets i

/-- Bidirected reachability inside `nodes`, with fuel `|V|`. -/
def bidirectedReachableWithin (G : ObservedGraph S) (nodes : NodeSet S)
    (source target : Fin S.count) : Bool :=
  nodes source && nodes target &&
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (fun i j => nodes i && nodes j && G.bidirected i j)
      S.count source target

/--
C-component of `root` inside `nodes`: the bidirected-connected class of
`root`.  Isolated vertices form singleton components.
-/
def cComponentOf (G : ObservedGraph S) (nodes : NodeSet S)
    (root : Fin S.count) : NodeSet S :=
  fun i => G.bidirectedReachableWithin nodes root i

/--
Partition of `nodes` into c-components, in the order of first discovery
along the topological enumeration.
-/
def cComponentsCollect (G : ObservedGraph S) (nodes : NodeSet S) :
    List (Fin S.count) -> List (NodeSet S) -> List (NodeSet S)
  | [], acc => acc.reverse
  | root :: rest, acc =>
      if nodes root then
        if acc.any (fun component => component root) then
          cComponentsCollect G nodes rest acc
        else
          cComponentsCollect G nodes rest (G.cComponentOf nodes root :: acc)
      else
        cComponentsCollect G nodes rest acc

def cComponents (G : ObservedGraph S) (nodes : NodeSet S) :
    List (NodeSet S) :=
  cComponentsCollect G nodes (NodeSet.enumerated S) []

/-- Whether `nodes` is a single bidirected-connected piece of `G`. -/
def isSingleCComponent (G : ObservedGraph S) (nodes : NodeSet S) : Bool :=
  match G.cComponents nodes with
  | [component] => NodeSet.equal component nodes
  | _ => false

/-- The unique listed c-component containing `subset`, if any. -/
def containingCComponent (G : ObservedGraph S) (nodes subset : NodeSet S) :
    Option (NodeSet S) :=
  (G.cComponents nodes).find? (fun component =>
    NodeSet.subsetBool subset component)

end ObservedGraph

/-- Every listed c-component is the bidirected class of some selected root. -/
theorem cComponentsCollect_mem
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pending : List (Fin S.count)) (acc : List (NodeSet S))
    (hacc : forall c, c ∈ acc ->
      Exists fun root =>
        nodes root = true ∧ c = G.cComponentOf nodes root)
    {component : NodeSet S}
    (h : component ∈ ObservedGraph.cComponentsCollect G nodes pending acc) :
    Exists fun root =>
      nodes root = true ∧ component = G.cComponentOf nodes root := by
  induction pending generalizing acc with
  | nil =>
      simp [ObservedGraph.cComponentsCollect] at h
      exact hacc component h
  | cons root rest ih =>
      cases hnode : nodes root with
      | false =>
          simp [ObservedGraph.cComponentsCollect, hnode] at h
          exact ih acc hacc h
      | true =>
          cases hseen : acc.any (fun c => c root) with
          | true =>
              simp [ObservedGraph.cComponentsCollect, hnode, hseen] at h
              exact ih acc hacc h
          | false =>
              simp [ObservedGraph.cComponentsCollect, hnode, hseen] at h
              refine ih (G.cComponentOf nodes root :: acc) ?_ h
              intro c hc
              rcases List.mem_cons.mp hc with heq | hca
              · exact ⟨root, hnode, heq⟩
              · exact hacc c hca

theorem cComponents_mem
    (G : ObservedGraph S) (nodes : NodeSet S) {component : NodeSet S}
    (h : component ∈ G.cComponents nodes) :
    Exists fun root =>
      nodes root = true ∧ component = G.cComponentOf nodes root :=
  cComponentsCollect_mem G nodes (NodeSet.enumerated S) []
    (fun _c hc => by cases hc) h

/-- Accumulated components survive the rest of the collector. -/
theorem cComponentsCollect_keeps_acc
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pending : List (Fin S.count)) (acc : List (NodeSet S))
    {component : NodeSet S} (h : component ∈ acc) :
    component ∈ ObservedGraph.cComponentsCollect G nodes pending acc := by
  induction pending generalizing acc with
  | nil =>
      simp [ObservedGraph.cComponentsCollect]
      exact h
  | cons root rest ih =>
      cases hnode : nodes root with
      | false =>
          simp [ObservedGraph.cComponentsCollect, hnode]
          exact ih acc h
      | true =>
          cases hseen : acc.any (fun c => c root) with
          | true =>
              simp [ObservedGraph.cComponentsCollect, hnode, hseen]
              exact ih acc h
          | false =>
              simp [ObservedGraph.cComponentsCollect, hnode, hseen]
              exact ih (G.cComponentOf nodes root :: acc)
                (List.mem_cons.mpr (Or.inr h))

/--
A Boolean singleton partition is the c-component of any of its members.
-/
theorem isSingleCComponent_spec
    (G : ObservedGraph S) (nodes : NodeSet S)
    (h : G.isSingleCComponent nodes = true) :
    Exists fun root =>
      nodes root = true ∧ nodes = G.cComponentOf nodes root := by
  unfold ObservedGraph.isSingleCComponent at h
  cases hc : G.cComponents nodes with
  | nil => simp [hc] at h
  | cons c rest =>
      cases rest with
      | cons _ _ => simp [hc] at h
      | nil =>
          simp [hc] at h
          have eq : c = nodes := (NodeSet.equal_eq_true_iff c nodes).mp h
          have mem : c ∈ G.cComponents nodes := by simp [hc]
          rcases cComponents_mem G nodes mem with ⟨root, hroot, hdef⟩
          exact ⟨root, hroot, eq.symm.trans hdef⟩

theorem isSingleCComponent_nonempty
    (G : ObservedGraph S) (nodes : NodeSet S)
    (h : G.isSingleCComponent nodes = true) :
    NodeSet.isEmpty nodes = false := by
  rcases isSingleCComponent_spec G nodes h with ⟨root, hroot, _⟩
  exact (NodeSet.isEmpty_eq_false_iff nodes).mpr ⟨root, hroot⟩

/--
Once every selected vertex already belongs to some accumulated component,
the collector adds nothing more.  A connected host therefore yields a
singleton partition after the first discovery.
-/
theorem cComponentsCollect_covered
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pending : List (Fin S.count)) (acc : List (NodeSet S))
    (hcov : forall root, nodes root = true ->
      acc.any (fun c => c root) = true) :
    ObservedGraph.cComponentsCollect G nodes pending acc = acc.reverse := by
  induction pending generalizing acc with
  | nil =>
      simp [ObservedGraph.cComponentsCollect]
  | cons root rest ih =>
      cases hnode : nodes root with
      | false =>
          simp [ObservedGraph.cComponentsCollect, hnode]
          exact ih acc hcov
      | true =>
          have hseen : acc.any (fun c => c root) = true := hcov root hnode
          simp [ObservedGraph.cComponentsCollect, hnode, hseen]
          exact ih acc hcov

/-- Ancestral restriction never adds vertices. -/
theorem ancestralSet_subset (G : ObservedGraph S) (nodes : NodeSet S)
    (m : GraphMutilation S) (targets : NodeSet S) :
    NodeSet.Subset (G.ancestralSet nodes m targets) nodes := by
  intro i hi
  exact (Bool.and_eq_true_iff.mp hi).1

/--
Boolean `find?` success yields membership and a true predicate, by
induction on the list.  The Init `find?_eq_some` lemma is avoided
because it depends on choice.
-/
theorem find?_eq_some_mem {α : Type _} (p : α -> Bool)
    (xs : List α) {a : α} (h : xs.find? p = some a) :
    a ∈ xs ∧ p a = true := by
  induction xs with
  | nil =>
      simp [List.find?] at h
  | cons x rest ih =>
      cases hp : p x with
      | true =>
          simp [List.find?, hp] at h
          subst h
          exact ⟨List.mem_cons.mpr (Or.inl rfl), hp⟩
      | false =>
          simp [List.find?, hp] at h
          rcases ih h with ⟨hmem, hpa⟩
          exact ⟨List.mem_cons.mpr (Or.inr hmem), hpa⟩

theorem containingCComponent_spec
    (G : ObservedGraph S) (nodes subset : NodeSet S) {larger : NodeSet S}
    (h : G.containingCComponent nodes subset = some larger) :
    larger ∈ G.cComponents nodes ∧ NodeSet.Subset subset larger := by
  have parts := find?_eq_some_mem
      (fun component => NodeSet.subsetBool subset component)
      (G.cComponents nodes) h
  exact ⟨parts.1, (NodeSet.subsetBool_eq_true_iff subset larger).mp parts.2⟩

/-- Membership in an executable c-component implies membership in the host set. -/
theorem cComponentOf_subset (G : ObservedGraph S) (nodes : NodeSet S)
    {root i : Fin S.count} (h : G.cComponentOf nodes root i = true) :
    nodes i = true := by
  have reached : G.bidirectedReachableWithin nodes root i = true := by
    simpa [ObservedGraph.cComponentOf] using h
  have outer :
      (nodes root && nodes i) = true ∧
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (fun a b => nodes a && nodes b && G.bidirected a b)
          S.count root i = true :=
    Bool.and_eq_true_iff.mp (by
      simpa [ObservedGraph.bidirectedReachableWithin] using reached)
  exact (Bool.and_eq_true_iff.mp outer.1).2

/-- Every listed c-component is supported on the host vertex set. -/
theorem cComponents_subset
    (G : ObservedGraph S) (nodes : NodeSet S) {component : NodeSet S}
    (h : component ∈ G.cComponents nodes) :
    NodeSet.Subset component nodes := by
  rcases cComponents_mem G nodes h with ⟨root, _, hdef⟩
  intro i hi
  have hi' : G.cComponentOf nodes root i = true := by
    simpa [hdef] using hi
  exact cComponentOf_subset G nodes hi'

theorem containingCComponent_subset_host
    (G : ObservedGraph S) (nodes subset : NodeSet S) {larger : NodeSet S}
    (h : G.containingCComponent nodes subset = some larger) :
    NodeSet.Subset larger nodes := by
  rcases containingCComponent_spec G nodes subset h with ⟨hmem, _⟩
  rcases cComponents_mem G nodes hmem with ⟨root, _, hdef⟩
  intro i hi
  have hi' : G.cComponentOf nodes root i = true := by
    simpa [hdef] using hi
  exact cComponentOf_subset G nodes hi'

/-! ## Vertex-thinned c-forests and ID failure data -/

/--
Directed children of `parent` that still lie in `nodes`, in topological
order.  A subgraph c-forest keeps at most one of these, or none.
-/
def directedChildren (nodes : NodeSet S) (parent : Fin S.count) :
    List (Fin S.count) :=
  (NodeSet.members nodes).filter (fun child => S.directed parent child)

/-- Boolean one-child test matching `AtMostOneDirectedChild` on `G`. -/
def atMostOneDirectedChildBool (nodes : NodeSet S) : Bool :=
  (NodeSet.members nodes).all (fun parent =>
    match directedChildren nodes parent with
    | [] => true
    | [_] => true
    | _ :: _ :: _ => false)

/-- Sinks of the induced directed graph on `nodes`: no selected child. -/
def forestSinks (nodes : NodeSet S) : NodeSet S :=
  fun i =>
    nodes i &&
      !(NodeSet.members nodes).any (fun child => S.directed i child)

/-- Preferred seed: first outcome node in `nodes`, otherwise the first member. -/
def forestSeed (preferred nodes : NodeSet S) : Option (Fin S.count) :=
  match NodeSet.firstMember (NodeSet.inter preferred nodes) with
  | some node => some node
  | none => NodeSet.firstMember nodes

theorem forestSeed_mem (preferred nodes : NodeSet S) {seed : Fin S.count}
    (h : forestSeed preferred nodes = some seed) : nodes seed = true := by
  cases hpref : NodeSet.firstMember (NodeSet.inter preferred nodes) with
  | none =>
      have hx : NodeSet.firstMember nodes = some seed := by
        simpa [forestSeed, hpref] using h
      exact NodeSet.firstMember_mem hx
  | some node =>
      simp [forestSeed, hpref] at h
      subst h
      exact NodeSet.inter_subset_right preferred nodes node
        (NodeSet.firstMember_mem hpref)

/-- If the preferred set meets `nodes`, `forestSeed` is that first preferred member. -/
theorem forestSeed_eq_preferred (preferred nodes : NodeSet S)
    {seed : Fin S.count}
    (hpref : NodeSet.firstMember (NodeSet.inter preferred nodes) = some seed) :
    forestSeed preferred nodes = some seed := by
  simp [forestSeed, hpref]

theorem forestSeed_preferred_mem (preferred nodes : NodeSet S)
    {seed : Fin S.count}
    (hpref : NodeSet.firstMember (NodeSet.inter preferred nodes) = some seed) :
    preferred seed = true ∧ nodes seed = true := by
  have hinter : NodeSet.inter preferred nodes seed = true :=
    NodeSet.firstMember_mem hpref
  exact ⟨NodeSet.inter_subset_left preferred nodes seed hinter,
    NodeSet.inter_subset_right preferred nodes seed hinter⟩

theorem forestSeed_of_nonempty (preferred nodes : NodeSet S)
    (h : NodeSet.isEmpty nodes = false) :
    Exists fun seed => forestSeed preferred nodes = some seed := by
  cases hpref : NodeSet.firstMember (NodeSet.inter preferred nodes) with
  | some seed =>
      exact ⟨seed, by simp [forestSeed, hpref]⟩
  | none =>
      rcases NodeSet.firstMember_of_not_empty h with ⟨seed, hs⟩
      exact ⟨seed, by simp [forestSeed, hpref, hs]⟩

/-- Extra directed children (all but the earliest) of one parent. -/
def extraDirectedChildren (nodes : NodeSet S) (parent : Fin S.count) :
    List (Fin S.count) :=
  match directedChildren nodes parent with
  | [] => []
  | _keep :: extras => extras

/--
Children of a branching parent that can be dropped without losing
bidirected contact between `seedY` and `seedKeep`.  The outcome seed itself
is never a candidate: dropping it would empty the component we are thinning.
-/
def extraChildrenOfParent (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep parent : Fin S.count) : List (Fin S.count) :=
  match directedChildren nodes parent with
  | [] => []
  | [_] => []
  | c1 :: c2 :: rest =>
      (c1 :: c2 :: rest).filter (fun child =>
        decide (child ≠ seedY) &&
          (G.cComponentOf (NodeSet.diff nodes (NodeSet.singleton child))
            seedY) seedKeep)

/-- Every extra child of every branching parent, in topological parent order. -/
def extraChildCandidates (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) : List (Fin S.count) :=
  (NodeSet.members nodes).flatMap
    (extraChildrenOfParent G nodes seedY seedKeep)

/--
A vertex that can be dropped while keeping `seedY`'s bidirected component
on the residual set in contact with `seedKeep`.
-/
def extraChildToDrop (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) : Option (Fin S.count) :=
  (extraChildCandidates G nodes seedY seedKeep).getLast?

theorem extraChildrenOfParent_ne_seedY
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep parent child : Fin S.count)
    (h : child ∈ extraChildrenOfParent G nodes seedY seedKeep parent) :
    child ≠ seedY := by
  unfold extraChildrenOfParent at h
  cases hcs : directedChildren nodes parent with
  | nil => simp [hcs] at h
  | cons c rest =>
      cases rest with
      | nil => simp [hcs] at h
      | cons c2 rest2 =>
          simp [hcs, List.mem_filter] at h
          exact h.2.1

theorem extraChildrenOfParent_keeps_contact
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep parent child : Fin S.count)
    (h : child ∈ extraChildrenOfParent G nodes seedY seedKeep parent) :
    G.cComponentOf (NodeSet.diff nodes (NodeSet.singleton child)) seedY
      seedKeep = true := by
  unfold extraChildrenOfParent at h
  cases hcs : directedChildren nodes parent with
  | nil => simp [hcs] at h
  | cons c rest =>
      cases rest with
      | nil => simp [hcs] at h
      | cons c2 rest2 =>
          simp [hcs, List.mem_filter] at h
          exact h.2.2

theorem extraChildCandidates_ne_seedY
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep child : Fin S.count)
    (h : child ∈ extraChildCandidates G nodes seedY seedKeep) :
    child ≠ seedY := by
  rcases (List.mem_flatMap.mp h) with ⟨parent, _, hinner⟩
  exact extraChildrenOfParent_ne_seedY G nodes seedY seedKeep parent child
    hinner

theorem extraChildToDrop_mem_candidates
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep child : Fin S.count)
    (h : extraChildToDrop G nodes seedY seedKeep = some child) :
    child ∈ extraChildCandidates G nodes seedY seedKeep := by
  have hx :
      (extraChildCandidates G nodes seedY seedKeep).getLast? = some child := by
    simpa [extraChildToDrop] using h
  rcases (List.getLast?_eq_some_iff).mp hx with ⟨_prefix, hlist⟩
  simp [hlist]

theorem extraChildToDrop_ne_seedY
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep child : Fin S.count)
    (h : extraChildToDrop G nodes seedY seedKeep = some child) :
    child ≠ seedY :=
  extraChildCandidates_ne_seedY G nodes seedY seedKeep child
    (extraChildToDrop_mem_candidates G nodes seedY seedKeep child h)

theorem extraChildToDrop_keeps_contact
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep child : Fin S.count)
    (h : extraChildToDrop G nodes seedY seedKeep = some child) :
    G.cComponentOf (NodeSet.diff nodes (NodeSet.singleton child)) seedY
      seedKeep = true := by
  have hmem := extraChildToDrop_mem_candidates G nodes seedY seedKeep child h
  rcases List.mem_flatMap.mp hmem with ⟨parent, _, hinner⟩
  exact extraChildrenOfParent_keeps_contact G nodes seedY seedKeep parent
    child hinner

/--
One thinning step: drop a later extra child and re-close the bidirected
component of `seedY`.  Fuel is the current vertex count.
-/
def thinTowardForest (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) : Nat -> NodeSet S
  | 0 => G.cComponentOf nodes seedY
  | fuel + 1 =>
      if atMostOneDirectedChildBool nodes &&
          G.bidirectedReachableWithin nodes seedY seedKeep then
        G.cComponentOf nodes seedY
      else
        match extraChildToDrop G nodes seedY seedKeep with
        | some child =>
            thinTowardForest G
              (G.cComponentOf
                (NodeSet.diff nodes (NodeSet.singleton child)) seedY)
              seedY seedKeep fuel
        | none =>
            G.cComponentOf nodes seedY

/--
Whether every displayed root has a directed walk, in the graph with
incoming arrows to the action cut, to some outcome vertex.
-/
def rootsReachOutcomeBool (q : JointKernelQuery S) (roots : NodeSet S) :
    Bool :=
  (NodeSet.members roots).all (fun root =>
    (NodeSet.members q.outcome).any (fun y =>
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S q.action) S.count root y))

/--
The remaining vertex set and the unique free c-component at an ID hedge
branch.  `free` avoids the current action; `remaining` is a single
c-component of the working graph.
-/
structure IdentificationFail (S : ObservedSignature) where
  remaining : NodeSet S
  free : NodeSet S

/--
Large side of the extracted hedge: thin the ID-failure remaining set toward
a c-forest that still bidirected-connects an outcome seed to an action seed.
-/
def hedgeLargeOf (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) : NodeSet S :=
  match forestSeed q.outcome fail.remaining,
      NodeSet.firstMember (NodeSet.inter fail.remaining q.action) with
  | some seedY, some seedX =>
      thinTowardForest G fail.remaining seedY seedX
        (NodeSet.members fail.remaining).length
  | some seedY, none =>
      thinTowardForest G fail.remaining seedY seedY
        (NodeSet.members fail.remaining).length
  | none, _ => fail.remaining

/--
Small side: the bidirected component of an outcome seed inside the large
forest minus the original action.  This keeps `small ⊆ large` by
construction and avoids the action whenever `fail.free` does.
-/
def hedgeSmallOf (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) : NodeSet S :=
  let large := hedgeLargeOf G q fail
  let restricted := NodeSet.diff large q.action
  match forestSeed q.outcome restricted with
  | some seed => G.cComponentOf restricted seed
  | none => restricted

def hedgeRootsOf (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) : NodeSet S :=
  forestSinks (hedgeLargeOf G q fail)

/-! ## Finite subgraph hedge search -/

/-- The empty child map: every vertex is treated as a kept-edge sink. -/
def emptyChild (S : ObservedSignature) : ForestChild S :=
  fun _ => none

/-- Overwrite the kept successor of one parent. -/
def setChild (child : ForestChild S) (parent : Fin S.count)
    (value : Option (Fin S.count)) : ForestChild S :=
  fun i => if i = parent then value else child i

theorem setChild_self (child : ForestChild S) (parent : Fin S.count)
    (value : Option (Fin S.count)) :
    setChild child parent value parent = value := by
  simp [setChild]

/--
Induced child map of a one-child vertex set: the unique selected directed
successor, or `none`.  Used by thinning lemmas, not by the extractor.
-/
def inducedChild (nodes : NodeSet S) : ForestChild S :=
  fun parent =>
    if nodes parent then
      match directedChildren nodes parent with
      | [c] => some c
      | _ => none
    else
      none

/--
Kept child map of a subgraph C-forest.  Vertices in `small` keep the
earliest directed successor that still lies in `small`; vertices in
`large \ small` keep the earliest directed successor in `large`.  Extra
graph edges are not selected, so the map is a forest without requiring
the induced directed graph to have unique children.  Child-closure on
`small` holds by construction.
-/
def closedForestChild (large small : NodeSet S) : ForestChild S :=
  fun parent =>
    if large parent then
      if small parent then
        match directedChildren small parent with
        | [] => none
        | c :: _ => some c
      else
        match directedChildren large parent with
        | [] => none
        | c :: _ => some c
    else
      none

/-- Kept-edge sinks: selected vertices with no kept child. -/
def keptSinks (nodes : NodeSet S) (child : ForestChild S) : NodeSet S :=
  fun i => nodes i && decide (child i = none)

theorem keptSinks_iff (nodes : NodeSet S) (child : ForestChild S)
    (i : Fin S.count) :
    keptSinks nodes child i = true ↔
      nodes i = true ∧ child i = none := by
  constructor
  · intro h
    have parts := Bool.and_eq_true_iff.mp h
    exact ⟨parts.1, of_decide_eq_true parts.2⟩
  · intro h
    exact Bool.and_eq_true_iff.mpr ⟨h.1, decide_eq_true h.2⟩

theorem keptSinks_subset (nodes : NodeSet S) (child : ForestChild S) :
    NodeSet.Subset (keptSinks nodes child) nodes :=
  fun i hi => ((keptSinks_iff nodes child i).mp hi).1

/-- Child maps that mention only selected directed edges of `nodes`. -/
def childWellFormedBool (nodes : NodeSet S) (child : ForestChild S) : Bool :=
  (NodeSet.enumerated S).all (fun parent =>
    match nodes parent, child parent with
    | false, none => true
    | false, some _ => false
    | true, none => true
    | true, some c => nodes c && S.directed parent c)

/-- Every kept successor of a selected parent still lies in the set. -/
def childClosedBool (nodes : NodeSet S) (child : ForestChild S) : Bool :=
  (NodeSet.members nodes).all (fun parent =>
    match child parent with
    | none => true
    | some c => nodes c)

theorem childWellFormed_off (nodes : NodeSet S) (child : ForestChild S)
    (h : childWellFormedBool nodes child = true)
    {parent : Fin S.count} (hp : nodes parent = false) :
    child parent = none := by
  have mem : parent ∈ NodeSet.enumerated S := NodeSet.mem_enumerated S parent
  have ok := (List.all_eq_true.mp h) parent mem
  rw [hp] at ok
  cases hc : child parent with
  | none => rfl
  | some _ =>
      rw [hc] at ok
      exact False.elim (Bool.false_ne_true ok)

theorem childWellFormed_edge (nodes : NodeSet S) (child : ForestChild S)
    (h : childWellFormedBool nodes child = true)
    {parent c : Fin S.count} (hc : child parent = some c) :
    nodes parent = true ∧ nodes c = true ∧ S.directed parent c = true := by
  have mem : parent ∈ NodeSet.enumerated S := NodeSet.mem_enumerated S parent
  have ok := (List.all_eq_true.mp h) parent mem
  cases hp : nodes parent with
  | false =>
      rw [hp, hc] at ok
      exact False.elim (Bool.false_ne_true ok)
  | true =>
      rw [hp, hc] at ok
      exact ⟨rfl, (Bool.and_eq_true_iff.mp ok).1, (Bool.and_eq_true_iff.mp ok).2⟩

/--
The propositional fields of a `CForest` imply the executable well-formedness
test for its child map.  This direction complements the search-side
`cForest_of_child` constructor: downstream data computations may safely use
`forestSink` even when their forest arrived as an abstract witness rather
than directly from the Boolean hedge search.
-/
theorem CForest.wellFormedBool
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {child : ForestChild S}
    (forest : CForest G nodes roots child) :
    childWellFormedBool nodes child = true := by
  unfold childWellFormedBool
  refine List.all_eq_true.mpr ?_
  intro parent _parentMem
  cases hp : nodes parent with
  | false =>
      have hc : child parent = none := forest.child_off_set parent hp
      simp [hc]
  | true =>
      cases hc : child parent with
      | none =>
          simp
      | some c =>
          have edge := forest.child_edge parent c hc
          simp [edge.2.1, edge.2.2]

/--
Walk the kept-child map for `fuel` steps.  On a well-formed forest the
map is a DAG (`directed_earlier`), so `fuel = S.count` always lands on a
kept sink.  Fuel avoids well-founded recursion through a `match` on
`Option`.
-/
def forestFollow (child : ForestChild S) (start : Fin S.count) :
    Nat -> Fin S.count
  | 0 => start
  | n + 1 =>
    match child start with
    | none => start
    | some c => forestFollow child c n

/--
A well-formed kept-child walk of length at least `S.count - start.val`
ends at a selected vertex with no kept successor.  The zero-fuel case is
impossible: `start.val < S.count`.
-/
theorem forestFollow_sink
    (nodes : NodeSet S) (child : ForestChild S)
    (hwell : childWellFormedBool nodes child = true)
    (start : Fin S.count) (hstart : nodes start = true)
    (fuel : Nat) (hfuel : S.count - start.val ≤ fuel) :
    nodes (forestFollow child start fuel) = true ∧
      child (forestFollow child start fuel) = none := by
  induction fuel generalizing start with
  | zero =>
      have hzero : S.count - start.val = 0 := Nat.eq_zero_of_le_zero hfuel
      have hle : S.count ≤ start.val := Nat.sub_eq_zero_iff_le.mp hzero
      exact False.elim (Nat.not_le_of_gt start.isLt hle)
  | succ n ih =>
      cases hch : child start with
      | none =>
          constructor
          · simpa [forestFollow, hch] using hstart
          · simp [forestFollow, hch]
      | some c =>
          have hedge := childWellFormed_edge nodes child hwell hch
          have hlt : start.val < c.val := S.directed_earlier hedge.2.2
          have hfuel' : S.count - c.val ≤ n := by
            have hs : start.val + 1 ≤ c.val := Nat.succ_le_of_lt hlt
            have hstep :
                S.count - c.val ≤ S.count - start.val - 1 := by
              have :
                  S.count - c.val ≤ S.count - (start.val + 1) :=
                Nat.sub_le_sub_left hs S.count
              simpa [Nat.sub_add_eq] using this
            have hpred : S.count - start.val - 1 ≤ n :=
              Nat.sub_le_sub_right hfuel 1
            exact Nat.le_trans hstep hpred
          simpa [forestFollow, hch] using ih c hedge.2.1 hfuel'

/-- Kept-edge sink reached by following the child map from `start`. -/
def forestSink (nodes : NodeSet S) (child : ForestChild S)
    (_hwell : childWellFormedBool nodes child = true)
    (start : Fin S.count) (_hstart : nodes start = true) : Fin S.count :=
  forestFollow child start S.count

theorem forestSink_spec
    (nodes : NodeSet S) (child : ForestChild S)
    (hwell : childWellFormedBool nodes child = true)
    (start : Fin S.count) (hstart : nodes start = true) :
    nodes (forestSink nodes child hwell start hstart) = true ∧
      child (forestSink nodes child hwell start hstart) = none :=
  forestFollow_sink nodes child hwell start hstart S.count
    (Nat.sub_le S.count start.val)

theorem forestSink_kept
    (nodes : NodeSet S) (child : ForestChild S)
    (hwell : childWellFormedBool nodes child = true)
    (start : Fin S.count) (hstart : nodes start = true) :
    keptSinks nodes child (forestSink nodes child hwell start hstart) =
      true :=
  (keptSinks_iff nodes child
      (forestSink nodes child hwell start hstart)).mpr
    (forestSink_spec nodes child hwell start hstart)

/-- Child reached by one kept-map step, defaulting to the parent at a sink. -/
def forestEntryChild (child : ForestChild S) (parent : Fin S.count) :
    Fin S.count :=
  match child parent with
  | none => parent
  | some c => c

/-- A kept edge whose parent is outside `nodes` and child is inside it. -/
def forestChildEnters (nodes : NodeSet S) (child : ForestChild S)
    (parent : Fin S.count) : Bool :=
  match child parent with
  | none => false
  | some c => !(nodes parent) && nodes c

/-- Unpack the executable boundary-edge predicate. -/
theorem forestChildEnters_spec
    (nodes : NodeSet S) (child : ForestChild S) {parent : Fin S.count}
    (h : forestChildEnters nodes child parent = true) :
    child parent = some (forestEntryChild child parent) ∧
      nodes parent = false ∧
        nodes (forestEntryChild child parent) = true := by
  cases hc : child parent with
  | none =>
      simp [forestChildEnters, hc] at h
  | some c =>
      cases hp : nodes parent with
      | false =>
          have hchild : nodes c = true := by
            simpa [forestChildEnters, hc, hp] using h
          simp [forestEntryChild, hc, hchild]
      | true =>
          simp [forestChildEnters, hc, hp] at h

/--
If a finite child-map walk starts outside a set and ends inside it, one of
its traversed kept edges crosses the boundary.  No graph assumptions are
needed: this is the elementary discrete intermediate-value property for the
stored `Option` successor map.
-/
theorem forestFollow_has_entry
    (nodes : NodeSet S) (child : ForestChild S)
    (start : Fin S.count) (fuel : Nat)
    (startOutside : nodes start = false)
    (endInside : nodes (forestFollow child start fuel) = true) :
    Exists fun parent =>
      Exists fun c =>
        child parent = some c ∧ nodes parent = false ∧ nodes c = true := by
  induction fuel generalizing start with
  | zero =>
      exact False.elim
        (Bool.false_ne_true (startOutside.symm.trans endInside))
  | succ fuel inductionHypothesis =>
      cases hc : child start with
      | none =>
          have impossible : nodes start = true := by
            simpa [forestFollow, hc] using endInside
          exact False.elim
            (Bool.false_ne_true (startOutside.symm.trans impossible))
      | some c =>
          cases hnext : nodes c with
          | true =>
              exact ⟨start, c, hc, startOutside, hnext⟩
          | false =>
              have endInside' :
                  nodes (forestFollow child c fuel) = true := by
                simpa [forestFollow, hc] using endInside
              exact inductionHypothesis c hnext endInside'

/-- The finite node enumeration detects a boundary edge on such a walk. -/
theorem forestChildEnters_any_of_follow
    (nodes : NodeSet S) (child : ForestChild S)
    (start : Fin S.count) (fuel : Nat)
    (startOutside : nodes start = false)
    (endInside : nodes (forestFollow child start fuel) = true) :
    (NodeSet.enumerated S).any (forestChildEnters nodes child) = true := by
  rcases forestFollow_has_entry nodes child start fuel startOutside endInside
      with ⟨parent, c, hc, hp, hchild⟩
  exact List.any_eq_true.mpr
    ⟨parent, NodeSet.mem_enumerated S parent, by
      simp [forestChildEnters, hc, hp, hchild]⟩

/-- `find? = none` contradicts a successful Boolean `any`. -/
theorem list_any_true_of_find?_none {α} {l : List α} {p : α -> Bool}
    (noneAll : l.find? p = none) (h : l.any p = true) : False := by
  have notTrue : forall x, x ∈ l → ¬ p x = true :=
    List.find?_eq_none.mp noneAll
  rcases List.any_eq_true.mp h with ⟨x, hx, hp⟩
  exact notTrue x hx hp

/--
The first list element satisfying a Boolean predicate, as data.  The
`none` branch of `find?` is impossible because `any` already succeeded;
the existential unpacking remains inside that proof of `False`, not in the
surrounding `Type`-valued definition.
-/
def listFirstAny {α} (l : List α) (p : α -> Bool)
    (h : l.any p = true) : α :=
  match hf : l.find? p with
  | some a => a
  | none => False.elim (list_any_true_of_find?_none hf h)

theorem listFirstAny_mem {α} (l : List α) (p : α -> Bool)
    (h : l.any p = true) :
    listFirstAny l p h ∈ l := by
  unfold listFirstAny
  split
  · next _a hf =>
      exact List.mem_of_find?_eq_some hf
  · next hf =>
      exact False.elim (list_any_true_of_find?_none hf h)

theorem listFirstAny_pred {α} (l : List α) (p : α -> Bool)
    (h : l.any p = true) :
    p (listFirstAny l p h) = true := by
  unfold listFirstAny
  split
  · next _a hf =>
      exact List.find?_some hf
  · next hf =>
      exact False.elim (list_any_true_of_find?_none hf h)

/-!
### Data carried by a hedge's action branch

The semantic hedge construction needs a concrete common root below an action
vertex.  `HedgeWitness` stores the action vertex in `Type`; the functions below
follow its already-selected large-forest child map, so the resulting root is
data as well and no existential forest reachability is unpacked.
-/

/-- The large-forest root reached from the witness's stored action vertex. -/
def HedgeWitness.actionRoot {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : Fin S.count :=
  forestSink w.large w.child w.large_forest.wellFormedBool
    w.actionSeed w.actionSeed_in_large

/-- The computed action branch remains inside the large forest. -/
theorem HedgeWitness.actionRoot_in_large
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.large w.actionRoot = true :=
  (forestSink_spec w.large w.child
    w.large_forest.wellFormedBool w.actionSeed
    w.actionSeed_in_large).1

/-- The computed action branch stops exactly where the kept child map stops. -/
theorem HedgeWitness.actionRoot_child_none
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.child w.actionRoot = none :=
  (forestSink_spec w.large w.child
    w.large_forest.wellFormedBool w.actionSeed
    w.actionSeed_in_large).2

/-- The computed endpoint is one of the large forest's declared roots. -/
theorem HedgeWitness.actionRoot_in_roots
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.roots w.actionRoot = true :=
  (w.large_forest.roots_exact w.actionRoot).mpr
    ⟨w.actionRoot_in_large, w.actionRoot_child_none⟩

/-- The two hedge forests have the same roots, so the action root is small. -/
theorem HedgeWitness.actionRoot_in_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.small w.actionRoot = true :=
  ((w.small_forest.roots_exact w.actionRoot).mp
    w.actionRoot_in_roots).1

/-- The stored action vertex cannot lie in the action-avoiding small forest. -/
theorem HedgeWitness.actionSeed_not_in_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.small w.actionSeed = false := by
  cases hs : w.small w.actionSeed with
  | false =>
      rfl
  | true =>
      have actionFalse := w.small_avoids_intervention w.actionSeed hs
      exact False.elim
        (Bool.false_ne_true
          (actionFalse.symm.trans w.actionSeed_in_action))

/-- The action-to-root child walk contains an edge entering the small side. -/
theorem HedgeWitness.actionBoundary_existsBool
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    (NodeSet.enumerated S).any (forestChildEnters w.small w.child) = true :=
  forestChildEnters_any_of_follow w.small w.child w.actionSeed S.count
    w.actionSeed_not_in_small (by
      simpa [HedgeWitness.actionRoot, forestSink] using
        w.actionRoot_in_small)

/-- First enumerated kept parent whose edge enters the small forest. -/
def HedgeWitness.actionBoundaryParent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : Fin S.count :=
  listFirstAny (NodeSet.enumerated S) (forestChildEnters w.small w.child)
    w.actionBoundary_existsBool

/-- Child across the selected action-branch boundary edge. -/
def HedgeWitness.actionBoundaryChild
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : Fin S.count :=
  forestEntryChild w.child w.actionBoundaryParent

/-- The selected boundary parent really maps to the selected boundary child. -/
theorem HedgeWitness.actionBoundary_child
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.child w.actionBoundaryParent = some w.actionBoundaryChild :=
  (forestChildEnters_spec w.small w.child
    (listFirstAny_pred (NodeSet.enumerated S)
      (forestChildEnters w.small w.child)
      w.actionBoundary_existsBool)).1

/-- The selected boundary edge starts outside the small forest. -/
theorem HedgeWitness.actionBoundaryParent_not_in_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.small w.actionBoundaryParent = false :=
  (forestChildEnters_spec w.small w.child
    (listFirstAny_pred (NodeSet.enumerated S)
      (forestChildEnters w.small w.child)
      w.actionBoundary_existsBool)).2.1

/-- The selected boundary edge ends inside the small forest. -/
theorem HedgeWitness.actionBoundaryChild_in_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.small w.actionBoundaryChild = true :=
  (forestChildEnters_spec w.small w.child
    (listFirstAny_pred (NodeSet.enumerated S)
      (forestChildEnters w.small w.child)
      w.actionBoundary_existsBool)).2.2

/-- Both endpoints of the selected boundary edge belong to the large forest. -/
theorem HedgeWitness.actionBoundary_in_large
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.large w.actionBoundaryParent = true ∧
      w.large w.actionBoundaryChild = true :=
  let edge :=
    w.large_forest.child_edge w.actionBoundaryParent w.actionBoundaryChild
      w.actionBoundary_child
  ⟨edge.1, edge.2.1⟩

/-- The selected boundary edge is an actual directed edge of the graph. -/
theorem HedgeWitness.actionBoundary_directed
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    S.directed w.actionBoundaryParent w.actionBoundaryChild = true :=
  (w.large_forest.child_edge w.actionBoundaryParent w.actionBoundaryChild
    w.actionBoundary_child).2.2

theorem childClosed_spec (nodes : NodeSet S) (child : ForestChild S)
    (h : childClosedBool nodes child = true)
    {parent c : Fin S.count} (hp : nodes parent = true)
    (hc : child parent = some c) :
    nodes c = true := by
  have mem : parent ∈ NodeSet.members nodes :=
    (NodeSet.mem_members_iff nodes parent).mpr hp
  have ok := (List.all_eq_true.mp h) parent mem
  rw [hc] at ok
  exact ok

/-- Child-closure is the Boolean image of a stay-inside property. -/
theorem childClosedBool_of_stay (nodes : NodeSet S) (child : ForestChild S)
    (h : forall parent c, nodes parent = true -> child parent = some c ->
      nodes c = true) :
    childClosedBool nodes child = true := by
  refine List.all_eq_true.mpr ?_
  intro parent hp
  have hnode : nodes parent = true :=
    (NodeSet.mem_members_iff nodes parent).mp hp
  cases hc : child parent with
  | none =>
      simp
  | some c =>
      exact h parent c hnode hc

theorem inducedChild_wellFormed (nodes : NodeSet S) :
    childWellFormedBool nodes (inducedChild nodes) = true := by
  refine List.all_eq_true.mpr ?_
  intro parent _hmem
  cases hp : nodes parent with
  | false =>
      simp [inducedChild, hp]
  | true =>
      cases hcs : directedChildren nodes parent with
      | nil =>
          simp [inducedChild, hp, hcs]
      | cons c rest =>
          cases rest with
          | nil =>
              have memc : c ∈ directedChildren nodes parent := by
                simp [hcs]
              have parts := List.mem_filter.mp memc
              simp [inducedChild, hp, hcs]
              exact ⟨(NodeSet.mem_members_iff nodes c).mp parts.1, parts.2⟩
          | cons _ _ =>
              simp [inducedChild, hp, hcs]

theorem closedForestChild_wellFormed (large small : NodeSet S)
    (hsub : NodeSet.Subset small large) :
    childWellFormedBool large (closedForestChild large small) = true := by
  refine List.all_eq_true.mpr ?_
  intro parent _hmem
  cases hL : large parent with
  | false =>
      simp [closedForestChild, hL]
  | true =>
      cases hS : small parent with
      | true =>
          cases hcs : directedChildren small parent with
          | nil =>
              simp [closedForestChild, hL, hS, hcs]
          | cons c _rest =>
              have memc : c ∈ directedChildren small parent := by
                simp [hcs]
              have parts := List.mem_filter.mp memc
              have inSmall : small c = true :=
                (NodeSet.mem_members_iff small c).mp parts.1
              have inLarge : large c = true := hsub c inSmall
              simp [closedForestChild, hL, hS, hcs, inLarge, parts.2]
      | false =>
          cases hcs : directedChildren large parent with
          | nil =>
              simp [closedForestChild, hL, hS, hcs]
          | cons c _rest =>
              have memc : c ∈ directedChildren large parent := by
                simp [hcs]
              have parts := List.mem_filter.mp memc
              have inLarge : large c = true :=
                (NodeSet.mem_members_iff large c).mp parts.1
              simp [closedForestChild, hL, hS, hcs, inLarge, parts.2]

theorem closedForestChild_childClosed (large small : NodeSet S) :
    childClosedBool small (closedForestChild large small) = true :=
  childClosedBool_of_stay small (closedForestChild large small)
    (fun parent c hp hc => by
      cases hL : large parent with
      | false =>
          simp [closedForestChild, hL] at hc
      | true =>
          cases hS : small parent with
          | false =>
              exact False.elim (Bool.false_ne_true (hS.symm.trans hp))
          | true =>
              cases hcs : directedChildren small parent with
              | nil =>
                  simp [closedForestChild, hL, hS, hcs] at hc
              | cons d _rest =>
                  have hred :
                      closedForestChild large small parent = some d := by
                    simp [closedForestChild, hL, hS, hcs]
                  have heq : some d = some c := hred.symm.trans hc
                  injection heq with hcd
                  rw [← hcd]
                  have memd : d ∈ directedChildren small parent := by
                    simp [hcs]
                  exact (NodeSet.mem_members_iff small d).mp
                    (List.mem_filter.mp memd).1)

/--
Kept sinks of `closedForestChild` lie in `small` once every vertex of
`large \ small` has at least one directed successor in `large`.  In a
4.1 ID failure the ancestral side of `G_{\overline{X}}` supplies that
outgoing edge for every remaining action vertex.
-/
theorem closedForestChild_keptSinks_subset (large small : NodeSet S)
    (hout :
      forall parent,
        large parent = true ->
          small parent = false ->
            Exists fun child => child ∈ directedChildren large parent) :
    NodeSet.Subset
      (keptSinks large (closedForestChild large small)) small := by
  intro i hi
  have parts :=
    (keptSinks_iff large (closedForestChild large small) i).mp hi
  cases hS : small i with
  | true =>
      rfl
  | false =>
      rcases hout i parts.1 hS with ⟨_child, hmem⟩
      cases hcs : directedChildren large i with
      | nil =>
          simp [hcs] at hmem
      | cons d _rest =>
          have hnone : closedForestChild large small i = none := parts.2
          simp [closedForestChild, parts.1, hS, hcs] at hnone

theorem childWellFormed_restrict (large small : NodeSet S)
    (child : ForestChild S)
    (hwell : childWellFormedBool large child = true)
    (_hsub : NodeSet.Subset small large)
    (hclosed : childClosedBool small child = true) :
    childWellFormedBool small (restrictChild small child) = true := by
  refine List.all_eq_true.mpr ?_
  intro parent _hmem
  cases hp : small parent with
  | false =>
      simp [restrictChild, hp]
  | true =>
      simp [restrictChild, hp]
      cases hc : child parent with
      | none => simp
      | some c =>
          have hedge := childWellFormed_edge large child hwell hc
          have inSmall : small c = true :=
            childClosed_spec small child hclosed hp hc
          simp [inSmall, hedge.2.2]

theorem keptSinks_restrict_eq (large small : NodeSet S)
    (child : ForestChild S)
    (hsub : NodeSet.Subset small large)
    (_hclosed : childClosedBool small child = true)
    (hroots : NodeSet.Subset (keptSinks large child) small) :
    keptSinks small (restrictChild small child) =
      keptSinks large child := by
  funext i
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have parts := (keptSinks_iff small (restrictChild small child) i).mp h
    have hchild : child i = none := by
      have : restrictChild small child i = none := parts.2
      simpa [restrictChild, parts.1] using this
    exact (keptSinks_iff large child i).mpr ⟨hsub i parts.1, hchild⟩
  · intro h
    have parts := (keptSinks_iff large child i).mp h
    have inSmall : small i = true := hroots i h
    have hrest : restrictChild small child i = none := by
      simp [restrictChild, inSmall, parts.2]
    exact (keptSinks_iff small (restrictChild small child) i).mpr
      ⟨inSmall, hrest⟩

/-- Vertex tests independent of the child map. -/
def largeVerticesReady (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) : Bool :=
  (!NodeSet.isEmpty large) &&
    G.isSingleCComponent large &&
    NodeSet.meetsBool large q.action

/-- Child-map tests on a completed large vertex set. -/
def largeChildReady (_G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S) : Bool :=
  childWellFormedBool large child &&
    rootsReachOutcomeBool q (keptSinks large child)

/--
Small side: nested c-component, child-closed restriction of `child`,
containing every large kept-root, and avoiding `X`.
-/
def smallForestReady (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S) (small : NodeSet S) : Bool :=
  (!NodeSet.isEmpty small) &&
    G.isSingleCComponent small &&
    NodeSet.subsetBool small large &&
    NodeSet.disjointBool small q.action &&
    childClosedBool small child &&
    NodeSet.subsetBool (keptSinks large child) small

structure HedgeSelection (S : ObservedSignature) where
  large : NodeSet S
  small : NodeSet S
  child : ForestChild S

def hedgeTestsHold (G : ObservedGraph S) (q : JointKernelQuery S)
    (sel : HedgeSelection S) : Bool :=
  largeVerticesReady G q sel.large &&
    largeChildReady G q sel.large sel.child &&
    smallForestReady G q sel.large sel.child sel.small

/--
Search subsets of `pending` by first including the head vertex, then
skipping it.  The first fully assigned selection that passes `p` is
returned, so the search does not materialise the power set.
-/
def findSubset (pending : List (Fin S.count)) (acc : NodeSet S)
    (p : NodeSet S -> Bool) : Option (NodeSet S) :=
  match pending with
  | [] => if p acc then some acc else none
  | node :: rest =>
      match findSubset rest (NodeSet.insert acc node) p with
      | some found => some found
      | none => findSubset rest acc p

/--
A completed vertex assignment `found` extends the accumulator along
`pending`: everything already in `acc` stays selected, and every newly
selected index is still among the vertices the search is allowed to
include.  This is the data of one branch of `findSubset`, written as a
`Prop` so completeness can quantify over a known candidate rather than
over the power set.
-/
def ExtendsAcc (pending : List (Fin S.count)) (acc found : NodeSet S) :
    Prop :=
  (forall i, acc i = true -> found i = true) ∧
    (forall i, found i = true -> acc i = true ∨ i ∈ pending)

theorem extendsAcc_nil {acc found : NodeSet S}
    (h : ExtendsAcc [] acc found) : acc = found := by
  funext i
  cases ha : acc i with
  | false =>
      cases hf : found i with
      | false => rfl
      | true =>
          cases h.2 i hf with
          | inl hAcc =>
              exact False.elim (Bool.false_ne_true (ha.symm.trans hAcc))
          | inr mem =>
              cases mem
  | true =>
      exact (h.1 i ha).symm

theorem extendsAcc_cons_insert {node : Fin S.count}
    {rest : List (Fin S.count)} {acc found : NodeSet S}
    (h : ExtendsAcc (node :: rest) acc found)
    (hn : found node = true) :
    ExtendsAcc rest (NodeSet.insert acc node) found := by
  constructor
  · intro i hi
    have parts := (NodeSet.insert_eq_true_iff acc node i).mp hi
    cases parts with
    | inl hAcc => exact h.1 i hAcc
    | inr hEq =>
        subst hEq
        exact hn
  · intro i hi
    have fromPending := h.2 i hi
    have inserted : NodeSet.insert acc node i = true ↔
        acc i = true ∨ i = node :=
      NodeSet.insert_eq_true_iff acc node i
    cases fromPending with
    | inl hAcc => exact Or.inl (inserted.mpr (Or.inl hAcc))
    | inr hMem =>
        cases List.mem_cons.mp hMem with
        | inl hEq =>
            subst hEq
            exact Or.inl (inserted.mpr (Or.inr rfl))
        | inr hRest =>
            exact Or.inr hRest

theorem extendsAcc_cons_skip {node : Fin S.count}
    {rest : List (Fin S.count)} {acc found : NodeSet S}
    (h : ExtendsAcc (node :: rest) acc found)
    (hn : found node = false) :
    ExtendsAcc rest acc found := by
  constructor
  · exact h.1
  · intro i hi
    cases h.2 i hi with
    | inl hAcc => exact Or.inl hAcc
    | inr hMem =>
        cases List.mem_cons.mp hMem with
        | inl hEq =>
            subst hEq
            exact False.elim (Bool.false_ne_true (hn.symm.trans hi))
        | inr hRest =>
            exact Or.inr hRest

/--
Selections contained in a host, starting from the empty accumulator, are
exactly the include/skip assignments of the host's members.
-/
theorem extendsAcc_empty_of_subset {host found : NodeSet S}
    (sub : NodeSet.Subset found host) :
    ExtendsAcc (NodeSet.members host) NodeSet.empty found := by
  constructor
  · intro i hi
    simp [NodeSet.empty] at hi
  · intro i hi
    exact Or.inr ((NodeSet.mem_members_iff host i).mpr (sub i hi))

/-- First successful image of a list, in listed order. -/
def firstSome {α β : Type _} : List α -> (α -> Option β) -> Option β
  | [], _ => none
  | a :: rest, f =>
      match f a with
      | some b => some b
      | none => firstSome rest f

/-- `none`, then each directed child still in `nodes`. -/
def childOptions (nodes : NodeSet S) (parent : Fin S.count) :
    List (Option (Fin S.count)) :=
  none :: (directedChildren nodes parent).map some

theorem none_mem_childOptions (nodes : NodeSet S) (parent : Fin S.count) :
    none ∈ childOptions nodes parent :=
  List.mem_cons_self

theorem mem_directedChildren_iff (nodes : NodeSet S)
    (parent c : Fin S.count) :
    c ∈ directedChildren nodes parent ↔
      nodes c = true ∧ S.directed parent c = true := by
  constructor
  · intro h
    have parts := List.mem_filter.mp h
    exact ⟨(NodeSet.mem_members_iff nodes c).mp parts.1, parts.2⟩
  · intro h
    exact List.mem_filter.mpr
      ⟨(NodeSet.mem_members_iff nodes c).mpr h.1, h.2⟩

theorem some_mem_childOptions_of_directed (nodes : NodeSet S)
    (parent c : Fin S.count)
    (hc : c ∈ directedChildren nodes parent) :
    some c ∈ childOptions nodes parent := by
  refine List.mem_cons.mpr (Or.inr ?_)
  exact List.mem_map.mpr ⟨c, hc, rfl⟩

/--
A well-formed assignment at a selected parent is one of the finitely many
values the extractor tries: `none`, or a directed child still in `nodes`.
-/
theorem child_mem_childOptions_of_wellFormed (nodes : NodeSet S)
    (child : ForestChild S) (parent : Fin S.count)
    (hwell : childWellFormedBool nodes child = true)
    (_hp : nodes parent = true) :
    child parent ∈ childOptions nodes parent := by
  cases hc : child parent with
  | none =>
      exact none_mem_childOptions nodes parent
  | some c =>
      have hedge := childWellFormed_edge nodes child hwell (by rw [hc])
      have mem : c ∈ directedChildren nodes parent :=
        (mem_directedChildren_iff nodes parent c).mpr ⟨hedge.2.1, hedge.2.2⟩
      simpa [hc] using some_mem_childOptions_of_directed nodes parent c mem

/--
Small-side search: subsets of `pending`, intended to be the members of
`large \ X`, tested against a fixed large child map.
-/
def findHedgeSmall (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S)
    (pending : List (Fin S.count)) (acc : NodeSet S) :
    Option (NodeSet S) :=
  findSubset pending acc (fun small => smallForestReady G q large child small)

/--
Child-map search on a fixed large vertex set: for each remaining parent,
try `none` then each directed child in `large`.  After every parent is
assigned, search child-closed small subsets of `large \ X`.
-/
def findChildAndSmall (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (pending : List (Fin S.count)) (acc : ForestChild S) :
    Option (HedgeSelection S) :=
  match pending with
  | [] =>
      if largeChildReady G q large acc then
        match findHedgeSmall G q large acc
            (NodeSet.members (NodeSet.diff large q.action)) NodeSet.empty with
        | some small => some ⟨large, small, acc⟩
        | none => none
      else
        none
  | parent :: rest =>
      firstSome (childOptions large parent) (fun value =>
        findChildAndSmall G q large rest (setChild acc parent value))

/--
Large-side vertex search: subsets of `pending`, intended to be the members
of `fail.remaining`.  For each completed large vertex set that is a
c-component meeting `X`, search child maps and then small subsets.
-/
def findHedgePair (G : ObservedGraph S) (q : JointKernelQuery S)
    (pending : List (Fin S.count)) (acc : NodeSet S) :
    Option (HedgeSelection S) :=
  match pending with
  | [] =>
      if largeVerticesReady G q acc then
        findChildAndSmall G q acc (NodeSet.members acc) (emptyChild S)
      else
        none
  | node :: rest =>
      match findHedgePair G q rest (NodeSet.insert acc node) with
      | some sel => some sel
      | none => findHedgePair G q rest acc

/--
Most general finite extractor from ID-failure data: vertex selections inside
`remaining`, kept children among induced directed edges, and child-closed
selections inside `large \ X`.
-/
def findHedgeWitnessSets (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) : Option (HedgeSelection S) :=
  findHedgePair G q (NodeSet.members fail.remaining) NodeSet.empty

theorem findSubset_spec (pending : List (Fin S.count)) (acc : NodeSet S)
    (p : NodeSet S -> Bool) {found : NodeSet S}
    (h : findSubset pending acc p = some found) : p found = true := by
  induction pending generalizing acc found with
  | nil =>
      simp [findSubset] at h
      rcases h with ⟨hp, hEq⟩
      subst hEq
      exact hp
  | cons node rest ih =>
      simp [findSubset] at h
      cases hinc : findSubset rest (NodeSet.insert acc node) p with
      | some s =>
          simp [hinc] at h
          subst h
          exact ih (NodeSet.insert acc node) hinc
      | none =>
          simp [hinc] at h
          exact ih acc h

theorem firstSome_eq_some {α β : Type _} (xs : List α)
    (f : α -> Option β) {found : β}
    (h : firstSome xs f = some found) :
    Exists fun a => f a = some found := by
  induction xs with
  | nil => simp [firstSome] at h
  | cons a rest ih =>
      simp [firstSome] at h
      cases ha : f a with
      | some b =>
          simp [ha] at h
          exact ⟨a, by simp [ha, h]⟩
      | none =>
          simp [ha] at h
          exact ih h

/--
If some listed argument already maps to `some`, the left-to-right scan
returns a success.  The returned value need not be that argument's image:
an earlier success is kept.  Completeness of the hedge extractor only
needs `isSome`.
-/
theorem firstSome_eq_some_of_mem {α β : Type _} :
    forall (xs : List α) (f : α -> Option β) {a : α} {b : β},
      a ∈ xs -> f a = some b ->
        Exists fun found => firstSome xs f = some found := by
  intro xs f a b mem ha
  induction xs with
  | nil =>
      cases mem
  | cons x rest ih =>
      cases hx : f x with
      | some found =>
          exact ⟨found, by simp [firstSome, hx]⟩
      | none =>
          have memRest : a ∈ rest := by
            rcases List.mem_cons.mp mem with hEq | hRest
            · subst hEq
              rw [ha] at hx
              cases hx
            · exact hRest
          rcases ih memRest with ⟨found, hf⟩
          exact ⟨found, by simp [firstSome, hx, hf]⟩

theorem findHedgeSmall_ready
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S)
    (pending : List (Fin S.count)) (acc small : NodeSet S)
    (h : findHedgeSmall G q large child pending acc = some small) :
    smallForestReady G q large child small = true :=
  findSubset_spec pending acc _ h

theorem findChildAndSmall_tests
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (pending : List (Fin S.count)) (acc : ForestChild S)
    {sel : HedgeSelection S}
    (h : findChildAndSmall G q large pending acc = some sel) :
    sel.large = large ∧
      largeChildReady G q large sel.child = true ∧
        smallForestReady G q large sel.child sel.small = true := by
  induction pending generalizing acc sel with
  | nil =>
      simp [findChildAndSmall] at h
      rcases h with ⟨hchild, hmatch⟩
      cases hs : findHedgeSmall G q large acc
          (NodeSet.members (NodeSet.diff large q.action)) NodeSet.empty with
      | none => simp [hs] at hmatch
      | some s =>
          simp [hs] at hmatch
          have hready :=
            findHedgeSmall_ready G q large acc
              (NodeSet.members (NodeSet.diff large q.action)) NodeSet.empty s hs
          subst hmatch
          exact ⟨rfl, hchild, hready⟩
  | cons parent rest ih =>
      simp [findChildAndSmall] at h
      rcases firstSome_eq_some _ _ h with ⟨value, hval⟩
      exact ih (setChild acc parent value) hval

theorem findHedgePair_tests
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (pending : List (Fin S.count)) (acc : NodeSet S)
    {sel : HedgeSelection S}
    (h : findHedgePair G q pending acc = some sel) :
    hedgeTestsHold G q sel = true := by
  induction pending generalizing acc sel with
  | nil =>
      simp [findHedgePair] at h
      rcases h with ⟨hverts, hrest⟩
      have hparts := findChildAndSmall_tests G q acc _ (emptyChild S) hrest
      simp [hedgeTestsHold, hparts.1, hverts, hparts.2.1, hparts.2.2]
  | cons node rest ih =>
      simp [findHedgePair] at h
      cases hinc : findHedgePair G q rest (NodeSet.insert acc node) with
      | some found =>
          simp [hinc] at h
          subst h
          exact ih (NodeSet.insert acc node) hinc
      | none =>
          simp [hinc] at h
          exact ih acc h

theorem findHedgeWitnessSets_tests
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {sel : HedgeSelection S}
    (h : findHedgeWitnessSets G q fail = some sel) :
    hedgeTestsHold G q sel = true :=
  findHedgePair_tests G q _ NodeSet.empty h

/-! ## Completeness of the finite hedge extractor -/

/--
If a known assignment of the pending vertices already passes `p`, the
include-then-skip scan returns some success.  The success need not be
that assignment: an earlier include-branch hit is kept.
-/
theorem findSubset_eq_some_of_extends
    (pending : List (Fin S.count)) (acc found : NodeSet S)
    (p : NodeSet S -> Bool)
    (hx : ExtendsAcc pending acc found)
    (hp : p found = true) :
    Exists fun result => findSubset pending acc p = some result := by
  induction pending generalizing acc with
  | nil =>
      have eq : acc = found := extendsAcc_nil hx
      have hpAcc : p acc = true := by simpa [eq] using hp
      exact ⟨acc, by simp [findSubset, hpAcc]⟩
  | cons node rest ih =>
      cases hf : found node with
      | false =>
          cases hinc : findSubset rest (NodeSet.insert acc node) p with
          | some result =>
              exact ⟨result, by simp [findSubset, hinc]⟩
          | none =>
              rcases ih acc (extendsAcc_cons_skip hx hf) with ⟨result, hr⟩
              exact ⟨result, by simp [findSubset, hinc, hr]⟩
      | true =>
          rcases ih (NodeSet.insert acc node)
              (extendsAcc_cons_insert hx hf) with ⟨result, hr⟩
          exact ⟨result, by simp [findSubset, hr]⟩

theorem hedgeTestsHold_iff
    (G : ObservedGraph S) (q : JointKernelQuery S) (sel : HedgeSelection S) :
    hedgeTestsHold G q sel = true ↔
      largeVerticesReady G q sel.large = true ∧
        largeChildReady G q sel.large sel.child = true ∧
          smallForestReady G q sel.large sel.child sel.small = true := by
  constructor
  · intro h
    have outer := Bool.and_eq_true_iff.mp h
    have inner := Bool.and_eq_true_iff.mp outer.1
    exact ⟨inner.1, inner.2, outer.2⟩
  · intro h
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨h.1, h.2.1⟩, h.2.2⟩

theorem largeChildReady_wellFormed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S)
    (h : largeChildReady G q large child = true) :
    childWellFormedBool large child = true :=
  (Bool.and_eq_true_iff.mp h).1

/--
A small-side test already implies the selection is an include/skip
assignment of `large \ X`.
-/
theorem extendsAcc_of_smallForestReady
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (child : ForestChild S) (small : NodeSet S)
    (h : smallForestReady G q large child small = true) :
    ExtendsAcc (NodeSet.members (NodeSet.diff large q.action))
      NodeSet.empty small := by
  have e := Bool.and_eq_true_iff.mp h
  have d := Bool.and_eq_true_iff.mp e.1
  have c := Bool.and_eq_true_iff.mp d.1
  have b := Bool.and_eq_true_iff.mp c.1
  have subset : NodeSet.Subset small large :=
    (NodeSet.subsetBool_eq_true_iff small large).mp b.2
  have disjoint : NodeSet.Disjoint small q.action :=
    (NodeSet.disjointBool_eq_true_iff small q.action).mp c.2
  exact extendsAcc_empty_of_subset
    (NodeSet.Subset.diff_of_subset_disjoint subset disjoint)

/--
A completed child map `target` extends `acc` along `pending`: they agree
off the remaining parents, and every remaining parent is assigned a value
from `childOptions large`.
-/
def ChildExtends (large : NodeSet S) (pending : List (Fin S.count))
    (acc target : ForestChild S) : Prop :=
  (forall i, i ∉ pending -> acc i = target i) ∧
    (forall parent, parent ∈ pending ->
      target parent ∈ childOptions large parent)

theorem childExtends_setChild
    {large : NodeSet S} {parent : Fin S.count}
    {rest : List (Fin S.count)} {acc target : ForestChild S}
    (h : ChildExtends large (parent :: rest) acc target) :
    ChildExtends large rest (setChild acc parent (target parent))
      target := by
  constructor
  · intro i hi
    if heq : i = parent then
      subst i
      exact setChild_self acc parent (target parent)
    else
      have notPending : i ∉ parent :: rest := by
        intro hp
        rcases List.mem_cons.mp hp with hEq | hRest
        · exact heq hEq
        · exact hi hRest
      have agree := h.1 i notPending
      simp [setChild, heq]
      exact agree
  · intro p hp
    exact h.2 p (List.mem_cons.mpr (Or.inr hp))

theorem childExtends_members_empty
    (large : NodeSet S) (child : ForestChild S)
    (hwell : childWellFormedBool large child = true) :
    ChildExtends large (NodeSet.members large) (emptyChild S) child := by
  constructor
  · intro i hi
    have off : large i = false := by
      cases hL : large i with
      | false => rfl
      | true =>
          exact False.elim (hi ((NodeSet.mem_members_iff large i).mpr hL))
    have hnone : child i = none :=
      childWellFormed_off large child hwell off
    simp [emptyChild, hnone]
  · intro parent hp
    exact child_mem_childOptions_of_wellFormed large child parent hwell
      ((NodeSet.mem_members_iff large parent).mp hp)

/--
Child-map search is complete for well-formed maps: if the remaining
parents of a known target still lie in `childOptions`, and some small
side of `large \ X` already passes, the scan returns a selection.
-/
theorem findChildAndSmall_eq_some_of_extends
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (large : NodeSet S) (pending : List (Fin S.count))
    (acc target : ForestChild S) (small : NodeSet S)
    (hx : ChildExtends large pending acc target)
    (hchild : largeChildReady G q large target = true)
    (hsmallExt : ExtendsAcc
      (NodeSet.members (NodeSet.diff large q.action)) NodeSet.empty small)
    (hsmallReady : smallForestReady G q large target small = true) :
    Exists fun sel => findChildAndSmall G q large pending acc = some sel := by
  induction pending generalizing acc with
  | nil =>
      have accEq : acc = target := by
        funext i
        exact hx.1 i (fun h => by cases h)
      have hready : largeChildReady G q large acc = true := by
        simpa [accEq] using hchild
      have hsmallReadyAcc :
          smallForestReady G q large acc small = true := by
        simpa [accEq] using hsmallReady
      rcases findSubset_eq_some_of_extends
          (NodeSet.members (NodeSet.diff large q.action))
          NodeSet.empty small
          (fun s => smallForestReady G q large acc s)
          hsmallExt hsmallReadyAcc with ⟨found, hf⟩
      refine ⟨⟨large, found, acc⟩, ?_⟩
      simp [findChildAndSmall, hready, findHedgeSmall, hf]
  | cons parent rest ih =>
      have hmem : target parent ∈ childOptions large parent :=
        hx.2 parent List.mem_cons_self
      rcases ih (setChild acc parent (target parent))
          (childExtends_setChild hx) with ⟨sel, hs⟩
      rcases firstSome_eq_some_of_mem (childOptions large parent)
          (fun value =>
            findChildAndSmall G q large rest (setChild acc parent value))
          hmem hs with ⟨found, hf⟩
      exact ⟨found, by simp [findChildAndSmall, hf]⟩

/--
Vertex search is complete for any selection whose large side extends the
accumulator along `pending` and whose tests already pass.
-/
theorem findHedgePair_eq_some_of_extends
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (pending : List (Fin S.count)) (acc : NodeSet S)
    (sel : HedgeSelection S)
    (hlarge : ExtendsAcc pending acc sel.large)
    (htests : hedgeTestsHold G q sel = true) :
    Exists fun found => findHedgePair G q pending acc = some found := by
  induction pending generalizing acc with
  | nil =>
      have accEq : acc = sel.large := extendsAcc_nil hlarge
      have parts := (hedgeTestsHold_iff G q sel).mp htests
      have hverts : largeVerticesReady G q acc = true := by
        simpa [accEq] using parts.1
      have hwell :
          childWellFormedBool sel.large sel.child = true :=
        largeChildReady_wellFormed G q sel.large sel.child parts.2.1
      have hchildAcc : largeChildReady G q acc sel.child = true := by
        simpa [accEq] using parts.2.1
      have hsmallReadyAcc :
          smallForestReady G q acc sel.child sel.small = true := by
        simpa [accEq] using parts.2.2
      have hxChild : ChildExtends acc (NodeSet.members acc)
          (emptyChild S) sel.child := by
        simpa [accEq] using
          childExtends_members_empty sel.large sel.child hwell
      have hsmallExt : ExtendsAcc
          (NodeSet.members (NodeSet.diff acc q.action))
          NodeSet.empty sel.small := by
        simpa [accEq] using
          extendsAcc_of_smallForestReady G q sel.large sel.child
            sel.small parts.2.2
      rcases findChildAndSmall_eq_some_of_extends G q acc
          (NodeSet.members acc) (emptyChild S) sel.child sel.small
          hxChild hchildAcc hsmallExt hsmallReadyAcc with ⟨found, hf⟩
      exact ⟨found, by simp [findHedgePair, hverts, hf]⟩
  | cons node rest ih =>
      cases hf : sel.large node with
      | true =>
          rcases ih (NodeSet.insert acc node)
              (extendsAcc_cons_insert hlarge hf) with ⟨found, hr⟩
          exact ⟨found, by simp [findHedgePair, hr]⟩
      | false =>
          cases hinc :
              findHedgePair G q rest (NodeSet.insert acc node) with
          | some found =>
              exact ⟨found, by simp [findHedgePair, hinc]⟩
          | none =>
              rcases ih acc (extendsAcc_cons_skip hlarge hf) with
                ⟨found, hr⟩
              exact ⟨found, by simp [findHedgePair, hinc, hr]⟩

/--
The hedge extractor returns a selection whenever some enumerated
candidate — a subset of `remaining`, a well-formed child map, and a
child-closed subset of `large \ X` — already passes the Boolean hedge
tests.  Returning `none` therefore means no such enumerated candidate
exists, not merely that greedy thinning failed.
-/
theorem findHedgeWitnessSets_eq_some_of_selection
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) (sel : HedgeSelection S)
    (hlarge : NodeSet.Subset sel.large fail.remaining)
    (htests : hedgeTestsHold G q sel = true) :
    Exists fun found => findHedgeWitnessSets G q fail = some found := by
  rcases findHedgePair_eq_some_of_extends G q
      (NodeSet.members fail.remaining) NodeSet.empty sel
      (extendsAcc_empty_of_subset hlarge) htests with ⟨found, hf⟩
  exact ⟨found, by simpa [findHedgeWitnessSets] using hf⟩

/--
Result of one executable ID run.

* `identified` carries an observational expression for `P(outcome | do(action))`.
* `failed` is ID's hedge branch: `C(G) = {G}` and `C(G \ X) = {S}`, with the
  working sets needed to thin a `HedgeWitness`.
* `unfinished` is an implementation sentinel, not a third mathematical case.
-/
inductive IdentificationOutcome (S : ObservedSignature) where
  | identified : ProbabilityTerm S -> IdentificationOutcome S
  | failed : IdentificationFail S -> IdentificationOutcome S
  | unfinished : IdentificationOutcome S

namespace IdentificationOutcome

/--
Walk a list of factor runs, accumulating successful observational terms.
A hedge or sentinel in the list aborts the product.
-/
def collect (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S) :
    List (IdentificationOutcome S) -> List (ProbabilityTerm S) ->
      IdentificationOutcome S
  | [], acc => identified (assemble acc.reverse)
  | identified term :: rest, acc => collect assemble rest (term :: acc)
  | failed seed :: _, _acc => failed seed
  | unfinished :: _, _acc => unfinished

/-- Combine factor runs: one hedge fails the product; one sentinel aborts. -/
def combine (outcomes : List (IdentificationOutcome S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S) :
    IdentificationOutcome S :=
  collect assemble outcomes []

theorem collect_eq_failed
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (pending : List (IdentificationOutcome S))
    (acc : List (ProbabilityTerm S)) {fail : IdentificationFail S}
    (h : collect assemble pending acc = failed fail) :
    failed fail ∈ pending := by
  induction pending generalizing acc with
  | nil =>
      simp [collect] at h
  | cons head rest ih =>
      cases head with
      | identified t =>
          simp [collect] at h
          exact List.mem_cons.mpr (Or.inr (ih (t :: acc) h))
      | failed seed =>
          simp [collect] at h
          subst h
          exact List.mem_cons.mpr (Or.inl rfl)
      | unfinished =>
          simp [collect] at h

theorem combine_eq_failed
    (outcomes : List (IdentificationOutcome S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : combine outcomes assemble = failed fail) :
    failed fail ∈ outcomes :=
  collect_eq_failed assemble outcomes [] h

/--
A successful product collects one observational term from every factor.
The assembled formula is `assemble` applied to those terms in list order.
-/
theorem collect_eq_identified
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (pending : List (IdentificationOutcome S))
    (acc : List (ProbabilityTerm S)) {term : ProbabilityTerm S}
    (h : collect assemble pending acc = identified term) :
    Exists fun terms =>
      pending = terms.map identified ∧
        term = assemble (acc.reverse ++ terms) := by
  induction pending generalizing acc term with
  | nil =>
      simp [collect] at h
      refine ⟨[], rfl, ?_⟩
      simpa using h.symm
  | cons head rest ih =>
      cases head with
      | identified t =>
          simp [collect] at h
          rcases ih (t :: acc) h with ⟨terms, hrest, hterm⟩
          refine ⟨t :: terms, ?_, ?_⟩
          · simp [hrest]
          · simpa [List.reverse_cons, List.append_assoc] using hterm
      | failed _seed =>
          simp [collect] at h
      | unfinished =>
          simp [collect] at h

theorem combine_eq_identified
    (outcomes : List (IdentificationOutcome S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    {term : ProbabilityTerm S}
    (h : combine outcomes assemble = identified term) :
    Exists fun terms =>
      outcomes = terms.map identified ∧
        term = assemble terms := by
  rcases collect_eq_identified assemble outcomes [] h with ⟨terms, hpending, hterm⟩
  exact ⟨terms, hpending, by simpa using hterm⟩

end IdentificationOutcome

/--
Fuel for ID.  Each recursive call consumes one unit; ancestral restriction,
c-component splits, and the proper-subset step together cannot exceed a cubic
bound in `|V|` on a finite DAG.
-/
def identificationFuel (S : ObservedSignature) : Nat :=
  Nat.succ (S.count * Nat.succ S.count * Nat.succ S.count)

theorem identificationFuel_pos (S : ObservedSignature) :
    0 < identificationFuel S :=
  Nat.succ_pos _

/-- Observational joint `P(V)` as a kernel with empty action. -/
def observationalJointTerm (S : ObservedSignature) : ProbabilityTerm S :=
  .kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩

/--
The unit of the probability-term product: the empty-outcome kernel, which
denotes the sure event.
-/
def unitProbabilityTerm (S : ObservedSignature) : ProbabilityTerm S :=
  .kernel ⟨NodeSet.empty, NodeSet.empty, NodeSet.empty⟩

def productTerms : List (ProbabilityTerm S) -> ProbabilityTerm S
  | [] => unitProbabilityTerm S
  | [term] => term
  | term :: rest => .multiply term (productTerms rest)

theorem unitProbabilityTerm_actionFree (S : ObservedSignature) :
    (unitProbabilityTerm S).ActionFree := by
  intro _i
  rfl

theorem observationalJointTerm_actionFree (S : ObservedSignature) :
    (observationalJointTerm S).ActionFree := by
  intro _i
  rfl

theorem productTerms_actionFree (terms : List (ProbabilityTerm S))
    (h : forall t, t ∈ terms -> t.ActionFree) :
    (productTerms terms).ActionFree := by
  induction terms with
  | nil => exact unitProbabilityTerm_actionFree S
  | cons t rest ih =>
      cases rest with
      | nil =>
          simpa [productTerms] using h t (by simp)
      | cons t2 rest2 =>
          refine ⟨h t (by simp), ?_⟩
          exact ih (fun u hu =>
            h u (List.mem_cons.mpr (Or.inr hu)))

/-- Nonempty tail: `productTerms` is later-first multiply, matching
`DoCalculusDerivation.chain`. -/
theorem productTerms_cons (t : ProbabilityTerm S)
    (rest : List (ProbabilityTerm S)) (hne : rest ≠ []) :
    productTerms (t :: rest) = .multiply t (productTerms rest) := by
  cases rest with
  | nil => exact (hne rfl).elim
  | cons _s _rest => rfl

/--
Chain-rule conditioner for `node`: every topologically earlier vertex that
still belongs to the current remaining set.  Signature nodes are already
topologically numbered by `directed_earlier`.
-/
def chainCondition (remaining : NodeSet S) (node : Fin S.count) : NodeSet S :=
  fun j => remaining j && decide (j.val < node.val)

/-- Extra topological predecessors of `node` that are not already in
the observed action.  Rule 1 inserts this block into `P(Y | X)` to
recover the chain-rule conditioner. -/
def extraPredecessors (remaining : NodeSet S) (node : Fin S.count)
    (action : NodeSet S) : NodeSet S :=
  NodeSet.diff (chainCondition remaining node) action

theorem disjoint_singleton_chainCondition (remaining : NodeSet S)
    (node : Fin S.count) :
    NodeSet.Disjoint (NodeSet.singleton node)
      (chainCondition remaining node) := by
  intro i hi
  have heq : i = node := (NodeSet.singleton_eq_true_iff node i).mp hi
  simp [chainCondition, heq]

theorem extraPredecessors_union_eq
    {remaining action : NodeSet S} {node : Fin S.count}
    (hsubset : NodeSet.Subset action (chainCondition remaining node)) :
    NodeSet.union (extraPredecessors remaining node action) action =
      chainCondition remaining node :=
  NodeSet.diff_union_eq hsubset

/-- Immediate topological predecessor of a positive-index vertex. -/
def predIndex {S : ObservedSignature} (j : Fin S.count) (h : 0 < j.val) :
    Fin S.count :=
  ⟨j.val - 1, by
    have hlt : j.val - 1 < j.val := Nat.sub_lt h Nat.zero_lt_one
    exact Nat.lt_trans hlt j.isLt⟩

theorem predIndex_val {S : ObservedSignature} (j : Fin S.count)
    (h : 0 < j.val) :
    (predIndex j h).val + 1 = j.val :=
  Nat.succ_pred_eq_of_pos h

theorem predIndex_ne {S : ObservedSignature} (j : Fin S.count)
    (h : 0 < j.val) :
    predIndex j h ≠ j := by
  intro heq
  have hlt : (predIndex j h).val < j.val :=
    Nat.sub_lt h Nat.zero_lt_one
  have hval : (predIndex j h).val = j.val := congrArg Fin.val heq
  exact Nat.lt_irrefl _ (hval ▸ hlt)

theorem predIndex_lt {S : ObservedSignature} (j : Fin S.count)
    (h : 0 < j.val) :
    (predIndex j h).val < j.val :=
  Nat.sub_lt h Nat.zero_lt_one

/-- A later vertex is disjoint from the chain-rule conditioner of an
earlier one: topological numbering forbids `j.val < i.val`. -/
theorem disjoint_later_chainCondition (remaining : NodeSet S)
    {i j : Fin S.count} (hlt : i.val < j.val) :
    NodeSet.Disjoint (NodeSet.singleton j) (chainCondition remaining i) := by
  intro k hk
  have heq : k = j := (NodeSet.singleton_eq_true_iff j k).mp hk
  have hnlt : ¬ j.val < i.val := Nat.not_lt.mpr (Nat.le_of_lt hlt)
  simp [chainCondition, heq, decide_eq_false hnlt]

/-- For consecutive indices, `Pa_V(j) = {i} ∪ Pa_V(i)`. -/
theorem chainCondition_predIndex {S : ObservedSignature}
    (j : Fin S.count) (h : 0 < j.val) :
    chainCondition NodeSet.full j =
      NodeSet.union (NodeSet.singleton (predIndex j h))
        (chainCondition NodeSet.full (predIndex j h)) := by
  funext k
  let i := predIndex j h
  have hilt : i.val < j.val := predIndex_lt j h
  have hi : i.val + 1 = j.val := predIndex_val j h
  simp [chainCondition, NodeSet.union, NodeSet.singleton, NodeSet.full]
  cases hlt : decide (k.val < i.val) with
  | true =>
      have hk : k.val < i.val := of_decide_eq_true hlt
      have hkj : k.val < j.val := Nat.lt_trans hk hilt
      simp [decide_eq_true hkj]
  | false =>
      cases heq : decide (k = i) with
      | true =>
          have hk : k = i := of_decide_eq_true heq
          have hkj : k.val < j.val := hk ▸ hilt
          simp [decide_eq_true hkj]
      | false =>
          have hne : k ≠ i := of_decide_eq_false heq
          have hnlt : ¬ k.val < i.val := of_decide_eq_false hlt
          have hge : i.val ≤ k.val := Nat.not_lt.mp hnlt
          have hneVal : k.val ≠ i.val := fun hv =>
            hne (Fin.eq_of_val_eq hv)
          have hgt : i.val < k.val :=
            Nat.lt_of_le_of_ne hge (Ne.symm hneVal)
          have hgej : j.val ≤ k.val := by
            have : Nat.succ i.val ≤ k.val := Nat.succ_le_of_lt hgt
            simpa [hi] using this
          have hnltj : ¬ k.val < j.val := Nat.not_lt.mpr hgej
          simp [decide_eq_false hnltj]

theorem predIndex_pos_of_two {S : ObservedSignature} (j : Fin S.count)
    (h1 : 1 < j.val) :
    0 < (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)).val := by
  simpa [predIndex] using Nat.sub_pos_of_lt h1

/-- Two-step topological predecessor of a vertex with index at least 2. -/
def predIndex2 {S : ObservedSignature} (j : Fin S.count) (h1 : 1 < j.val) :
    Fin S.count :=
  predIndex (predIndex j (Nat.lt_trans Nat.zero_lt_one h1))
    (predIndex_pos_of_two j h1)

theorem predIndex2_lt {S : ObservedSignature} (j : Fin S.count)
    (h1 : 1 < j.val) :
    (predIndex2 j h1).val <
      (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)).val :=
  predIndex_lt _ (predIndex_pos_of_two j h1)

/-- For two consecutive steps, `Pa_V(j) = {i} ∪ {k} ∪ Pa_V(k)`. -/
theorem chainCondition_predIndex2 {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    chainCondition NodeSet.full j =
      NodeSet.union
        (NodeSet.singleton (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)))
        (NodeSet.union (NodeSet.singleton (predIndex2 j h1))
          (chainCondition NodeSet.full (predIndex2 j h1))) := by
  have hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  have hi := chainCondition_predIndex j hpos
  have hk := chainCondition_predIndex
    (predIndex j hpos) (predIndex_pos_of_two j h1)
  calc
    chainCondition NodeSet.full j =
      NodeSet.union (NodeSet.singleton (predIndex j hpos))
        (chainCondition NodeSet.full (predIndex j hpos)) := hi
    _ = NodeSet.union (NodeSet.singleton (predIndex j hpos))
          (NodeSet.union (NodeSet.singleton (predIndex2 j h1))
            (chainCondition NodeSet.full (predIndex2 j h1))) := by
        have hdef : predIndex2 j h1 =
            predIndex (predIndex j hpos) (predIndex_pos_of_two j h1) :=
          rfl
        rw [hdef, hk]

/-- n-step topological predecessor: `predIndexNth j 0 = j`,
`predIndexNth j 1 = predIndex j`, `predIndexNth j 2 = predIndex2`.
The bound `n ≤ j.val` is data, so the inhabitant is a `Fin` without
searching for a predecessor. -/
def predIndexNth {S : ObservedSignature} (j : Fin S.count) (n : Nat)
    (_h : n ≤ j.val) : Fin S.count :=
  ⟨j.val - n, Nat.lt_of_le_of_lt (Nat.sub_le j.val n) j.isLt⟩

theorem predIndexNth_val {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (_h : n ≤ j.val) :
    (predIndexNth j n _h).val = j.val - n :=
  rfl

theorem predIndexNth_zero {S : ObservedSignature} (j : Fin S.count) :
    predIndexNth j 0 (Nat.zero_le j.val) = j :=
  Fin.eq_of_val_eq (by simp [predIndexNth])

theorem predIndexNth_one {S : ObservedSignature} (j : Fin S.count)
    (h : 1 ≤ j.val) :
    predIndexNth j 1 h = predIndex j (Nat.lt_of_succ_le h) :=
  Fin.eq_of_val_eq (by simp [predIndexNth, predIndex])

theorem predIndexNth_two {S : ObservedSignature} (j : Fin S.count)
    (h : 2 ≤ j.val) :
    predIndexNth j 2 h = predIndex2 j (Nat.lt_of_succ_le h) :=
  Fin.eq_of_val_eq (by
    simp [predIndexNth, predIndex2, predIndex]
    omega)

/-- The next predecessor is one `predIndex` step from the current
n-step predecessor, once `n + 1 ≤ j.val` so that step is still in
range. -/
theorem predIndexNth_succ {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (h : n + 1 ≤ j.val) :
    predIndexNth j (n + 1) h =
      predIndex
        (predIndexNth j n (Nat.le_trans (Nat.le_succ n) h))
        (by
          have hlt : n < j.val := Nat.lt_of_succ_le h
          simpa [predIndexNth] using Nat.sub_pos_of_lt hlt) :=
  Fin.eq_of_val_eq (by
    simp [predIndexNth, predIndex]
    omega)

/-- The n immediate topological predecessors of `j`, nearest first. -/
def consecutivePredList {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (h : n ≤ j.val) : List (Fin S.count) :=
  List.ofFn fun i : Fin n =>
    predIndexNth j (i.val + 1)
      (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le i.isLt h))

/-- Vertices summed off a consecutive n-step chain factorization. -/
def consecutiveSummed {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (h : n ≤ j.val) : NodeSet S :=
  (consecutivePredList j n h).foldl
    (fun acc node => NodeSet.union acc (NodeSet.singleton node))
    NodeSet.empty

theorem consecutivePredList_zero {S : ObservedSignature}
    (j : Fin S.count) :
    consecutivePredList j 0 (Nat.zero_le j.val) = [] :=
  List.ofFn_zero

theorem consecutiveSummed_zero {S : ObservedSignature}
    (j : Fin S.count) :
    consecutiveSummed j 0 (Nat.zero_le j.val) = NodeSet.empty := by
  simp [consecutiveSummed, consecutivePredList_zero]

theorem consecutivePredList_one {S : ObservedSignature}
    (j : Fin S.count) (h : 1 ≤ j.val) :
    consecutivePredList j 1 h = [predIndex j (Nat.lt_of_succ_le h)] := by
  unfold consecutivePredList
  rw [List.ofFn_succ, List.ofFn_zero]
  simp [predIndexNth_one]

theorem consecutiveSummed_one {S : ObservedSignature}
    (j : Fin S.count) (h : 1 ≤ j.val) :
    consecutiveSummed j 1 h =
      NodeSet.singleton (predIndex j (Nat.lt_of_succ_le h)) := by
  simp [consecutiveSummed, consecutivePredList_one, List.foldl,
    NodeSet.union_empty_left]

theorem consecutivePredList_two {S : ObservedSignature}
    (j : Fin S.count) (h : 2 ≤ j.val) :
    consecutivePredList j 2 h =
      [predIndex j (Nat.lt_of_succ_le (Nat.le_trans (Nat.le_succ 1) h)),
        predIndex2 j (Nat.lt_of_succ_le h)] := by
  have h1 : 1 ≤ j.val := Nat.le_trans (Nat.le_succ 1) h
  unfold consecutivePredList
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp [predIndexNth_one (h := h1), predIndexNth_two (h := h)]

theorem consecutiveSummed_two {S : ObservedSignature}
    (j : Fin S.count) (h : 2 ≤ j.val) :
    consecutiveSummed j 2 h =
      NodeSet.union
        (NodeSet.singleton
          (predIndex j (Nat.lt_of_succ_le (Nat.le_trans (Nat.le_succ 1) h))))
        (NodeSet.singleton (predIndex2 j (Nat.lt_of_succ_le h))) := by
  simp [consecutiveSummed, consecutivePredList_two, List.foldl,
    NodeSet.union_empty_left]

theorem foldl_union_singleton_left {S : ObservedSignature}
    (X : NodeSet S) (nodes : List (Fin S.count)) :
    nodes.foldl
        (fun acc node => NodeSet.union acc (NodeSet.singleton node)) X =
      NodeSet.union X
        (nodes.foldl
          (fun acc node => NodeSet.union acc (NodeSet.singleton node))
          NodeSet.empty) := by
  induction nodes generalizing X with
  | nil =>
      simp [List.foldl, NodeSet.union_empty_right]
  | cons n ns ih =>
      simp only [List.foldl]
      rw [ih]
      rw [NodeSet.union_empty_left]
      rw [ih (X := NodeSet.singleton n)]
      exact NodeSet.union_assoc _ _ _

theorem foldl_union_singleton_cons {S : ObservedSignature}
    (head : Fin S.count) (tail : List (Fin S.count)) :
    (head :: tail).foldl
        (fun acc node => NodeSet.union acc (NodeSet.singleton node))
        NodeSet.empty =
      NodeSet.union (NodeSet.singleton head)
        (tail.foldl
          (fun acc node => NodeSet.union acc (NodeSet.singleton node))
          NodeSet.empty) := by
  simp only [List.foldl]
  rw [NodeSet.union_empty_left, foldl_union_singleton_left]

theorem one_le_of_succ_le {n jval : Nat} (h : n + 1 ≤ jval) : 1 ≤ jval :=
  Nat.le_trans (Nat.succ_le_succ (Nat.zero_le n)) h

theorem predIndexNth_lt_of_pos {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) (hn : 0 < n) :
    (predIndexNth j n h).val < j.val := by
  have hj : 0 < j.val := Nat.lt_of_lt_of_le hn h
  simpa [predIndexNth] using Nat.sub_lt hj hn

theorem consecutivePredList_succ {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    consecutivePredList j (n + 1) h =
      predIndexNth j 1 (one_le_of_succ_le h) ::
        consecutivePredList
          (predIndexNth j 1 (one_le_of_succ_le h)) n
          (by
            simpa [predIndexNth] using
              Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)) := by
  unfold consecutivePredList
  rw [List.ofFn_succ]
  refine congr (congrArg List.cons ?_) ?_
  · apply Fin.eq_of_val_eq
    simp [predIndexNth]
  · congr 1
    funext i
    apply Fin.eq_of_val_eq
    simp [predIndexNth, Fin.succ]
    omega

theorem consecutiveSummed_succ {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    consecutiveSummed j (n + 1) h =
      NodeSet.union
        (NodeSet.singleton (predIndexNth j 1 (one_le_of_succ_le h)))
        (consecutiveSummed
          (predIndexNth j 1 (one_le_of_succ_le h)) n
          (by
            simpa [predIndexNth] using
              Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h))) := by
  unfold consecutiveSummed
  rw [consecutivePredList_succ]
  simp only [List.foldl]
  rw [NodeSet.union_empty_left, foldl_union_singleton_left]

theorem consecutiveSummed_of_zero {S : ObservedSignature}
    (j : Fin S.count) (h : 0 ≤ j.val) :
    consecutiveSummed j 0 h = NodeSet.empty := by
  simp [consecutiveSummed, consecutivePredList, List.ofFn_zero]

theorem predIndexNth_eq_zero {S : ObservedSignature}
    (j : Fin S.count) (h : 0 ≤ j.val) :
    predIndexNth j 0 h = j :=
  Fin.eq_of_val_eq (by simp [predIndexNth])

/-- `j` together with its n topological predecessors. -/
def consecutiveInterval {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (h : n ≤ j.val) : NodeSet S :=
  NodeSet.union (NodeSet.singleton j) (consecutiveSummed j n h)

theorem consecutiveInterval_zero {S : ObservedSignature}
    (j : Fin S.count) (h : 0 ≤ j.val) :
    consecutiveInterval j 0 h = NodeSet.singleton j := by
  simp [consecutiveInterval, consecutiveSummed_of_zero, NodeSet.union_empty_right]

theorem predIndexNth_predIndexNth_one {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    predIndexNth (predIndexNth j 1 (one_le_of_succ_le h)) n
        (by
          simpa [predIndexNth] using
            Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)) =
      predIndexNth j (n + 1) h :=
  Fin.eq_of_val_eq (by
    simp [predIndexNth]
    omega)

theorem chainCondition_predIndexNth {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) :
    chainCondition NodeSet.full j =
      NodeSet.union (consecutiveSummed j n h)
        (chainCondition NodeSet.full (predIndexNth j n h)) := by
  induction n generalizing j with
  | zero =>
      rw [consecutiveSummed_of_zero, predIndexNth_eq_zero,
        NodeSet.union_empty_left]
  | succ n ih =>
      have h1 : 1 ≤ j.val := one_le_of_succ_le h
      have hpos : 0 < j.val := Nat.lt_of_succ_le h1
      have hn' : n ≤ (predIndexNth j 1 h1).val := by
        simpa [predIndexNth] using
          Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)
      have hi := chainCondition_predIndex j hpos
      have hnth1 : predIndexNth j 1 h1 = predIndex j hpos :=
        predIndexNth_one j h1
      rw [consecutiveSummed_succ]
      calc
        chainCondition NodeSet.full j =
            NodeSet.union (NodeSet.singleton (predIndex j hpos))
              (chainCondition NodeSet.full (predIndex j hpos)) := hi
        _ = NodeSet.union (NodeSet.singleton (predIndexNth j 1 h1))
              (chainCondition NodeSet.full (predIndexNth j 1 h1)) := by
            rw [hnth1]
        _ = NodeSet.union (NodeSet.singleton (predIndexNth j 1 h1))
              (NodeSet.union
                (consecutiveSummed (predIndexNth j 1 h1) n hn')
                (chainCondition NodeSet.full
                  (predIndexNth (predIndexNth j 1 h1) n hn'))) := by
            rw [ih (predIndexNth j 1 h1) hn']
        _ = NodeSet.union
              (NodeSet.union (NodeSet.singleton (predIndexNth j 1 h1))
                (consecutiveSummed (predIndexNth j 1 h1) n hn'))
              (chainCondition NodeSet.full
                (predIndexNth (predIndexNth j 1 h1) n hn')) :=
          (NodeSet.union_assoc _ _ _).symm
        _ = NodeSet.union
              (NodeSet.union (NodeSet.singleton (predIndexNth j 1 h1))
                (consecutiveSummed (predIndexNth j 1 h1) n hn'))
              (chainCondition NodeSet.full (predIndexNth j (n + 1) h)) := by
            rw [predIndexNth_predIndexNth_one]

theorem mem_consecutivePredList_lt {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) {i : Fin S.count}
    (hi : i ∈ consecutivePredList j n h) :
    i.val < j.val := by
  rcases List.mem_ofFn.mp hi with ⟨k, hk⟩
  have hn : 0 < k.val + 1 := Nat.succ_pos _
  rw [← hk]
  exact predIndexNth_lt_of_pos j (k.val + 1) _ hn

theorem disjoint_foldl_union_singleton {S : ObservedSignature}
    (X : NodeSet S) (nodes : List (Fin S.count))
    (h : ∀ node ∈ nodes, NodeSet.Disjoint X (NodeSet.singleton node)) :
    NodeSet.Disjoint X
      (nodes.foldl
        (fun acc node => NodeSet.union acc (NodeSet.singleton node))
        NodeSet.empty) := by
  induction nodes with
  | nil =>
      simpa [List.foldl] using NodeSet.disjoint_empty_right X
  | cons n ns ih =>
      rw [foldl_union_singleton_cons]
      exact NodeSet.disjoint_union_of
        (h n (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun node hm => h node (List.mem_cons.mpr (Or.inr hm))))

theorem disjoint_singleton_consecutiveSummed {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) :
    NodeSet.Disjoint (NodeSet.singleton j) (consecutiveSummed j n h) := by
  unfold consecutiveSummed
  apply disjoint_foldl_union_singleton
  intro node hmem
  have hlt := mem_consecutivePredList_lt j n h hmem
  exact NodeSet.disjoint_singletons_of_ne (fun heq =>
    Nat.lt_irrefl _ (heq ▸ hlt))

theorem disjoint_foldl_union_singleton_left {S : ObservedSignature}
    (W : NodeSet S) (nodes : List (Fin S.count))
    (h : ∀ node ∈ nodes, NodeSet.Disjoint (NodeSet.singleton node) W) :
    NodeSet.Disjoint
      (nodes.foldl
        (fun acc node => NodeSet.union acc (NodeSet.singleton node))
        NodeSet.empty)
      W := by
  induction nodes with
  | nil =>
      simpa [List.foldl] using NodeSet.disjoint_empty_left W
  | cons n ns ih =>
      rw [foldl_union_singleton_cons]
      exact NodeSet.disjoint_union_left_of
        (h n (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun node hm => h node (List.mem_cons.mpr (Or.inr hm))))

theorem disjoint_consecutiveSummed_chainCondition {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) :
    NodeSet.Disjoint (consecutiveSummed j n h)
      (chainCondition NodeSet.full (predIndexNth j n h)) := by
  unfold consecutiveSummed
  apply disjoint_foldl_union_singleton_left
  intro node hmem
  rcases List.mem_ofFn.mp hmem with ⟨k, hk⟩
  have hle : (predIndexNth j n h).val ≤ node.val := by
    rw [← hk]
    simpa [predIndexNth] using
      Nat.sub_le_sub_left (Nat.succ_le_of_lt k.isLt) j.val
  cases Nat.lt_or_eq_of_le hle with
  | inl hlt =>
      exact disjoint_later_chainCondition NodeSet.full hlt
  | inr heq =>
      have hnode : node = predIndexNth j n h := Fin.eq_of_val_eq heq.symm
      simpa [hnode] using
        disjoint_singleton_chainCondition NodeSet.full node

def chainKernel (remaining : NodeSet S) (node : Fin S.count) : Kernel S where
  outcome := NodeSet.singleton node
  action := NodeSet.empty
  condition := chainCondition remaining node

/--
Observational factorization of a c-component, written as a product of
chain-rule kernels.  This is `Q[S]` in Tian's notation, using global
topological predecessors that still lie in `remaining` (Shpitser–Pearl 2006,
step 4).
-/
def chainProduct (remaining component : NodeSet S) : ProbabilityTerm S :=
  productTerms
    ((NodeSet.members component).map (fun node =>
      .kernel (chainKernel remaining node)))

theorem chainProduct_actionFree (remaining component : NodeSet S) :
    (chainProduct remaining component).ActionFree :=
  productTerms_actionFree _
    (fun t ht => by
      rcases List.mem_map.mp ht with ⟨_node, _, rfl⟩
      intro _i
      rfl)

/-- A one-vertex c-component factorizes as the single chain-rule kernel
on that vertex.  Singleton 4.2 writes this kernel (then an empty
complementary sum) once the free component coincides with a singleton
outcome. -/
theorem chainProduct_of_members_singleton (remaining : NodeSet S)
    {component : NodeSet S} {y : Fin S.count}
    (h : NodeSet.members component = [y]) :
    chainProduct remaining component =
      ProbabilityTerm.kernel (chainKernel remaining y) := by
  simp [chainProduct, h, productTerms]

/-- Chain-rule kernels of `j` and its n predecessors, later first so
`productTerms` matches the chain-constructor multiply order used by
the consecutive 4.2 certificates. -/
def consecutiveChainKernels {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (h : n ≤ j.val) : List (ProbabilityTerm S) :=
  List.ofFn fun i : Fin (n + 1) =>
    ProbabilityTerm.kernel
      (chainKernel NodeSet.full
        (predIndexNth j i.val
          (Nat.le_trans (Nat.le_of_lt_succ i.isLt) h)))

/-- Consecutive n-step 4.2 formula: the singleton kernel when `n = 0`,
and otherwise the complementary sum of the later-first chain product. -/
def consecutiveChainTerm {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (h : n ≤ j.val) : ProbabilityTerm S :=
  match n with
  | 0 => ProbabilityTerm.kernel (chainKernel NodeSet.full j)
  | n + 1 =>
      ProbabilityTerm.marginalize (consecutiveSummed j (n + 1) h)
        (productTerms (consecutiveChainKernels j (n + 1) h))

theorem consecutiveChainTerm_zero {S : ObservedSignature}
    (j : Fin S.count) :
    consecutiveChainTerm j 0 (Nat.zero_le j.val) =
      ProbabilityTerm.kernel (chainKernel NodeSet.full j) :=
  rfl

theorem consecutiveChainKernels_one {S : ObservedSignature}
    (j : Fin S.count) (h : 1 ≤ j.val) :
    consecutiveChainKernels j 1 h =
      [ProbabilityTerm.kernel (chainKernel NodeSet.full j),
        ProbabilityTerm.kernel
          (chainKernel NodeSet.full (predIndex j (Nat.lt_of_succ_le h)))] := by
  unfold consecutiveChainKernels
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp [predIndexNth_zero, predIndexNth_one]

theorem consecutiveChainKernels_two {S : ObservedSignature}
    (j : Fin S.count) (h : 2 ≤ j.val) :
    consecutiveChainKernels j 2 h =
      [ProbabilityTerm.kernel (chainKernel NodeSet.full j),
        ProbabilityTerm.kernel
          (chainKernel NodeSet.full
            (predIndex j (Nat.lt_of_succ_le (Nat.le_trans (Nat.le_succ 1) h)))),
        ProbabilityTerm.kernel
          (chainKernel NodeSet.full (predIndex2 j (Nat.lt_of_succ_le h)))] := by
  have h1 : 1 ≤ j.val := Nat.le_trans (Nat.le_succ 1) h
  unfold consecutiveChainKernels
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp [predIndexNth_zero, predIndexNth_one (h := h1), predIndexNth_two (h := h)]

theorem consecutiveChainTerm_one {S : ObservedSignature}
    (j : Fin S.count) (h : 1 ≤ j.val) :
    consecutiveChainTerm j 1 h =
      ProbabilityTerm.marginalize
        (NodeSet.singleton (predIndex j (Nat.lt_of_succ_le h)))
        (.multiply
          (.kernel (chainKernel NodeSet.full j))
          (.kernel (chainKernel NodeSet.full
            (predIndex j (Nat.lt_of_succ_le h))))) := by
  simp [consecutiveChainTerm, consecutiveSummed_one, consecutiveChainKernels_one,
    productTerms]

theorem consecutiveChainTerm_two {S : ObservedSignature}
    (j : Fin S.count) (h : 2 ≤ j.val) :
    consecutiveChainTerm j 2 h =
      ProbabilityTerm.marginalize
        (NodeSet.union
          (NodeSet.singleton
            (predIndex j (Nat.lt_of_succ_le (Nat.le_trans (Nat.le_succ 1) h))))
          (NodeSet.singleton (predIndex2 j (Nat.lt_of_succ_le h))))
        (.multiply
          (.kernel (chainKernel NodeSet.full j))
          (.multiply
            (.kernel (chainKernel NodeSet.full
              (predIndex j (Nat.lt_of_succ_le
                (Nat.le_trans (Nat.le_succ 1) h)))))
            (.kernel (chainKernel NodeSet.full
              (predIndex2 j (Nat.lt_of_succ_le h)))))) := by
  simp [consecutiveChainTerm, consecutiveSummed_two, consecutiveChainKernels_two,
    productTerms]

theorem consecutiveChainKernels_zero {S : ObservedSignature}
    (j : Fin S.count) (h : 0 ≤ j.val) :
    consecutiveChainKernels j 0 h =
      [ProbabilityTerm.kernel
        (chainKernel NodeSet.full (predIndexNth j 0 h))] := by
  unfold consecutiveChainKernels
  rw [List.ofFn_succ, List.ofFn_zero]
  congr 1

/--
The consecutive chain-kernel list is a `List.ofFn` of length `n + 1`,
so it is never `[]`.  Length of `nil` is definitionally `0`; rewriting
the computed length along `heq` and using `Nat.succ_ne_zero` avoids
`List.eq_nil_iff_forall_not_mem`, which depends on `Classical.choice`.
-/
theorem consecutiveChainKernels_ne_nil {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) :
    consecutiveChainKernels j n h ≠ [] := by
  have hlen : (consecutiveChainKernels j n h).length = n + 1 := by
    simp [consecutiveChainKernels]
  intro heq
  rw [heq] at hlen
  exact Nat.succ_ne_zero n (Eq.symm hlen)

theorem consecutiveChainKernels_product_zero {S : ObservedSignature}
    (j : Fin S.count) (h : 0 ≤ j.val) :
    productTerms (consecutiveChainKernels j 0 h) =
      ProbabilityTerm.kernel (chainKernel NodeSet.full j) := by
  rw [consecutiveChainKernels_zero, predIndexNth_eq_zero]
  rfl

theorem consecutiveChainKernels_succ {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    consecutiveChainKernels j (n + 1) h =
      ProbabilityTerm.kernel (chainKernel NodeSet.full j) ::
        consecutiveChainKernels
          (predIndexNth j 1 (one_le_of_succ_le h)) n
          (by
            simpa [predIndexNth] using
              Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)) := by
  unfold consecutiveChainKernels
  rw [List.ofFn_succ]
  refine congr (congrArg List.cons ?_) ?_
  · apply congrArg
    apply congrArg
    exact predIndexNth_eq_zero _ _
  · congr 1
    funext i
    apply congrArg
    apply congrArg
    apply Fin.eq_of_val_eq
    simp [predIndexNth, Fin.succ]
    omega

theorem consecutiveChainTerm_succ {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    consecutiveChainTerm j (n + 1) h =
      ProbabilityTerm.marginalize (consecutiveSummed j (n + 1) h)
        (.multiply
          (.kernel (chainKernel NodeSet.full j))
          (productTerms
            (consecutiveChainKernels
              (predIndexNth j 1 (one_le_of_succ_le h)) n
              (by
                simpa [predIndexNth] using
                  Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h))))) := by
  simp only [consecutiveChainTerm]
  rw [consecutiveChainKernels_succ,
    productTerms_cons _ _ (consecutiveChainKernels_ne_nil _ _ _)]

theorem consecutiveChainTerm_actionFree {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) :
    (consecutiveChainTerm j n h).ActionFree := by
  cases n with
  | zero =>
      intro _i
      rfl
  | succ n =>
      simp only [consecutiveChainTerm]
      exact productTerms_actionFree _
        (fun t ht => by
          rcases List.mem_ofFn.mp ht with ⟨_i, rfl⟩
          intro _k
          rfl)

theorem consecutive_chainKernel_eq {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n ≤ j.val) :
    ProbabilityTerm.kernel
        ⟨NodeSet.singleton j, NodeSet.empty,
          NodeSet.union (consecutiveSummed j n h)
            (chainCondition NodeSet.full (predIndexNth j n h))⟩ =
      .kernel (chainKernel NodeSet.full j) := by
  simp only [chainKernel]
  rw [← chainCondition_predIndexNth j n h]

theorem consecutiveSummed_succ_eq_interval {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    consecutiveSummed j (n + 1) h =
      consecutiveInterval (predIndexNth j 1 (one_le_of_succ_le h)) n
        (by
          simpa [predIndexNth] using
            Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)) := by
  rw [consecutiveInterval, consecutiveSummed_succ]

/--
One fuel-bounded ID step on a current remaining vertex set and a current
observational expression `current` for `P(remaining)`.

The cases follow Shpitser–Pearl 2006, function ID:

1. empty action — marginalize to the outcome;
2. discard non-ancestors of `Y` in `G_{\overline{X}}`;
3. `C(G \ X)` has two or more pieces — product of subproblems, then
   marginalize `V \ (Y ∪ X)`;
4. unique free c-component `S`:
   4.1 `C(G) = {G}` — fail (hedge);
   4.2 `S` is already a c-component of `G` — chain-rule expression;
   4.3 `S ⊂ S' ∈ C(G)` — recurse on `G_{S'}` with the restricted action
       `X ∩ S'` and the chain-rule joint on `S'`.
-/
def identifyFuel (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S) : IdentificationOutcome S :=
  match fuel with
  | 0 => .unfinished
  | fuel + 1 =>
      let identifyNext := identifyFuel fuel
      let y := NodeSet.inter outcome remaining
      let x := NodeSet.inter action remaining
      if NodeSet.isEmpty x then
        .identified (.marginalize (NodeSet.diff remaining y) current)
      else
        let kept := G.ancestralSet remaining (GraphMutilation.bar x) y
        if NodeSet.equal kept remaining then
          let free := NodeSet.diff remaining x
          let freeComponents := G.cComponents free
          match freeComponents with
          | [] =>
              .identified (.marginalize remaining current)
          | [component] =>
              if G.isSingleCComponent remaining then
                .failed ⟨remaining, component⟩
              else if (G.cComponents remaining).any (fun piece =>
                  NodeSet.equal piece component) then
                .identified
                  (.marginalize (NodeSet.diff component y)
                    (chainProduct remaining component))
              else
                match G.containingCComponent remaining component with
                | some larger =>
                    identifyNext G larger outcome (NodeSet.inter x larger)
                      (chainProduct remaining larger)
                | none =>
                    .unfinished
          | _ :: _ :: _ =>
              IdentificationOutcome.combine
                (freeComponents.map (fun component =>
                  identifyNext G remaining component
                    (NodeSet.diff remaining component) current))
                (fun terms =>
                  .marginalize
                    (NodeSet.diff remaining (NodeSet.union y x))
                    (productTerms terms))
        else
          identifyNext G kept outcome action
            (.marginalize (NodeSet.diff remaining kept) current)

/-- Top-level ID for a joint kernel query on the full observed graph. -/
def identifyJoint (G : ObservedGraph S) (q : JointKernelQuery S) :
    IdentificationOutcome S :=
  identifyFuel (identificationFuel S) G NodeSet.full q.outcome q.action
    (observationalJointTerm S)

/-- Joint numerator `P(outcome, condition | do(action))` of a conditional query. -/
def ConditionalKernelQuery.jointNumerator (q : ConditionalKernelQuery S) :
    JointKernelQuery S where
  outcome := NodeSet.union q.outcome q.condition
  action := q.action
  action_outcome_disjoint :=
    NodeSet.disjoint_union_of q.action_outcome_disjoint
      q.action_condition_disjoint

/-- Joint denominator `P(condition | do(action))` of a conditional query. -/
def ConditionalKernelQuery.jointDenominator (q : ConditionalKernelQuery S) :
    JointKernelQuery S where
  outcome := q.condition
  action := q.action
  action_outcome_disjoint := q.action_condition_disjoint

/--
Bayes reduction of IDC: identify `P(Y, Z | do(X))` and `P(Z | do(X))`, then
divide.  Sound when both joints identify; not yet complete for every
identifiable conditional, because IDC may first drop d-separated witnesses
or insert observations.  Those reductions will be added as Boolean
d-separation pre-steps on the same fuel.
-/
def identifyConditional (G : ObservedGraph S)
    (q : ConditionalKernelQuery S) : IdentificationOutcome S :=
  match identifyJoint G q.jointNumerator, identifyJoint G q.jointDenominator with
  | .identified numerator, .identified denominator =>
      .identified (.divide numerator denominator)
  | .failed seed, _ => .failed seed
  | _, .failed seed => .failed seed
  | _, _ => .unfinished

/--
Empty-action queries reduce in one step to an observational marginal of
`P(V)`.  Completeness of this branch is the trivial ID base case.
-/
theorem identifyJoint_of_empty_action (G : ObservedGraph S)
    (q : JointKernelQuery S) (emptyAction : NodeSet.isEmpty q.action = true) :
    identifyJoint G q =
      .identified
        (.marginalize (NodeSet.diff NodeSet.full q.outcome)
          (observationalJointTerm S)) := by
  simp [identifyJoint, identificationFuel, identifyFuel, emptyAction,
    NodeSet.inter_full_right]

/--
Empty-action conditional queries reduce by IDC's Bayes step: identify
the two joints `P(Y, Z)` and `P(Z)`, then divide.  Completeness of this
branch is the empty-action base case of IDC.
-/
theorem identifyConditional_of_empty_action (G : ObservedGraph S)
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    identifyConditional G q =
      IdentificationOutcome.identified
        (.divide
          (.marginalize
            (NodeSet.diff NodeSet.full
              (NodeSet.union q.outcome q.condition))
            (observationalJointTerm S))
          (.marginalize
            (NodeSet.diff NodeSet.full q.condition)
            (observationalJointTerm S))) := by
  have hnum :=
    identifyJoint_of_empty_action G q.jointNumerator emptyAction
  have hden :=
    identifyJoint_of_empty_action G q.jointDenominator emptyAction
  simp only [identifyConditional]
  rw [hnum, hden]
  simp [ConditionalKernelQuery.jointNumerator,
    ConditionalKernelQuery.jointDenominator]

/--
The empty-local-action ID step, at any remaining set.  Top-level
`identifyJoint_of_empty_action` is the instance `remaining = V`.
-/
theorem identifyFuel_eq_identified_of_empty_action
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = true) :
    identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff remaining (NodeSet.inter outcome remaining))
          current) := by
  simp [identifyFuel, hex]

/--
No free c-component means the working remaining set lies inside the
local action, so ID returns the current expression marginalized off
every remaining vertex.
-/
theorem identifyFuel_eq_identified_of_empty_free
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) = []) :
    identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize remaining current) := by
  simp [identifyFuel, hex, hkept, hfc]

theorem IdentificationOutcome.collect_identified_actionFree
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (assembleFree :
      forall terms,
        (forall t, t ∈ terms -> t.ActionFree) -> (assemble terms).ActionFree)
    (pending : List (IdentificationOutcome S))
    (acc : List (ProbabilityTerm S))
    (accFree : forall t, t ∈ acc -> t.ActionFree)
    (pendingFree :
      forall t, IdentificationOutcome.identified t ∈ pending -> t.ActionFree)
    {term : ProbabilityTerm S}
    (h : IdentificationOutcome.collect assemble pending acc =
      IdentificationOutcome.identified term) :
    term.ActionFree := by
  induction pending generalizing acc term with
  | nil =>
      simp [IdentificationOutcome.collect] at h
      subst h
      exact assembleFree acc.reverse (fun t ht =>
        accFree t (List.mem_reverse.mp ht))
  | cons head rest ih =>
      cases head with
      | identified t =>
          simp [IdentificationOutcome.collect] at h
          refine ih (t :: acc) ?_ ?_ h
          · intro w hw
            cases List.mem_cons.mp hw with
            | inl hEq =>
                exact hEq.symm ▸ pendingFree t (by simp)
            | inr hwacc =>
                exact accFree w hwacc
          · intro u hu
            exact pendingFree u (List.mem_cons.mpr (Or.inr hu))
      | failed _seed =>
          simp [IdentificationOutcome.collect] at h
      | unfinished =>
          simp [IdentificationOutcome.collect] at h

theorem IdentificationOutcome.combine_identified_actionFree
    (outcomes : List (IdentificationOutcome S))
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
    (assembleFree :
      forall terms,
        (forall t, t ∈ terms -> t.ActionFree) -> (assemble terms).ActionFree)
    (eachFree :
      forall t, IdentificationOutcome.identified t ∈ outcomes -> t.ActionFree)
    {term : ProbabilityTerm S}
    (h : IdentificationOutcome.combine outcomes assemble =
      IdentificationOutcome.identified term) :
    term.ActionFree :=
  IdentificationOutcome.collect_identified_actionFree assemble assembleFree
    outcomes [] (fun _t ht => by cases ht) eachFree h

/--
Every successful ID formula is action-free: the recursion starts from `P(V)`
and only composes observational kernels, products, quotients, and
marginals.  That is the syntactic half of a published joint certificate.
-/
theorem identifyFuel_identified_actionFree
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hcur : current.ActionFree)
    {term : ProbabilityTerm S}
    (h : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.identified term) :
    term.ActionFree := by
  induction fuel generalizing remaining outcome action current term with
  | zero =>
      simp [identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, hex] at h
          subst h
          exact hcur
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [identifyFuel, hex, hkept] at h
              exact ih
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                outcome action
                (.marginalize
                  (NodeSet.diff remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)))
                  current)
                hcur h
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, hex, hkept, hfc] at h
                  subst h
                  exact hcur
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, hex, hkept, hfc, hsingle] at h
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                              subst h
                              exact chainProduct_actionFree remaining
                                component
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  exact ih larger outcome
                                    (NodeSet.inter
                                      (NodeSet.inter action remaining)
                                      larger)
                                    (chainProduct remaining larger)
                                    (chainProduct_actionFree remaining larger)
                                    h
                  | cons component2 rest2 =>
                      simp [identifyFuel, hex, hkept, hfc] at h
                      refine IdentificationOutcome.combine_identified_actionFree
                        _ _ ?_ ?_ h
                      · intro terms hterms
                        exact productTerms_actionFree terms hterms
                      · intro t ht
                        simp [List.mem_cons] at ht
                        rcases ht with h1 | hrest
                        · exact ih remaining component
                            (NodeSet.diff remaining component) current hcur
                            h1.symm
                        · rcases hrest with h2 | ⟨piece, _, hEq⟩
                          · exact ih remaining component2
                              (NodeSet.diff remaining component2) current
                              hcur h2.symm
                          · exact ih remaining piece
                              (NodeSet.diff remaining piece) current hcur hEq

/--
ID failure always occurs on a remaining set that is a single c-component
of the working graph.  The failed remaining set is contained in the
remaining set of the call that produced it.
-/
theorem identifyFuel_eq_failed
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    G.isSingleCComponent fail.remaining = true ∧
      NodeSet.Subset fail.remaining remaining := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [identifyFuel, hex, hkept] at h
              have nested :=
                ih
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  h
              exact ⟨nested.1, NodeSet.Subset.trans nested.2
                (ancestralSet_subset G remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))⟩
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          exact ⟨hsingle, fun _i hi => hi⟩
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  have nested :=
                                    ih larger outcome
                                      (NodeSet.inter
                                        (NodeSet.inter action remaining)
                                        larger)
                                      (chainProduct remaining larger) h
                                  exact ⟨nested.1, NodeSet.Subset.trans nested.2
                                    (containingCComponent_subset_host G
                                      remaining component hcont)⟩
                  | cons component2 rest2 =>
                      simp [identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

/--
The free side recorded at a hedge failure is a listed c-component of some
host still inside the working remaining set.  That host is `remaining \ X`
at an immediate 4.1 fail, and is preserved by ancestral restriction, 4.3
c-component restriction, and product recursion.
-/
theorem identifyFuel_eq_failed_free
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    NodeSet.Subset fail.free fail.remaining ∧
      Exists fun host =>
        Exists fun root =>
          host root = true ∧
            fail.free = G.cComponentOf host root ∧
              NodeSet.Subset host remaining := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [identifyFuel, hex, hkept] at h
              have nested :=
                ih
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  h
              constructor
              · exact nested.1
              · rcases nested.2 with ⟨host, root, hroot, hdef, hsub⟩
                exact ⟨host, root, hroot, hdef,
                  NodeSet.Subset.trans hsub
                    (ancestralSet_subset G remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining))⟩
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          constructor
                          · intro i hi
                            have hmem :
                                component ∈
                                  G.cComponents
                                    (NodeSet.diff remaining
                                      (NodeSet.inter action remaining)) := by
                              simp [hfc]
                            rcases cComponents_mem G _ hmem with
                              ⟨root, _, hdef⟩
                            have hi' :
                                G.cComponentOf
                                  (NodeSet.diff remaining
                                    (NodeSet.inter action remaining))
                                  root i = true := by
                              simpa [hdef] using hi
                            exact NodeSet.diff_subset_left _ _ i
                              (cComponentOf_subset G _ hi')
                          · have hmem :
                                component ∈
                                  G.cComponents
                                    (NodeSet.diff remaining
                                      (NodeSet.inter action remaining)) := by
                              simp [hfc]
                            rcases cComponents_mem G _ hmem with
                              ⟨root, hroot, hdef⟩
                            exact ⟨NodeSet.diff remaining
                                (NodeSet.inter action remaining),
                              root, hroot, hdef, NodeSet.diff_subset_left _ _⟩
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  have nested :=
                                    ih larger outcome
                                      (NodeSet.inter
                                        (NodeSet.inter action remaining)
                                        larger)
                                      (chainProduct remaining larger) h
                                  constructor
                                  · exact nested.1
                                  · rcases nested.2 with
                                      ⟨host, root, hroot, hdef, hsub⟩
                                    exact ⟨host, root, hroot, hdef,
                                      NodeSet.Subset.trans hsub
                                        (containingCComponent_subset_host G
                                          remaining component hcont)⟩
                  | cons component2 rest2 =>
                      simp [identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

/--
A 4.1 failure always records a nonempty cut `remaining \ free`.  The local
action of that call is nonempty and lives in the cut, because the free
side is a c-component of `remaining \ X`.
-/
theorem identifyFuel_eq_failed_cut_nonempty
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    NodeSet.isEmpty
      (NodeSet.diff fail.remaining fail.free) = false := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [identifyFuel, hex, hkept] at h
              exact ih
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                outcome action
                (.marginalize
                  (NodeSet.diff remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)))
                  current)
                h
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          rcases (NodeSet.isEmpty_eq_false_iff
                              (NodeSet.inter action remaining)).mp hex with
                            ⟨i, hi⟩
                          have hrem : remaining i = true :=
                            NodeSet.inter_subset_right action remaining i hi
                          have hhost :
                              NodeSet.diff remaining
                                (NodeSet.inter action remaining) i = false := by
                            simp [NodeSet.diff, hi]
                          have hfree : component i = false := by
                            cases hf : component i with
                            | false => rfl
                            | true =>
                                have hmem :
                                    component ∈
                                      G.cComponents
                                        (NodeSet.diff remaining
                                          (NodeSet.inter action remaining)) :=
                                  by simp [hfc]
                                rcases cComponents_mem G _ hmem with
                                  ⟨root, _, hdef⟩
                                have inHost :
                                    NodeSet.diff remaining
                                      (NodeSet.inter action remaining) i =
                                      true :=
                                  cComponentOf_subset G _
                                    (by simpa [hdef] using hf)
                                exact False.elim
                                  (Bool.false_ne_true
                                    (hhost.symm.trans inHost))
                          exact (NodeSet.isEmpty_eq_false_iff _).mpr
                            ⟨i, Bool.and_eq_true_iff.mpr
                              ⟨hrem, by simp [hfree]⟩⟩
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  exact ih larger outcome
                                    (NodeSet.inter
                                      (NodeSet.inter action remaining)
                                      larger)
                                    (chainProduct remaining larger) h
                  | cons component2 rest2 =>
                      simp [identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

theorem identifyJoint_eq_failed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : identifyJoint G q = IdentificationOutcome.failed fail) :
    G.isSingleCComponent fail.remaining = true :=
  (identifyFuel_eq_failed (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h).1

theorem identifyJoint_eq_failed_cut_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty (NodeSet.diff fail.remaining fail.free) = false :=
  identifyFuel_eq_failed_cut_nonempty (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h

theorem identifyJoint_identified_actionFree
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {term : ProbabilityTerm S}
    (h : identifyJoint G q = IdentificationOutcome.identified term) :
    term.ActionFree :=
  identifyFuel_identified_actionFree (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S)
    (observationalJointTerm_actionFree S) h

theorem identifyConditional_identified_actionFree
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    {term : ProbabilityTerm S}
    (h : identifyConditional G q = IdentificationOutcome.identified term) :
    term.ActionFree := by
  cases hnum : identifyJoint G q.jointNumerator with
  | identified numerator =>
      cases hden : identifyJoint G q.jointDenominator with
      | identified denominator =>
          simp [identifyConditional, hnum, hden] at h
          subst h
          exact ⟨identifyJoint_identified_actionFree G q.jointNumerator hnum,
            identifyJoint_identified_actionFree G q.jointDenominator hden⟩
      | failed _ => simp [identifyConditional, hnum, hden] at h
      | unfinished => simp [identifyConditional, hnum, hden] at h
  | failed _ =>
      cases hden : identifyJoint G q.jointDenominator <;>
        simp [identifyConditional, hnum, hden] at h
  | unfinished =>
      cases hden : identifyJoint G q.jointDenominator <;>
        simp [identifyConditional, hnum, hden] at h

theorem FiniteReachability.source_mem_closure
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (fuel : Nat) (source : α) (reached : List α)
    (inNodes : source ∈ nodes) (self : same source source = true)
    (inReached : source ∈ reached) :
    source ∈ FiniteReachability.closure same nodes edge fuel reached := by
  induction fuel generalizing reached with
  | zero => simpa [FiniteReachability.closure] using inReached
  | succ fuel ih =>
      rw [FiniteReachability.closure]
      apply ih
      simp [FiniteReachability.step, List.mem_filter]
      exact ⟨inNodes, source, inReached, Or.inl self⟩

theorem FiniteReachability.within_self
    (same : α -> α -> Bool) (nodes : List α) (edge : α -> α -> Bool)
    (fuel : Nat) (source : α)
    (inNodes : source ∈ nodes) (self : same source source = true) :
    FiniteReachability.within same nodes edge fuel source source = true := by
  simp [FiniteReachability.within, FiniteReachability.contains]
  exact ⟨source,
    FiniteReachability.source_mem_closure same nodes edge fuel source
      [source] inNodes self (List.mem_singleton.mpr rfl),
    self⟩

theorem cComponentOf_root_mem (G : ObservedGraph S) (nodes : NodeSet S)
    {root : Fin S.count} (hroot : nodes root = true) :
    G.cComponentOf nodes root root = true := by
  unfold ObservedGraph.cComponentOf ObservedGraph.bidirectedReachableWithin
  simp [hroot]
  exact FiniteReachability.within_self finBeq (NodeSet.enumerated S)
    (fun i j => nodes i && nodes j && G.bidirected i j) S.count root
    (NodeSet.mem_enumerated S root) (natBeq_refl root.val)

/--
A selected target is ancestral of itself: the Boolean ancestry test
includes the reflexive walk at that vertex.
-/
theorem ancestralSet_contains_targets
    (G : ObservedGraph S) (nodes : NodeSet S)
    (m : GraphMutilation S) (targets : NodeSet S)
    {i : Fin S.count}
    (hnodes : nodes i = true) (htargets : targets i = true) :
    G.ancestralSet nodes m targets i = true := by
  unfold ObservedGraph.ancestralSet ObservedGraph.ancestorOfWithin
  refine Bool.and_eq_true_iff.mpr ⟨hnodes, ?_⟩
  refine List.any_eq_true.mpr ?_
  refine ⟨i, ?_, ?_⟩
  · exact (NodeSet.mem_members_iff (NodeSet.inter targets nodes) i).mpr
      (Bool.and_eq_true_iff.mpr ⟨htargets, hnodes⟩)
  · exact FiniteReachability.within_self finBeq (NodeSet.enumerated S)
      (G.directedEdgeWithin nodes m) S.count i
      (NodeSet.mem_enumerated S i) (natBeq_refl i.val)

/--
Every selected vertex is placed in some listed c-component, once it has
either already been accumulated or still appears in the pending scan.
The top-level collector pending is the full enumeration, so every selected
vertex is covered.
-/
theorem cComponentsCollect_covers
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pending : List (Fin S.count)) (acc : List (NodeSet S))
    (hacc : forall component, component ∈ acc ->
      Exists fun root =>
        nodes root = true ∧ component = G.cComponentOf nodes root)
    {i : Fin S.count} (hi : nodes i = true)
    (hseen :
      acc.any (fun c => c i) = true ∨ i ∈ pending) :
    Exists fun component =>
      component ∈ ObservedGraph.cComponentsCollect G nodes pending acc ∧
        component i = true := by
  induction pending generalizing acc with
  | nil =>
      have hany : acc.any (fun c => c i) = true := by
        cases hseen with
        | inl h => exact h
        | inr hmem => cases hmem
      rcases List.any_eq_true.mp hany with ⟨component, hc, hi'⟩
      exact ⟨component,
        cComponentsCollect_keeps_acc G nodes [] acc hc, hi'⟩
  | cons root rest ih =>
      cases hanyI : acc.any (fun c => c i) with
      | true =>
          rcases List.any_eq_true.mp hanyI with ⟨component, hc, hi'⟩
          exact ⟨component,
            cComponentsCollect_keeps_acc G nodes (root :: rest) acc hc, hi'⟩
      | false =>
          have hiPend : i ∈ root :: rest := by
            cases hseen with
            | inl h =>
                exact False.elim (Bool.false_ne_true (hanyI.symm.trans h))
            | inr hmem =>
                exact hmem
          cases hnode : nodes root with
          | false =>
              have irest : i ∈ rest := by
                rcases List.mem_cons.mp hiPend with heq | hrest
                · subst heq
                  exact False.elim
                    (Bool.false_ne_true (hnode.symm.trans hi))
                · exact hrest
              simp [ObservedGraph.cComponentsCollect, hnode]
              exact ih acc hacc (Or.inr irest)
          | true =>
              cases hseenR : acc.any (fun c => c root) with
              | true =>
                  simp [ObservedGraph.cComponentsCollect, hnode, hseenR]
                  rcases List.mem_cons.mp hiPend with heq | hrest
                  · subst heq
                    exact False.elim
                      (Bool.false_ne_true (hanyI.symm.trans hseenR))
                  · exact ih acc hacc (Or.inr hrest)
              | false =>
                  simp [ObservedGraph.cComponentsCollect, hnode, hseenR]
                  have hacc' :
                      forall component,
                        component ∈ G.cComponentOf nodes root :: acc ->
                          Exists fun r =>
                            nodes r = true ∧
                              component = G.cComponentOf nodes r := by
                    intro component hc
                    rcases List.mem_cons.mp hc with heq | hca
                    · exact ⟨root, hnode, heq⟩
                    · exact hacc component hca
                  rcases List.mem_cons.mp hiPend with heq | hrest
                  · subst heq
                    refine ⟨G.cComponentOf nodes i, ?_,
                      cComponentOf_root_mem G nodes hnode⟩
                    exact cComponentsCollect_keeps_acc G nodes rest
                      (G.cComponentOf nodes i :: acc)
                      (List.mem_cons.mpr (Or.inl rfl))
                  · exact ih (G.cComponentOf nodes root :: acc) hacc'
                      (Or.inr hrest)

theorem cComponents_covers
    (G : ObservedGraph S) (nodes : NodeSet S) {i : Fin S.count}
    (hi : nodes i = true) :
    Exists fun component =>
      component ∈ G.cComponents nodes ∧ component i = true :=
  cComponentsCollect_covers G nodes (NodeSet.enumerated S) []
    (fun _c hc => by cases hc) hi
    (Or.inr (NodeSet.mem_enumerated S i))

/-- A singleton listed partition is the host set itself. -/
theorem cComponents_eq_of_singleton
    (G : ObservedGraph S) (nodes : NodeSet S) {c : NodeSet S}
    (h : G.cComponents nodes = [c]) : c = nodes := by
  funext i
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hc
    have hmem : c ∈ G.cComponents nodes := by simp [h]
    rcases cComponents_mem G nodes hmem with ⟨root, _, hdef⟩
    have hi : G.cComponentOf nodes root i = true := by
      simpa [hdef] using hc
    exact cComponentOf_subset G nodes hi
  · intro hn
    rcases cComponents_covers G nodes hn with ⟨component, hmem, hi⟩
    have hcomp : component = c := by
      simp [h] at hmem
      exact hmem
    simpa [hcomp] using hi

/--
Every ID failure is a 4.1 site for some local outcome and local action:
the recorded remaining set is ancestral of that local outcome in
`G_{\overline{remaining \ free}}`, and the free side is exactly
`remaining` minus the local cut.  Product recursion instantiates the
local query with a c-component of `G \ X` and action `V \ S_i`; ancestral
restriction and 4.3 keep the outer outcome.
-/
theorem identifyFuel_eq_failed_site
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    Exists fun localOutcome =>
      Exists fun localAction =>
        NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter localOutcome fail.remaining))
            fail.remaining = true ∧
          NodeSet.equal fail.free
              (NodeSet.diff fail.remaining
                (NodeSet.inter localAction fail.remaining)) = true := by
  induction fuel generalizing remaining outcome action current with
  | zero =>
      simp [identifyFuel] at h
  | succ fuel ih =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [identifyFuel, hex, hkept] at h
              exact ih
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                outcome action
                (.marginalize
                  (NodeSet.diff remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)))
                  current)
                h
          | true =>
              cases hfc :
                  G.cComponents
                    (NodeSet.diff remaining
                      (NodeSet.inter action remaining)) with
              | nil =>
                  simp [identifyFuel, hex, hkept, hfc] at h
              | cons component rest =>
                  cases rest with
                  | nil =>
                      cases hsingle : G.isSingleCComponent remaining with
                      | true =>
                          simp [identifyFuel, hex, hkept, hfc, hsingle] at h
                          cases h
                          have hcomp : component =
                              NodeSet.diff remaining
                                (NodeSet.inter action remaining) :=
                            cComponents_eq_of_singleton G _ hfc
                          refine ⟨outcome, action, ?_, ?_⟩
                          · have hcut :
                                NodeSet.diff remaining component =
                                  NodeSet.inter action remaining := by
                              rw [hcomp, NodeSet.diff_diff]
                              exact NodeSet.inter_eq_of_subset
                                (NodeSet.inter_subset_right action remaining)
                            have heq :=
                              (NodeSet.equal_eq_true_iff _ _).mp hkept
                            have heq' :
                                G.ancestralSet remaining
                                  (GraphMutilation.bar
                                    (NodeSet.diff remaining component))
                                  (NodeSet.inter outcome remaining) =
                                  remaining := by
                              simpa [hcut] using heq
                            exact (NodeSet.equal_eq_true_iff _ _).mpr heq'
                          · exact (NodeSet.equal_eq_true_iff _ _).mpr hcomp
                      | false =>
                          cases hany :
                              (G.cComponents remaining).any
                                (fun piece =>
                                  NodeSet.equal piece component) with
                          | true =>
                              simp [identifyFuel, hex, hkept, hfc, hsingle,
                                hany] at h
                          | false =>
                              cases hcont :
                                  G.containingCComponent remaining
                                    component with
                              | none =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                              | some larger =>
                                  simp [identifyFuel, hex, hkept, hfc,
                                    hsingle, hany, hcont] at h
                                  exact ih larger outcome
                                    (NodeSet.inter
                                      (NodeSet.inter action remaining)
                                      larger)
                                    (chainProduct remaining larger) h
                  | cons component2 rest2 =>
                      simp [identifyFuel, hex, hkept, hfc] at h
                      have hin :
                          IdentificationOutcome.failed fail ∈
                            (component :: component2 :: rest2).map
                              (fun c =>
                                identifyFuel fuel G remaining c
                                  (NodeSet.diff remaining c) current) :=
                        IdentificationOutcome.combine_eq_failed _ _ h
                      rcases List.mem_map.mp hin with ⟨piece, _, hEq⟩
                      exact ih remaining piece
                        (NodeSet.diff remaining piece) current hEq

theorem identifyJoint_eq_failed_site
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : identifyJoint G q = IdentificationOutcome.failed fail) :
    Exists fun localOutcome =>
      Exists fun localAction =>
        NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter localOutcome fail.remaining))
            fail.remaining = true ∧
          NodeSet.equal fail.free
              (NodeSet.diff fail.remaining
                (NodeSet.inter localAction fail.remaining)) = true :=
  identifyFuel_eq_failed_site (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h

/--
An immediate 4.1 hedge: the working remaining set is already ancestral of
the local outcome in `G_{\overline{X}}`, that remaining set is a single
c-component, and `G \ X` has a unique free component.  The failure record
is exactly that remaining set together with `remaining \ X`.
-/
theorem identifyFuel_eq_failed_immediate_query_site
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S} {component : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = true)
    (h : identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    fail.remaining = remaining ∧
      fail.free = component ∧
        NodeSet.equal fail.free
            (NodeSet.diff fail.remaining
              (NodeSet.inter action fail.remaining)) = true ∧
          NodeSet.equal
            (G.ancestralSet fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter outcome fail.remaining))
            fail.remaining = true := by
  simp [identifyFuel, hex, hkept, hfc, hsingle] at h
  cases h
  have hcomp : component =
      NodeSet.diff remaining (NodeSet.inter action remaining) :=
    cComponents_eq_of_singleton G _ hfc
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact (NodeSet.equal_eq_true_iff _ _).mpr hcomp
  · have hcut :
        NodeSet.diff remaining component =
          NodeSet.inter action remaining := by
      rw [hcomp, NodeSet.diff_diff]
      exact NodeSet.inter_eq_of_subset
        (NodeSet.inter_subset_right action remaining)
    have heq := (NodeSet.equal_eq_true_iff _ _).mp hkept
    have heq' :
        G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.diff remaining component))
          (NodeSet.inter outcome remaining) = remaining := by
      simpa [hcut] using heq
    exact (NodeSet.equal_eq_true_iff _ _).mpr heq'

/--
A failing ID call whose remaining set is not ancestral of the local
outcome first restricts to that ancestral set.  Product-nested 4.1 and
the top-level shrink branch both instantiate this unpacking.
-/
theorem identifyFuel_eq_failed_of_shrink
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false)
    (h : identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    identifyFuel fuel G
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        outcome action
        (.marginalize
          (NodeSet.diff remaining
            (G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining)))
          current) =
      IdentificationOutcome.failed fail := by
  simp [identifyFuel, hex, hkept] at h
  exact h

/--
A 4.3 restriction whose containing c-component is found unpacks as the
nested ID run on that host, with action `X ∩ remaining ∩ larger`.
Immediate 4.1 and the chain-product success branch are excluded by the
Boolean hypotheses.
-/
theorem identifyFuel_eq_failed_of_restrict
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S} {component larger : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent remaining component = some larger)
    (h : identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    identifyFuel fuel G larger outcome
        (NodeSet.inter (NodeSet.inter action remaining) larger)
        (chainProduct remaining larger) =
      IdentificationOutcome.failed fail := by
  simp [identifyFuel, hex, hkept, hfc, hsingle, hany, hcont] at h
  exact h

/--
A product split with at least two free c-components unpacks as a nested
ID run on one of those pieces, with action `remaining \ piece`.
-/
theorem identifyFuel_eq_failed_of_product
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        component :: component2 :: rest)
    (h : identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    Exists fun piece =>
      piece ∈ component :: component2 :: rest ∧
        identifyFuel fuel G remaining piece
            (NodeSet.diff remaining piece) current =
          IdentificationOutcome.failed fail := by
  simp [identifyFuel, hex, hkept, hfc] at h
  have hin :
      IdentificationOutcome.failed fail ∈
        (component :: component2 :: rest).map (fun piece =>
          identifyFuel fuel G remaining piece
            (NodeSet.diff remaining piece) current) :=
    IdentificationOutcome.combine_eq_failed _ _ h
  rcases List.mem_map.mp hin with ⟨piece, hmem, hEq⟩
  exact ⟨piece, hmem, hEq⟩

/--
A successful ID call whose remaining set is not ancestral of the local
outcome first restricts to that ancestral set.  Dual of
`identifyFuel_eq_failed_of_shrink`.
-/
theorem identifyFuel_eq_identified_of_shrink
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {term : ProbabilityTerm S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false)
    (h : identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified term) :
    identifyFuel fuel G
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        outcome action
        (.marginalize
          (NodeSet.diff remaining
            (G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining)))
          current) =
      IdentificationOutcome.identified term := by
  simp [identifyFuel, hex, hkept] at h
  exact h

/--
Ancestral restriction whose nested remaining set no longer meets the
action is the empty-action base case on that ancestral set: ID returns
the observational marginal of the already-shrunk current expression.
Needs two fuel units (one shrink, one empty-action step).
-/
theorem identifyFuel_eq_identified_of_shrink_empty
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = false)
    (hexNested :
      NodeSet.isEmpty
        (NodeSet.inter action
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))) = true) :
    identifyFuel (fuel + 2) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff
            (G.ancestralSet remaining
              (GraphMutilation.bar (NodeSet.inter action remaining))
              (NodeSet.inter outcome remaining))
            (NodeSet.inter outcome
              (G.ancestralSet remaining
                (GraphMutilation.bar (NodeSet.inter action remaining))
                (NodeSet.inter outcome remaining))))
          (.marginalize
            (NodeSet.diff remaining
              (G.ancestralSet remaining
                (GraphMutilation.bar (NodeSet.inter action remaining))
                (NodeSet.inter outcome remaining)))
            current)) := by
  have hshrink :
      identifyFuel (fuel + 1 + 1) G remaining outcome action current =
        identifyFuel (fuel + 1) G
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining))
          outcome action
          (.marginalize
            (NodeSet.diff remaining
              (G.ancestralSet remaining
                (GraphMutilation.bar (NodeSet.inter action remaining))
                (NodeSet.inter outcome remaining)))
            current) := by
    simp [identifyFuel, hex, hkept]
  have hempty :=
    identifyFuel_eq_identified_of_empty_action fuel G
      (G.ancestralSet remaining
        (GraphMutilation.bar (NodeSet.inter action remaining))
        (NodeSet.inter outcome remaining))
      outcome action
      (.marginalize
        (NodeSet.diff remaining
          (G.ancestralSet remaining
            (GraphMutilation.bar (NodeSet.inter action remaining))
            (NodeSet.inter outcome remaining)))
        current)
      hexNested
  rw [show fuel + 2 = fuel + 1 + 1 from rfl, hshrink, hempty]

/--
ID step 4.2: the unique free c-component is already a c-component of the
working remaining graph, so the answer is the chain-rule factorization
`Q[S]` marginalized to the local outcome.
-/
theorem identifyFuel_eq_identified_of_chain
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {component : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = true) :
    identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff component (NodeSet.inter outcome remaining))
          (chainProduct remaining component)) := by
  simp [identifyFuel, hex, hkept, hfc, hsingle, hany]

/--
A 4.3 restriction whose containing c-component is found unpacks as the
nested ID run on that host.  Dual of `identifyFuel_eq_failed_of_restrict`.
-/
theorem identifyFuel_eq_identified_of_restrict
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {term : ProbabilityTerm S} {component larger : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent remaining component = some larger)
    (h : identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified term) :
    identifyFuel fuel G larger outcome
        (NodeSet.inter (NodeSet.inter action remaining) larger)
        (chainProduct remaining larger) =
      IdentificationOutcome.identified term := by
  simp [identifyFuel, hex, hkept, hfc, hsingle, hany, hcont] at h
  exact h

/--
A 4.3 restriction whose nested remaining set misses the restricted
action is the empty-action base case on that host, with current
expression the chain-rule joint on the host.  Needs two fuel units.
-/
theorem identifyFuel_eq_identified_of_restrict_empty
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {component larger : NodeSet S}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (hsingle : G.isSingleCComponent remaining = false)
    (hany :
      (G.cComponents remaining).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent remaining component = some larger)
    (hexNested :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter action remaining) larger) = true) :
    identifyFuel (fuel + 2) G remaining outcome action current =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff larger (NodeSet.inter outcome larger))
          (chainProduct remaining larger)) := by
  have hrestrict :
      identifyFuel (fuel + 1 + 1) G remaining outcome action current =
        identifyFuel (fuel + 1) G larger outcome
          (NodeSet.inter (NodeSet.inter action remaining) larger)
          (chainProduct remaining larger) := by
    simp [identifyFuel, hex, hkept, hfc, hsingle, hany, hcont]
  have hexNested' :
      NodeSet.isEmpty
        (NodeSet.inter
          (NodeSet.inter (NodeSet.inter action remaining) larger)
          larger) = true := by
    simpa [NodeSet.inter_idempotent_right] using hexNested
  have hempty :=
    identifyFuel_eq_identified_of_empty_action fuel G larger outcome
      (NodeSet.inter (NodeSet.inter action remaining) larger)
      (chainProduct remaining larger) hexNested'
  rw [show fuel + 2 = fuel + 1 + 1 from rfl, hrestrict, hempty]

/--
A product split with at least two free c-components unpacks as identified
runs on those pieces, assembled by `productTerms` and marginalized off
`V \ (Y ∪ X)` in the working remaining set.  Dual of
`identifyFuel_eq_failed_of_product`.
-/
theorem identifyFuel_eq_identified_of_product
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {term : ProbabilityTerm S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty (NodeSet.inter action remaining) = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet remaining
          (GraphMutilation.bar (NodeSet.inter action remaining))
          (NodeSet.inter outcome remaining))
        remaining = true)
    (hfc :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        component :: component2 :: rest)
    (h : identifyFuel (fuel + 1) G remaining outcome action current =
      IdentificationOutcome.identified term) :
    Exists fun terms =>
      term =
          ProbabilityTerm.marginalize
            (NodeSet.diff remaining
              (NodeSet.union (NodeSet.inter outcome remaining)
                (NodeSet.inter action remaining)))
            (productTerms terms) ∧
        (component :: component2 :: rest).map (fun piece =>
            identifyFuel fuel G remaining piece
              (NodeSet.diff remaining piece) current) =
          terms.map IdentificationOutcome.identified := by
  simp [identifyFuel, hex, hkept, hfc] at h
  rcases IdentificationOutcome.combine_eq_identified _ _ h with
    ⟨terms, hmap, hterm⟩
  exact ⟨terms, hterm, hmap⟩

/--
On a vertex set contained in both `larger` and `remaining`, intersecting
the 4.3 restricted action `X ∩ remaining ∩ larger` agrees with intersecting
the outer action.
-/
theorem inter_action_eq_of_contained
    (action remaining larger nodes : NodeSet S)
    (hL : NodeSet.Subset nodes larger)
    (hR : NodeSet.Subset nodes remaining) :
    NodeSet.inter
        (NodeSet.inter (NodeSet.inter action remaining) larger) nodes =
      NodeSet.inter action nodes := by
  funext i
  cases hn : nodes i with
  | false =>
      simp [NodeSet.inter, hn]
  | true =>
      simp [NodeSet.inter, hn, hL i hn, hR i hn]

/--
If the recorded remaining set is still the working remaining set of the
call that failed, and the free side is `remaining \ X` for that call's
action, then the remaining set is ancestral of the call's outcome in
`G_{\overline{cut}}`.  Ancestral restriction cannot produce this
situation: it strictly shrinks the working remaining set.  Immediate 4.1,
4.3 with `larger` restored to `remaining`, and product with an unshrunk
remaining set all have `hkept`, which is the required ancestry.
-/
theorem identifyFuel_eq_failed_query_of_remaining_eq
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining remaining = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter action fail.remaining)) = true) :
    NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter outcome fail.remaining))
        fail.remaining = true := by
  cases fuel with
  | zero =>
      simp [identifyFuel] at h
  | succ fuel =>
      cases hex :
          NodeSet.isEmpty (NodeSet.inter action remaining) with
      | true =>
          simp [identifyFuel, hex] at h
      | false =>
          cases hkept :
              NodeSet.equal
                (G.ancestralSet remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining))
                remaining with
          | false =>
              simp [identifyFuel, hex, hkept] at h
              have nested :=
                identifyFuel_eq_failed fuel G
                  (G.ancestralSet remaining
                    (GraphMutilation.bar (NodeSet.inter action remaining))
                    (NodeSet.inter outcome remaining))
                  outcome action
                  (.marginalize
                    (NodeSet.diff remaining
                      (G.ancestralSet remaining
                        (GraphMutilation.bar (NodeSet.inter action remaining))
                        (NodeSet.inter outcome remaining)))
                    current)
                  h
              have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
              have hsubset :
                  NodeSet.Subset remaining
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining)) := by
                intro i hi
                have hi' : fail.remaining i = true := by
                  rw [heqR]
                  exact hi
                exact nested.2 i hi'
              have hsubset' :=
                ancestralSet_subset G remaining
                  (GraphMutilation.bar (NodeSet.inter action remaining))
                  (NodeSet.inter outcome remaining)
              have hkeptTrue :
                  NodeSet.equal
                    (G.ancestralSet remaining
                      (GraphMutilation.bar (NodeSet.inter action remaining))
                      (NodeSet.inter outcome remaining))
                    remaining = true :=
                Bool.and_eq_true_iff.mpr
                  ⟨(NodeSet.subsetBool_eq_true_iff _ _).mpr hsubset',
                    (NodeSet.subsetBool_eq_true_iff _ _).mpr hsubset⟩
              exact False.elim (Bool.false_ne_true (hkept.symm.trans hkeptTrue))
          | true =>
              have heqR := (NodeSet.equal_eq_true_iff _ _).mp heq
              have hfreeEq := (NodeSet.equal_eq_true_iff _ _).mp hfree
              have hfreeEq' :
                  fail.free =
                    NodeSet.diff remaining
                      (NodeSet.inter action remaining) := by
                rw [hfreeEq, heqR]
              have hcut :
                  NodeSet.diff remaining fail.free =
                    NodeSet.inter action remaining := by
                rw [hfreeEq', NodeSet.diff_diff]
                exact NodeSet.inter_eq_of_subset
                  (NodeSet.inter_subset_right action remaining)
              have hkeptEq := (NodeSet.equal_eq_true_iff _ _).mp hkept
              have hanc :
                  G.ancestralSet fail.remaining
                    (GraphMutilation.bar
                      (NodeSet.diff fail.remaining fail.free))
                    (NodeSet.inter outcome fail.remaining) =
                    fail.remaining := by
                rw [heqR, hcut]
                exact hkeptEq
              exact (NodeSet.equal_eq_true_iff _ _).mpr hanc

/--
Thinning always returns the bidirected component of `seedY` inside some
residual host that still contains `seedY`.  That is the data needed to treat
the result as a `CForest` host, once the one-child Boolean succeeds.
-/
theorem thinTowardForest_exists_host
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) (fuel : Nat)
    (hY : nodes seedY = true) :
    Exists fun host =>
      host seedY = true ∧
        thinTowardForest G nodes seedY seedKeep fuel =
          G.cComponentOf host seedY := by
  induction fuel generalizing nodes with
  | zero =>
      exact ⟨nodes, hY, rfl⟩
  | succ fuel ih =>
      cases hcond :
          atMostOneDirectedChildBool nodes &&
            G.bidirectedReachableWithin nodes seedY seedKeep with
      | true =>
          refine ⟨nodes, hY, ?_⟩
          simp [thinTowardForest, hcond]
      | false =>
          cases hdrop : extraChildToDrop G nodes seedY seedKeep with
          | none =>
              refine ⟨nodes, hY, ?_⟩
              simp [thinTowardForest, hcond, hdrop]
          | some child =>
              have hne : child ≠ seedY :=
                extraChildToDrop_ne_seedY G nodes seedY seedKeep child hdrop
              have inDiff :
                  NodeSet.diff nodes (NodeSet.singleton child) seedY = true := by
                refine Bool.and_eq_true_iff.mpr ⟨hY, ?_⟩
                have notChild : NodeSet.singleton child seedY = false :=
                  Bool.eq_false_iff.mpr fun htrue =>
                    hne ((NodeSet.singleton_eq_true_iff child seedY).mp
                      htrue).symm
                simp [notChild]
              have hY' :
                  G.cComponentOf
                    (NodeSet.diff nodes (NodeSet.singleton child))
                    seedY seedY = true :=
                cComponentOf_root_mem G _ inDiff
              have hostFromIH :=
                ih (G.cComponentOf
                  (NodeSet.diff nodes (NodeSet.singleton child)) seedY) hY'
              simpa [thinTowardForest, hcond, hdrop] using hostFromIH

theorem thinTowardForest_seed_mem
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) (fuel : Nat)
    (hY : nodes seedY = true) :
    thinTowardForest G nodes seedY seedKeep fuel seedY = true := by
  rcases thinTowardForest_exists_host G nodes seedY seedKeep fuel hY with
    ⟨host, hHost, hEq⟩
  rw [hEq]
  exact cComponentOf_root_mem G host hHost

/-- Thinning only drops vertices, never adds them. -/
theorem thinTowardForest_subset
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) (fuel : Nat)
    (hY : nodes seedY = true) :
    NodeSet.Subset (thinTowardForest G nodes seedY seedKeep fuel) nodes := by
  induction fuel generalizing nodes with
  | zero =>
      intro i hi
      exact cComponentOf_subset G nodes hi
  | succ fuel ih =>
      cases hcond :
          atMostOneDirectedChildBool nodes &&
            G.bidirectedReachableWithin nodes seedY seedKeep with
      | true =>
          intro i hi
          simp [thinTowardForest, hcond] at hi
          exact cComponentOf_subset G nodes hi
      | false =>
          cases hdrop : extraChildToDrop G nodes seedY seedKeep with
          | none =>
              intro i hi
              simp [thinTowardForest, hcond, hdrop] at hi
              exact cComponentOf_subset G nodes hi
          | some child =>
              have hne : child ≠ seedY :=
                extraChildToDrop_ne_seedY G nodes seedY seedKeep child hdrop
              have inDiff :
                  NodeSet.diff nodes (NodeSet.singleton child) seedY = true := by
                refine Bool.and_eq_true_iff.mpr ⟨hY, ?_⟩
                have notChild : NodeSet.singleton child seedY = false :=
                  Bool.eq_false_iff.mpr fun htrue =>
                    hne ((NodeSet.singleton_eq_true_iff child seedY).mp
                      htrue).symm
                simp [notChild]
              have hY' :
                  G.cComponentOf
                    (NodeSet.diff nodes (NodeSet.singleton child))
                    seedY seedY = true :=
                cComponentOf_root_mem G _ inDiff
              intro i hi
              have hi' :
                  thinTowardForest G
                    (G.cComponentOf
                      (NodeSet.diff nodes (NodeSet.singleton child)) seedY)
                    seedY seedKeep fuel i = true := by
                simpa [thinTowardForest, hcond, hdrop] using hi
              have inComp :=
                ih (G.cComponentOf
                  (NodeSet.diff nodes (NodeSet.singleton child)) seedY)
                  hY' i hi'
              exact NodeSet.diff_subset_left _ _ i
                (cComponentOf_subset G _ inComp)

theorem atMostOneDirectedChild_of_bool (G : ObservedGraph S)
    (nodes : NodeSet S) (h : atMostOneDirectedChildBool nodes = true) :
    AtMostOneDirectedChild G nodes := by
  intro parent child₁ child₂ hp h1 h2 e1 e2
  have parentMem : parent ∈ NodeSet.members nodes :=
    (NodeSet.mem_members_iff nodes parent).mpr hp
  have parentOk :
      (match directedChildren nodes parent with
        | [] => true
        | [_] => true
        | _ :: _ :: _ => false) = true :=
    (List.all_eq_true.mp h) parent parentMem
  have mem1 : child₁ ∈ directedChildren nodes parent := by
    simp [directedChildren, List.mem_filter, NodeSet.mem_members_iff, h1, e1]
  have mem2 : child₂ ∈ directedChildren nodes parent := by
    simp [directedChildren, List.mem_filter, NodeSet.mem_members_iff, h2, e2]
  cases hcs : directedChildren nodes parent with
  | nil =>
      rw [hcs] at mem1
      cases mem1
  | cons c rest =>
      cases rest with
      | nil =>
          have eq1 : child₁ = c := by
            have : child₁ ∈ [c] := by
              rw [hcs] at mem1
              exact mem1
            simpa [List.mem_singleton] using this
          have eq2 : child₂ = c := by
            have : child₂ ∈ [c] := by
              rw [hcs] at mem2
              exact mem2
            simpa [List.mem_singleton] using this
          exact eq1.trans eq2.symm
      | cons _ _ =>
          simp [hcs] at parentOk

theorem forestSinks_iff_isRootIn (G : ObservedGraph S) (nodes : NodeSet S)
    (i : Fin S.count) :
    forestSinks nodes i = true ↔ IsRootIn G nodes i := by
  constructor
  · intro h
    have parts := Bool.and_eq_true_iff.mp h
    have noChild :
        (NodeSet.members nodes).any (fun child => S.directed i child) = false := by
      cases hany : (NodeSet.members nodes).any (fun child => S.directed i child)
      · rfl
      · simp [forestSinks, parts.1, hany] at h
    refine ⟨parts.1, fun child hc => ?_⟩
    have childMem : child ∈ NodeSet.members nodes :=
      (NodeSet.mem_members_iff nodes child).mpr hc
    have predFalse : S.directed i child = false :=
      Bool.eq_false_iff.mpr
        (List.any_eq_false.mp noChild child childMem)
    exact predFalse
  · intro hroot
    refine Bool.and_eq_true_iff.mpr ⟨hroot.1, ?_⟩
    have anyFalse :
        (NodeSet.members nodes).any (fun child => S.directed i child) = false := by
      refine List.any_eq_false.mpr ?_
      intro child childMem
      exact Bool.eq_false_iff.mp
        (hroot.2 child ((NodeSet.mem_members_iff nodes child).mp childMem))
    simp [anyFalse]

theorem hedgeSmallOf_subset_large (G : ObservedGraph S)
    (q : JointKernelQuery S) (fail : IdentificationFail S) :
    NodeSet.Subset (hedgeSmallOf G q fail) (hedgeLargeOf G q fail) := by
  intro i hi
  cases hseed : forestSeed q.outcome
      (NodeSet.diff (hedgeLargeOf G q fail) q.action) with
  | none =>
      simp [hedgeSmallOf, hseed] at hi
      exact NodeSet.diff_subset_left _ q.action i hi
  | some seed =>
      simp [hedgeSmallOf, hseed] at hi
      exact NodeSet.diff_subset_left _ q.action i
        (cComponentOf_subset G _ hi)

theorem hedgeSmallOf_avoids_action (G : ObservedGraph S)
    (q : JointKernelQuery S) (fail : IdentificationFail S) :
    NodeSet.Disjoint (hedgeSmallOf G q fail) q.action :=
  NodeSet.Disjoint.of_subset_left (NodeSet.Disjoint.diff_right _ _)
    (by
      intro i hi
      cases hseed : forestSeed q.outcome
          (NodeSet.diff (hedgeLargeOf G q fail) q.action) with
      | none =>
          simp [hedgeSmallOf, hseed] at hi
          exact hi
      | some seed =>
          simp [hedgeSmallOf, hseed] at hi
          exact cComponentOf_subset G _ hi)

theorem hedgeSmallOf_subsetBool
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    NodeSet.subsetBool (hedgeSmallOf G q fail) (hedgeLargeOf G q fail) =
      true :=
  (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (hedgeSmallOf_subset_large G q fail)

theorem hedgeSmallOf_disjointBool
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    NodeSet.disjointBool (hedgeSmallOf G q fail) q.action = true :=
  (NodeSet.disjointBool_eq_true_iff _ _).mpr
    (hedgeSmallOf_avoids_action G q fail)

/--
The extracted large side remains inside the ID-failure remaining set, so
it is among the vertex assignments enumerated by `findHedgeWitnessSets`.
-/
theorem hedgeLargeOf_subset_remaining
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    NodeSet.Subset (hedgeLargeOf G q fail) fail.remaining := by
  cases hY : forestSeed q.outcome fail.remaining with
  | none =>
      intro i hi
      simpa [hedgeLargeOf, hY] using hi
  | some seedY =>
      have hYmem : fail.remaining seedY = true :=
        forestSeed_mem q.outcome fail.remaining hY
      cases hX : NodeSet.firstMember (NodeSet.inter fail.remaining q.action) with
      | none =>
          intro i hi
          simp [hedgeLargeOf, hY, hX] at hi
          exact thinTowardForest_subset G fail.remaining seedY seedY
            (NodeSet.members fail.remaining).length hYmem i hi
      | some seedX =>
          intro i hi
          simp [hedgeLargeOf, hY, hX] at hi
          exact thinTowardForest_subset G fail.remaining seedY seedX
            (NodeSet.members fail.remaining).length hYmem i hi

/--
Canonical candidate assembled from greedy thinning.  Search completeness
reduces `identifyJoint = failed → hedgeWitness? = some` to the Boolean
tests on this (or any other enumerated) selection.
-/
def thinnedHedgeSelection (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) : HedgeSelection S where
  large := hedgeLargeOf G q fail
  small := hedgeSmallOf G q fail
  child := inducedChild (hedgeLargeOf G q fail)

theorem thinnedHedgeSelection_subset_remaining
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    NodeSet.Subset (thinnedHedgeSelection G q fail).large fail.remaining :=
  hedgeLargeOf_subset_remaining G q fail

theorem findHedgeWitnessSets_eq_some_of_thinned
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S)
    (htests :
      hedgeTestsHold G q (thinnedHedgeSelection G q fail) = true) :
    Exists fun found => findHedgeWitnessSets G q fail = some found :=
  findHedgeWitnessSets_eq_some_of_selection G q fail
    (thinnedHedgeSelection G q fail)
    (thinnedHedgeSelection_subset_remaining G q fail) htests

/--
Canonical candidate assembled from the ID-failure record itself: the
failing remaining c-component, the recorded free component, and the
child-closed first-successor map.  This is the most general vertex pair
the failure data determines; greedy thinning is a further specialization.
-/
def failedHedgeSelection (fail : IdentificationFail S) : HedgeSelection S where
  large := fail.remaining
  small := fail.free
  child := closedForestChild fail.remaining fail.free

theorem failedHedgeSelection_subset_remaining
    (fail : IdentificationFail S) :
    NodeSet.Subset (failedHedgeSelection fail).large fail.remaining :=
  fun _i hi => hi

theorem findHedgeWitnessSets_eq_some_of_failed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S)
    (htests : hedgeTestsHold G q (failedHedgeSelection fail) = true) :
    Exists fun found => findHedgeWitnessSets G q fail = some found :=
  findHedgeWitnessSets_eq_some_of_selection G q fail
    (failedHedgeSelection fail)
    (failedHedgeSelection_subset_remaining fail) htests

theorem identifyJoint_eq_failed_free_subset
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.Subset fail.free fail.remaining :=
  (identifyFuel_eq_failed_free (identificationFuel S) G NodeSet.full
    q.outcome q.action (observationalJointTerm S) h).1

theorem failedHedgeSelection_cut_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty
      (NodeSet.diff (failedHedgeSelection fail).large
        (failedHedgeSelection fail).small) = false :=
  identifyJoint_eq_failed_cut_nonempty G q hfail

/--
If every original-action vertex in the remaining set lies in the cut,
the free side avoids the original action.
-/
theorem failedHedgeSelection_avoids_action_of_cut
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : identifyJoint G q = IdentificationOutcome.failed fail)
    (hcut :
      NodeSet.Subset (NodeSet.inter q.action fail.remaining)
        (NodeSet.diff fail.remaining fail.free)) :
    NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
      true :=
  (NodeSet.disjointBool_eq_true_iff _ _).mpr (fun i hi => by
    have hrem : fail.remaining i = true :=
      identifyJoint_eq_failed_free_subset G q hfail i hi
    cases ha : q.action i with
    | false =>
        rfl
    | true =>
        have hinter : NodeSet.inter q.action fail.remaining i = true :=
          Bool.and_eq_true_iff.mpr ⟨ha, hrem⟩
        have hcuti := hcut i hinter
        have hfreeF : fail.free i = false := by
          have parts := Bool.and_eq_true_iff.mp hcuti
          cases hf : fail.free i with
          | false =>
              rfl
          | true =>
              have : (!fail.free i) = true := parts.2
              simp [hf] at this
        exact False.elim (Bool.false_ne_true (hfreeF.symm.trans hi)))

/--
If the nonempty cut sits inside the original action, the remaining set
meets that action.
-/
theorem failedHedgeSelection_meets_action_of_cut
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : identifyJoint G q = IdentificationOutcome.failed fail)
    (hsub :
      NodeSet.Subset (NodeSet.diff fail.remaining fail.free) q.action) :
    NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true := by
  rcases (NodeSet.isEmpty_eq_false_iff _).mp
      (failedHedgeSelection_cut_nonempty G q hfail) with ⟨i, hi⟩
  have hrem : fail.remaining i = true :=
    NodeSet.diff_subset_left fail.remaining fail.free i hi
  have hact : q.action i = true := hsub i hi
  exact (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨i, hrem, hact⟩

/-- Incoming-deleted directed edges of `G_{\overline{cut}}`. -/
theorem observedDirectedEdge_bar
    (G : ObservedGraph S) (cut : NodeSet S)
    {parent child : Fin S.count} :
    G.observedDirectedEdge (GraphMutilation.bar cut) parent child = true ↔
      S.directed parent child = true ∧ cut child = false := by
  constructor
  · intro h
    simpa [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
      NodeSet.empty] using h
  · intro h
    simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
      NodeSet.empty, h.1, h.2]

/--
On remaining vertices, incoming deletion of `X ∩ remaining` agrees with
incoming deletion of `X`.
-/
theorem observedDirectedEdge_bar_inter
    (G : ObservedGraph S) (nodes action : NodeSet S)
    {parent child : Fin S.count}
    (hchild : nodes child = true) :
    G.observedDirectedEdge
        (GraphMutilation.bar (NodeSet.inter action nodes)) parent child =
      G.observedDirectedEdge (GraphMutilation.bar action) parent child := by
  simp [ObservedGraph.observedDirectedEdge, GraphMutilation.bar,
    NodeSet.empty, NodeSet.inter, hchild]

theorem directedEdgeWithin_bar_inter
    (G : ObservedGraph S) (nodes action : NodeSet S)
    (parent child : Fin S.count) :
    G.directedEdgeWithin nodes
        (GraphMutilation.bar (NodeSet.inter action nodes)) parent child =
      G.directedEdgeWithin nodes (GraphMutilation.bar action)
        parent child := by
  simp [ObservedGraph.directedEdgeWithin]
  cases hch : nodes child with
  | false =>
      simp
  | true =>
      simp [observedDirectedEdge_bar_inter G nodes action hch]

theorem ancestralSet_bar_inter
    (G : ObservedGraph S) (nodes action targets : NodeSet S) :
    G.ancestralSet nodes
        (GraphMutilation.bar (NodeSet.inter action nodes)) targets =
      G.ancestralSet nodes (GraphMutilation.bar action) targets := by
  funext i
  have hedge :
      G.directedEdgeWithin nodes
        (GraphMutilation.bar (NodeSet.inter action nodes)) =
      G.directedEdgeWithin nodes (GraphMutilation.bar action) :=
    funext fun parent =>
      funext fun child =>
        directedEdgeWithin_bar_inter G nodes action parent child
  simp [ObservedGraph.ancestralSet, ObservedGraph.ancestorOfWithin, hedge]

/-- Membership in an ancestral remaining set is directed reachability. -/
theorem ancestorOfWithin_of_ancestralSet
    (G : ObservedGraph S) (nodes : NodeSet S)
    (m : GraphMutilation S) (targets : NodeSet S)
    (heq : NodeSet.equal (G.ancestralSet nodes m targets) nodes = true)
    {i : Fin S.count} (hi : nodes i = true) :
    G.ancestorOfWithin nodes m targets i = true := by
  have eq : G.ancestralSet nodes m targets = nodes :=
    (NodeSet.equal_eq_true_iff _ _).mp heq
  have : G.ancestralSet nodes m targets i = true := by
    rw [eq]
    exact hi
  simpa [ObservedGraph.ancestralSet] using this

end Causality
end Thesis
