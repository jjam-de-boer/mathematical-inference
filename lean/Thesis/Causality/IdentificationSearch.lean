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

/--
Chain-rule conditioner for `node`: every topologically earlier vertex that
still belongs to the current remaining set.  Signature nodes are already
topologically numbered by `directed_earlier`.
-/
def chainCondition (remaining : NodeSet S) (node : Fin S.count) : NodeSet S :=
  fun j => remaining j && decide (j.val < node.val)

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

end Causality
end Thesis
