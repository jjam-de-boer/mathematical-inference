import Thesis.Causality.ExecutedMultiworld.Linking

namespace Thesis
namespace Causality

open Probability

/-!
Literal exogenous-root and occurrence-world construction from an empty mode.

Unlike the from-factual route, this construction begins with zero observed and
zero latent coordinates. It explicitly learns every required source root and
occurrence node before linking, configuring, and reindexing them. Its purpose
is to show that the multiworld endpoint can be obtained by literal typed edits,
not merely by extending a pre-existing copy of the source model.

Reading order: first construct the literal empty mode; then append one root
for every source latent coordinate; then append isolated observed occurrence
nodes and install their directed and latent links; finally install copied
mechanisms, reindex the source belief, and prove agreement with the reference
occurrence-multiworld evaluator.  The apparently numerous coordinate maps are
necessary because each typed edit changes a dependent signature.
-/

/-! ## Literal construction from an empty causal mode -/

/-!
`EmptyCausalMode` is deliberately a genuine zero-coordinate SCM rather than
an abbreviation for an arbitrary source mode.  Consequently every later root
and observed node has an explicit provenance-producing creation transition.
-/

namespace EmptyCausalMode

def signature : ObservedSignature where
  count := 0
  Value := Fin.elim0
  valueEnumeration := fun node => Fin.elim0 node
  value_complete := fun node => Fin.elim0 node
  value_nodup := fun node => Fin.elim0 node
  defaultValue := fun node => Fin.elim0 node
  valueDecidableEq := fun node => Fin.elim0 node
  directed := fun node => Fin.elim0 node
  directed_earlier := fun {parent} => Fin.elim0 parent

def latent : LatentExtension signature where
  count := 0
  Value := Fin.elim0
  valueEnumeration := fun root => Fin.elim0 root
  value_complete := fun root => Fin.elim0 root
  valueDecidableEq := fun root => Fin.elim0 root
  incident := fun root => Fin.elim0 root

def factor (root : Fin latent.count) :
    FiniteProbRecord (latent.Value root) :=
  Fin.elim0 root

def model : ExactModel signature where
  latent := latent
  factor := factor
  prior := FiniteProduct.record 0 latent.Value factor
  product_law := FiniteProduct.record_rectangular_probVal
    0 latent.Value factor
  mechanism := fun child => Fin.elim0 child

def mode : CausalMode signature :=
  ⟨"empty-causal-mode", CausalEpistemicRecord.initial model⟩

theorem mode_noActiveIntervention :
    AtomicIntervention.NoActiveIntervention mode := by
  intro child
  exact Fin.elim0 child

end EmptyCausalMode

/-- Extract the creation data for one existing root of a source model. -/
def FiniteLatentSCM.exogenousSpec (M : ExactModel S)
    (root : Fin M.latent.count) : ExogenousVariableSpec where
  Value := M.latent.Value root
  valueEnumeration := M.latent.valueEnumeration root
  value_complete := M.latent.value_complete root
  valueDecidableEq := M.latent.valueDecidableEq root
  factor := M.factor root

/-! ## Recreating the source latent roots -/

/--
Append one fresh exogenous variable for every source-root occurrence.  This is
an actual path of `learningExogenous` edits, not a pre-populated latent record.
Besides the endpoint and path, the structure records exactly where old and
new root coordinates land after the recursive construction.
-/
structure SourceRootsConstruction
    (M : ExactModel template) {S : ObservedSignature}
    (source : CausalMode S) (roots : List (Fin M.latent.count)) where
  target : CausalMode S
  path : CausalEditPath source target
  count_eq :
    target.record.model.latent.count =
      source.record.model.latent.count + roots.length
  oldRoot :
    Fin source.record.model.latent.count ->
      Fin target.record.model.latent.count
  oldRoot_val : forall root, (oldRoot root).val = root.val
  oldValue_eq : forall root,
    target.record.model.latent.Value (oldRoot root) =
      source.record.model.latent.Value root
  itemRoot : Fin roots.length -> Fin target.record.model.latent.count
  itemRoot_val : forall index,
    (itemRoot index).val =
      source.record.model.latent.count + index.val
  itemValue_eq : forall index,
    target.record.model.latent.Value (itemRoot index) =
      M.latent.Value (roots.get index)

namespace SourceRootsConstruction

/--
Recursive root creation.  The empty case is the identity path.  The cons case
creates the head root and then interprets the tail's coordinate invariants in
the one-root-larger target signature.
-/
def build (M : ExactModel template) {S : ObservedSignature}
    (source : CausalMode S) :
    (roots : List (Fin M.latent.count)) ->
      SourceRootsConstruction M source roots
  | [] =>
      { target := source
        path := .nil source
        count_eq := by simp
        oldRoot := fun root => root
        oldRoot_val := fun _ => rfl
        oldValue_eq := fun _ => rfl
        itemRoot := fun index => Fin.elim0 index
        itemRoot_val := fun index => Fin.elim0 index
        itemValue_eq := fun index => Fin.elim0 index }
  | root :: rest =>
      let spec := M.exogenousSpec root
      let transition := spec.learnTransition source "create-exogenous"
      let tail := build M transition.target rest
      { target := tail.target
        path := (CausalEditPath.single transition).append tail.path
        count_eq := by
          have stepCount :
              transition.target.record.model.latent.count =
                source.record.model.latent.count + 1 :=
            rfl
          rw [tail.count_eq]
          rw [stepCount]
          simp
          omega
        oldRoot := fun sourceRoot =>
          tail.oldRoot (spec.oldSource source.record.model sourceRoot)
        oldRoot_val := fun sourceRoot => by
          rw [tail.oldRoot_val]
          rfl
        oldValue_eq := fun sourceRoot =>
          Eq.trans
            (tail.oldValue_eq
              (spec.oldSource source.record.model sourceRoot))
            (spec.extendLatent_value_old source.record.model sourceRoot)
        itemRoot := fun index =>
          Fin.cases
            (tail.oldRoot (spec.newSource source.record.model))
            (fun restIndex => tail.itemRoot restIndex)
            index
        itemRoot_val := fun index => by
          refine Fin.cases ?_ (fun restIndex => ?_) index
          · simp only [Fin.cases_zero]
            rw [tail.oldRoot_val]
            rfl
          · simp only [Fin.cases_succ]
            rw [tail.itemRoot_val]
            have stepCount :
                transition.target.record.model.latent.count =
                  source.record.model.latent.count + 1 :=
              rfl
            rw [stepCount]
            simp
            omega
        itemValue_eq := fun index => by
          refine Fin.cases ?_ (fun restIndex => ?_) index
          · exact Eq.trans
              (tail.oldValue_eq
                (spec.newSource source.record.model))
              (spec.extendLatent_value_new source.record.model)
          · exact tail.itemValue_eq restIndex }

/-- Exogenous-root creation preserves absence of a compact intervention. -/
theorem build_noActiveIntervention
    (M : ExactModel template) {S : ObservedSignature}
    (source : CausalMode S)
    (empty : AtomicIntervention.NoActiveIntervention source) :
    (roots : List (Fin M.latent.count)) ->
      AtomicIntervention.NoActiveIntervention (build M source roots).target
  | [] => by
      rw [build]
      exact empty
  | root :: rest => by
      let spec := M.exogenousSpec root
      let transition := spec.learnTransition source "create-exogenous"
      have stepEmpty : AtomicIntervention.NoActiveIntervention transition.target :=
        AtomicIntervention.exogenousLearning_noActiveIntervention
          source spec "create-exogenous" empty
      rw [build]
      dsimp only
      exact build_noActiveIntervention M transition.target stepEmpty rest

/-- The special case that recreates every source root in its canonical order. -/
abbrev All (M : ExactModel template) :=
  SourceRootsConstruction M EmptyCausalMode.mode
    (List.finRange M.latent.count)

def all (M : ExactModel template) : All M :=
  build M EmptyCausalMode.mode (List.finRange M.latent.count)

theorem all_noActiveIntervention (M : ExactModel template) :
    AtomicIntervention.NoActiveIntervention (all M).target :=
  build_noActiveIntervention M EmptyCausalMode.mode
    EmptyCausalMode.mode_noActiveIntervention
    (List.finRange M.latent.count)

def sourceRoot (built : All M)
    (root : Fin M.latent.count) :
    Fin built.target.record.model.latent.count :=
  built.itemRoot (finRangePosition root)

theorem sourceRoot_val (built : All M)
    (root : Fin M.latent.count) :
    (built.sourceRoot root).val = root.val := by
  rw [sourceRoot, built.itemRoot_val]
  simp [EmptyCausalMode.mode, CausalEpistemicRecord.initial,
    EmptyCausalMode.model,
    EmptyCausalMode.latent, finRangePosition]

theorem sourceRootValue_eq (built : All M)
    (root : Fin M.latent.count) :
    built.target.record.model.latent.Value (built.sourceRoot root) =
      M.latent.Value root := by
  exact Eq.trans
    (built.itemValue_eq (finRangePosition root))
    (congrArg M.latent.Value (finRange_get_position root))

theorem all_count_eq (built : All M) :
    built.target.record.model.latent.count = M.latent.count := by
  simpa [EmptyCausalMode.mode, CausalEpistemicRecord.initial,
    EmptyCausalMode.model,
    EmptyCausalMode.latent] using built.count_eq

/--
The all-roots construction has exactly the source's root count, hence its
recorded forward map is a finite-index equivalence rather than only an
embedding.
-/
def sourceRootEquiv (built : All M) :
    AtomicIntervention.FinIndexEquiv M.latent.count
      built.target.record.model.latent.count where
  toFun := built.sourceRoot
  invFun := fun root => Fin.cast built.all_count_eq root
  left_inv := by
    intro root
    apply Fin.ext
    exact built.sourceRoot_val root
  right_inv := by
    intro root
    apply Fin.ext
    rw [built.sourceRoot_val]
    rfl

end SourceRootsConstruction

namespace EmptyOccurrenceConstruction

/-! ## Allocating isolated occurrence coordinates -/

/-!
The reference occurrence multiworld has one encoded coordinate for each
world/node pair.  Here those coordinates are first learned as terminal
endogenous variables with no edges; the next section computes the edges that
must subsequently be installed.
-/

abbrev World (M : ExactModel S) (event : CounterfactualEvent S) :=
  M.occurrenceMultiworld event

abbrev EncodingSignature (M : ExactModel S)
    (event : CounterfactualEvent S) :=
  OccurrenceMultiworld.Encoding.signature (World M event)

abbrev Nodes (M : ExactModel S) (event : CounterfactualEvent S)
    (roots : SourceRootsConstruction.All M) :=
  TerminalListConstruction
    (EncodingSignature M event).isolatedNodeFamily roots.target
    (List.finRange (EncodingSignature M event).count)

/-- Create one isolated endpoint node for every encoded occurrence coordinate. -/
def buildNodes (M : ExactModel S) (event : CounterfactualEvent S)
    (roots : SourceRootsConstruction.All M) : Nodes M event roots :=
  TerminalListConstruction.build
    (EncodingSignature M event).isolatedNodeFamily roots.target
    (List.finRange (EncodingSignature M event).count)

theorem buildNodes_noActiveIntervention
    (M : ExactModel S) (event : CounterfactualEvent S)
    (roots : SourceRootsConstruction.All M)
    (empty : AtomicIntervention.NoActiveIntervention roots.target) :
    AtomicIntervention.NoActiveIntervention (buildNodes M event roots).target :=
  TerminalListConstruction.build_noActiveIntervention
    (EncodingSignature M event).isolatedNodeFamily roots.target empty
    (List.finRange (EncodingSignature M event).count)

def node (nodes : Nodes M event roots)
    (index : Fin (EncodingSignature M event).count) :
    Fin nodes.signature.count :=
  nodes.itemNode (finRangePosition index)

theorem node_val (nodes : Nodes M event roots)
    (index : Fin (EncodingSignature M event).count) :
    (node nodes index).val = index.val := by
  rw [node, nodes.itemNode_val]
  simp [EmptyCausalMode.signature, finRangePosition]

theorem nodeValue_eq (nodes : Nodes M event roots)
    (index : Fin (EncodingSignature M event).count) :
    nodes.signature.Value (node nodes index) =
      (EncodingSignature M event).Value index := by
  exact Eq.trans
    (nodes.itemValue_eq (finRangePosition index))
    (congrArg (EncodingSignature M event).Value
      (finRange_get_position index))

/-! ## Reinstating the reference multiworld graph -/

/--
The directed edge test before interventions are compiled.  It retains a source
edge only when both encoded coordinates belong to the same world, which is why
the resulting graph has no directed cross-world edges.
-/
def untreatedDirected (M : ExactModel S) (event : CounterfactualEvent S)
    (parent child : Fin (EncodingSignature M event).count) : Bool :=
  if _same :
      (OccurrenceMultiworld.Encoding.decode parent).world =
        (OccurrenceMultiworld.Encoding.decode child).world then
    S.directed
      (OccurrenceMultiworld.Encoding.decode parent).node
      (OccurrenceMultiworld.Encoding.decode child).node
  else false

theorem untreatedDirected_earlier
    {S : ObservedSignature} {M : ExactModel S}
    {event : CounterfactualEvent S}
    {parent child : Fin (EncodingSignature M event).count}
    (edge : untreatedDirected M event parent child = true) :
    parent.val < child.val := by
  unfold untreatedDirected at edge
  split at edge
  · rename_i sameWorld
    have rankEarlier :
        (OccurrenceMultiworld.Encoding.decode parent).node.val <
          (OccurrenceMultiworld.Encoding.decode child).node.val :=
      S.directed_earlier edge
    have sameIndex :
        (OccurrenceMultiworld.Encoding.decode parent).world.index.val =
          (OccurrenceMultiworld.Encoding.decode child).world.index.val :=
      congrArg
        (fun world : OccurrenceWorld S event => world.index.val) sameWorld
    have parentEncoded := congrArg Fin.val
      (OccurrenceMultiworld.Encoding.encode_decode parent)
    have childEncoded := congrArg Fin.val
      (OccurrenceMultiworld.Encoding.encode_decode child)
    change
      (OccurrenceMultiworld.Encoding.decode parent).world.index.val * S.count +
          (OccurrenceMultiworld.Encoding.decode parent).node.val =
        parent.val at parentEncoded
    change
      (OccurrenceMultiworld.Encoding.decode child).world.index.val * S.count +
          (OccurrenceMultiworld.Encoding.decode child).node.val =
        child.val at childEncoded
    rw [sameIndex] at parentEncoded
    omega
  · simp at edge

def directedEdge (nodes : Nodes M event roots)
    (parent child : Fin (EncodingSignature M event).count)
    (edge : untreatedDirected M event parent child = true) :
    DirectedEdge nodes.signature where
  parent := node nodes parent
  child := node nodes child
  earlier := by
    rw [node_val, node_val]
    exact untreatedDirected_earlier edge

/-- Enumerate the within-world source directed edges that must be installed. -/
def directedEdges (nodes : Nodes M event roots) :
    List (DirectedEdge nodes.signature) :=
  (List.finRange (EncodingSignature M event).count).flatMap fun child =>
    (List.finRange (EncodingSignature M event).count).filterMap fun parent =>
      if edge :
          untreatedDirected M event parent child = true then
        some (directedEdge nodes parent child edge)
      else none

theorem directedEdge_mem (nodes : Nodes M event roots)
    (parent child : Fin (EncodingSignature M event).count)
    (edge : untreatedDirected M event parent child = true) :
    directedEdge nodes parent child edge ∈ directedEdges nodes := by
  simp only [directedEdges, List.mem_flatMap]
  refine ⟨child, List.mem_finRange child, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨parent, List.mem_finRange parent, ?_⟩
  simp [edge]

def rootBeforeLatent
    (roots : SourceRootsConstruction.All M)
    (nodes : Nodes M event roots)
    (directed : DirectedLinksConstruction nodes.target
      (directedEdges nodes))
    (root : Fin M.latent.count) :
    Fin directed.target.record.model.latent.count :=
  directed.roots.rootEquiv.toFun
    (nodes.roots.rootEquiv.toFun (roots.sourceRoot root))

def latentEdge
    (roots : SourceRootsConstruction.All M)
    (nodes : Nodes M event roots)
    (directed : DirectedLinksConstruction nodes.target
      (directedEdges nodes))
    (root : Fin M.latent.count)
    (child : Fin (EncodingSignature M event).count) :
    LatentEdge directed.target where
  source := rootBeforeLatent roots nodes directed root
  child := directed.node (node nodes child)

/--
Enumerate source-root incidences for every occurrence node.  Roots are shared
between worlds; only their target incidence is duplicated.
-/
def latentEdges
    (roots : SourceRootsConstruction.All M)
    (nodes : Nodes M event roots)
    (directed : DirectedLinksConstruction nodes.target
      (directedEdges nodes)) :
    List (LatentEdge directed.target) :=
  (List.finRange M.latent.count).flatMap fun root =>
    (List.finRange (EncodingSignature M event).count).filterMap fun child =>
      if _incident :
          M.latent.incident root
            (OccurrenceMultiworld.Encoding.decode child).node = true then
        some (latentEdge roots nodes directed root child)
      else none

theorem latentEdge_mem
    (roots : SourceRootsConstruction.All M)
    (nodes : Nodes M event roots)
    (directed : DirectedLinksConstruction nodes.target
      (directedEdges nodes))
    (root : Fin M.latent.count)
    (child : Fin (EncodingSignature M event).count)
    (incident :
      M.latent.incident root
        (OccurrenceMultiworld.Encoding.decode child).node = true) :
    latentEdge roots nodes directed root child ∈
      latentEdges roots nodes directed := by
  simp only [latentEdges, List.mem_flatMap]
  refine ⟨root, List.mem_finRange root, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨child, List.mem_finRange child, ?_⟩
  simp [incident]

/--
Every occurrence coordinate and every source root is created from the empty
mode before its causal links are installed by genuine `relate` transitions.
The four fields correspond to the four construction phases and retain their
individual paths and coordinate witnesses for later composition.
-/
structure Linked (M : ExactModel S) (event : CounterfactualEvent S) where
  roots : SourceRootsConstruction.All M
  nodes : Nodes M event roots
  directed : DirectedLinksConstruction nodes.target (directedEdges nodes)
  latent : LatentLinksConstruction directed.target
    (latentEdges roots nodes directed)

def Linked.build (M : ExactModel S) (event : CounterfactualEvent S) :
    Linked M event :=
  let roots := SourceRootsConstruction.all M
  let nodes := buildNodes M event roots
  let directed := DirectedLinksConstruction.build nodes.target
    (directedEdges nodes)
  let latent := LatentLinksConstruction.build directed.target
    (latentEdges roots nodes directed)
  ⟨roots, nodes, directed, latent⟩

namespace Linked

/-! ## Assembling and transporting the linked endpoint -/

/-!
This namespace packages the four phase results as one causal-edit path.  The
next group of lemmas proves that the endpoint's coordinate and root maps have
the same finite shape and value types as the reference encoding.  These facts
are prerequisites for copying mechanisms and beliefs without unsafe casts.
-/

abbrev signature (linked : Linked M event) : ObservedSignature :=
  linked.directed.signature

abbrev target (linked : Linked M event) : CausalMode linked.signature :=
  linked.latent.target

/--
The canonical from-empty builder preserves intervention emptiness through root
and node creation and every causal-link installation.
-/
theorem build_noActiveIntervention (M : ExactModel S)
    (event : CounterfactualEvent S) :
    AtomicIntervention.NoActiveIntervention (Linked.build M event).target := by
  let roots := SourceRootsConstruction.all M
  let nodes := buildNodes M event roots
  let directed := DirectedLinksConstruction.build nodes.target
    (directedEdges nodes)
  have rootsEmpty : AtomicIntervention.NoActiveIntervention roots.target :=
    SourceRootsConstruction.all_noActiveIntervention M
  have nodesEmpty : AtomicIntervention.NoActiveIntervention nodes.target :=
    buildNodes_noActiveIntervention M event roots rootsEmpty
  have directedEmpty :
      AtomicIntervention.NoActiveIntervention directed.target :=
    DirectedLinksConstruction.build_noActiveIntervention nodes.target
      nodesEmpty (directedEdges nodes)
  exact LatentLinksConstruction.build_noActiveIntervention directed.target
    directedEmpty (latentEdges roots nodes directed)

/-- Concatenate root creation, node creation, directed linking, and latent linking. -/
def path (linked : Linked M event) :
    CausalEditPath EmptyCausalMode.mode linked.target :=
  linked.roots.path.append
    (linked.nodes.path.append
      (linked.directed.path.append linked.latent.path))

def encodedNode (linked : Linked M event)
    (index : Fin (EncodingSignature M event).count) :
    Fin linked.signature.count :=
  linked.directed.node (node linked.nodes index)

def sourceRoot (linked : Linked M event) (root : Fin M.latent.count) :
    Fin linked.target.record.model.latent.count :=
  linked.latent.roots.rootEquiv.toFun
    (linked.directed.roots.rootEquiv.toFun
      (linked.nodes.roots.rootEquiv.toFun
        (linked.roots.sourceRoot root)))

theorem count_eq (linked : Linked M event) :
    linked.signature.count = (EncodingSignature M event).count := by
  rw [linked.directed.count_eq, linked.nodes.count_eq]
  simp [EmptyCausalMode.signature]

theorem encodedNode_val (linked : Linked M event)
    (index : Fin (EncodingSignature M event).count) :
    (linked.encodedNode index).val = index.val := by
  unfold encodedNode
  rw [linked.directed.node_val, node_val]

theorem encodedNodeValue_eq (linked : Linked M event)
    (index : Fin (EncodingSignature M event).count) :
    linked.signature.Value (linked.encodedNode index) =
      (EncodingSignature M event).Value index :=
  Eq.trans
    (linked.directed.value_eq (node linked.nodes index))
    (nodeValue_eq linked.nodes index)

theorem sourceRootValue_eq (linked : Linked M event)
    (root : Fin M.latent.count) :
    linked.target.record.model.latent.Value (linked.sourceRoot root) =
      M.latent.Value root := by
  exact Eq.trans
    (linked.latent.roots.value_eq
      (linked.directed.roots.rootEquiv.toFun
        (linked.nodes.roots.rootEquiv.toFun
          (linked.roots.sourceRoot root)))).symm
    (Eq.trans
      (linked.directed.roots.value_eq
        (linked.nodes.roots.rootEquiv.toFun
          (linked.roots.sourceRoot root))).symm
      (Eq.trans
        (linked.nodes.roots.value_eq
          (linked.roots.sourceRoot root)).symm
        (linked.roots.sourceRootValue_eq root)))

theorem directedInstalled (linked : Linked M event)
    (parent child : Fin (EncodingSignature M event).count)
    (edge : untreatedDirected M event parent child = true) :
    linked.signature.directed
        (linked.encodedNode parent) (linked.encodedNode child) = true :=
  linked.directed.installs
    (directedEdge linked.nodes parent child edge)
    (directedEdge_mem linked.nodes parent child edge)

theorem incident (linked : Linked M event)
    (root : Fin M.latent.count)
    (child : Fin (EncodingSignature M event).count)
    (incident :
      M.latent.incident root
        (OccurrenceMultiworld.Encoding.decode child).node = true) :
    linked.target.record.model.latent.incident
        (linked.sourceRoot root) (linked.encodedNode child) = true :=
  linked.latent.installs
    (latentEdge linked.roots linked.nodes linked.directed root child)
    (latentEdge_mem linked.roots linked.nodes linked.directed
      root child incident)

/--
The bijection from encoded reference coordinates to the endpoint coordinates.
It follows from equality of finite counts.  `coordinates` below pairs this
index equivalence with the separately proved value-type equality needed for
transport.
-/
def nodeEquiv (linked : Linked M event) :
    AtomicIntervention.NodeEquiv (EncodingSignature M event)
      linked.signature where
  toFun := linked.encodedNode
  invFun := fun node => Fin.cast linked.count_eq node
  left_inv := by
    intro node
    apply Fin.ext
    exact linked.encodedNode_val node
  right_inv := by
    intro node
    apply Fin.ext
    rw [linked.encodedNode_val]
    rfl

def coordinates (linked : Linked M event) :
    AtomicIntervention.SameCoordinates (EncodingSignature M event)
      linked.signature where
  nodeEquiv := linked.nodeEquiv
  value_eq := fun node => (linked.encodedNodeValue_eq node).symm

def sourceRootEquiv (linked : Linked M event) :
    AtomicIntervention.FinIndexEquiv M.latent.count
      linked.target.record.model.latent.count :=
  (linked.roots.sourceRootEquiv.trans linked.nodes.roots.rootEquiv).trans
    (linked.directed.roots.rootEquiv.trans linked.latent.roots.rootEquiv)

theorem sourceRootEquiv_toFun (linked : Linked M event)
    (root : Fin M.latent.count) :
    linked.sourceRootEquiv.toFun root = linked.sourceRoot root :=
  rfl

variable {S : ObservedSignature} {mode : CausalMode S}
  {event : CounterfactualEvent S}

def sameRoots (linked : Linked mode.record.model event) :
    AtomicIntervention.SameRoots (counterfactualBaseMode mode)
      linked.target where
  rootEquiv := linked.sourceRootEquiv
  value_eq := fun root => (linked.sourceRootValue_eq root).symm

/-! ## Installing copied equations and reindexing belief -/

/-!
At this point the directed edges and latent incidences required by the
occurrence construction have been installed, while its creation-time equations
are placeholders.  A `Fiber` decodes each endpoint coordinate back to its
world/node occurrence so `representedMechanism` can install the corresponding
source equation.  The source belief is then transported along the accumulated
root equivalence.
-/

/-- Transport one source latent assignment to the roots created by this route. -/
def rootAssignment (linked : Linked mode.record.model event)
    (assignment : mode.record.model.latent.Assignment) :
    linked.target.record.model.latent.Assignment :=
  (linked.sameRoots (mode := mode)).transportAssignment assignment

theorem rootAssignment_at (linked : Linked mode.record.model event)
    (assignment : mode.record.model.latent.Assignment)
    (root : Fin mode.record.model.latent.count) :
    cast (linked.sourceRootValue_eq root)
        (linked.rootAssignment assignment (linked.sourceRoot root)) =
      assignment root := by
  have rootEq := linked.sourceRootEquiv_toFun root
  have transported :=
    AtomicIntervention.SameRoots.transportAssignment_toFun
      (linked.sameRoots (mode := mode)) assignment root
  apply eq_of_heq
  exact HEq.trans (cast_heq _ _)
    (HEq.trans
      (dependentApplyHEq (linked.rootAssignment assignment) rootEq.symm)
      (HEq.trans (cast_heq _ _).symm (heq_of_eq transported)))

def worldNode (linked : Linked M event)
    (world : OccurrenceWorld S event) (node : Fin S.count) :
    Fin linked.signature.count :=
  linked.encodedNode
    (OccurrenceMultiworld.Encoding.encode
      (⟨world, node⟩ : OccurrenceNode S event))

theorem worldNodeValue_eq (linked : Linked M event)
    (world : OccurrenceWorld S event) (node : Fin S.count) :
    linked.signature.Value (linked.worldNode world node) =
      S.Value node := by
  exact Eq.trans
    (linked.encodedNodeValue_eq
      (OccurrenceMultiworld.Encoding.encode
        (⟨world, node⟩ : OccurrenceNode S event)))
    (by
      change
        (OccurrenceMultiworld.Encoding.decode
          (OccurrenceMultiworld.Encoding.encode
            (⟨world, node⟩ : OccurrenceNode S event))).Value =
          S.Value node
      rw [OccurrenceMultiworld.Encoding.decode_encode]
      rfl)

theorem worldNode_directed (linked : Linked M event)
    (world : OccurrenceWorld S event) (parent child : Fin S.count)
    (edge : S.directed parent child = true) :
    linked.signature.directed
        (linked.worldNode world parent)
        (linked.worldNode world child) = true := by
  apply linked.directedInstalled
  simp [untreatedDirected, OccurrenceMultiworld.Encoding.decode_encode, edge]

theorem worldNode_incident (linked : Linked M event)
    (world : OccurrenceWorld S event)
    (root : Fin M.latent.count) (child : Fin S.count)
    (incident : M.latent.incident root child = true) :
    linked.target.record.model.latent.incident
        (linked.sourceRoot root) (linked.worldNode world child) = true := by
  apply linked.incident
  simpa using incident

/--
A decoded occurrence coordinate represented by one actual endpoint node.  The
`represented` equality is the local dependent-type bridge used to ask the
endpoint for values at that coordinate.
-/
structure Fiber (linked : Linked M event)
    (child : Fin linked.signature.count) where
  occurrence : OccurrenceNode S event
  represented :
    linked.worldNode occurrence.world occurrence.node = child

def decodedFiber (linked : Linked M event)
    (child : Fin linked.signature.count) : Fiber linked child where
  occurrence :=
    OccurrenceMultiworld.Encoding.decode
      (linked.coordinates.nodeEquiv.invFun child)
  represented := by
    unfold worldNode
    rw [OccurrenceMultiworld.Encoding.encode_decode]
    exact linked.coordinates.nodeEquiv.right_inv child

def worldFiber (linked : Linked M event)
    (world : OccurrenceWorld S event) (node : Fin S.count) :
    Fiber linked (linked.worldNode world node) where
  occurrence := ⟨world, node⟩
  represented := rfl

theorem decodedFiber_eq_worldFiber (linked : Linked M event)
    (world : OccurrenceWorld S event) (node : Fin S.count) :
    linked.decodedFiber (linked.worldNode world node) =
      linked.worldFiber world node := by
  have inverse :
      linked.coordinates.nodeEquiv.invFun (linked.worldNode world node) =
        OccurrenceMultiworld.Encoding.encode
          (⟨world, node⟩ : OccurrenceNode S event) := by
    unfold worldNode
    exact linked.coordinates.nodeEquiv.left_inv _
  have occurrenceEq :
      (linked.decodedFiber
        (linked.worldNode world node)).occurrence =
      (linked.worldFiber world node).occurrence :=
    (congrArg OccurrenceMultiworld.Encoding.decode inverse).trans
      (OccurrenceMultiworld.Encoding.decode_encode _)
  cases decoded : linked.decodedFiber (linked.worldNode world node) with
  | mk decodedOccurrence decodedRepresented =>
      cases expected : linked.worldFiber world node with
      | mk expectedOccurrence expectedRepresented =>
          simp only [decoded, expected] at occurrenceEq
          subst expectedOccurrence
          have representedEq :
              decodedRepresented = expectedRepresented :=
            Subsingleton.elim _ _
          cases representedEq
          rfl

/--
Read the original source mechanism through a decoded fiber.  Parent and latent
inputs are transported back along the coordinate and root maps, respectively.
-/
def representedMechanism (linked : Linked M event)
    {child : Fin linked.signature.count}
    (fiber : Fiber linked child)
    (parents : linked.signature.ParentValues child)
    (latents : linked.target.record.model.latent.Inputs child) :
    S.Value fiber.occurrence.node :=
  M.mechanism fiber.occurrence.node
    (fun parent edge =>
      cast (linked.worldNodeValue_eq fiber.occurrence.world parent)
        (parents (linked.worldNode fiber.occurrence.world parent)
          (by
            have representedEdge :=
              linked.worldNode_directed fiber.occurrence.world parent
                fiber.occurrence.node edge
            rw [fiber.represented] at representedEdge
            exact representedEdge)))
    (fun root incident =>
      cast (linked.sourceRootValue_eq root)
        (latents (linked.sourceRoot root)
          (by
            have representedIncident :=
              linked.worldNode_incident fiber.occurrence.world root
                fiber.occurrence.node incident
            rw [fiber.represented] at representedIncident
            exact representedIncident)))

def fiberMechanism (linked : Linked M event)
    (child : Fin linked.signature.count)
    (parents : linked.signature.ParentValues child)
    (latents : linked.target.record.model.latent.Inputs child)
    (fiber : Fiber linked child) :
    linked.signature.Value child :=
  cast
    (Eq.trans
      (linked.worldNodeValue_eq fiber.occurrence.world
        fiber.occurrence.node).symm
      (congrArg linked.signature.Value fiber.represented))
    (linked.representedMechanism fiber parents latents)

def sourceMechanism (linked : Linked M event)
    (child : Fin linked.signature.count)
    (parents : linked.signature.ParentValues child)
    (latents : linked.target.record.model.latent.Inputs child) :
    linked.signature.Value child :=
  linked.fiberMechanism child parents latents (linked.decodedFiber child)

/-- Replace all placeholder mechanisms by their decoded source mechanisms. -/
def configureOperation (linked : Linked M event) :
    StructuralMechanismReplacement.Operation linked.target.record where
  replacement := linked.sourceMechanism

def configuredModel (linked : Linked M event) : ExactModel linked.signature :=
  linked.configureOperation.apply.model

def configureRecord (linked : Linked mode.record.model event) :
    CausalEpistemicRecord linked.signature :=
  linked.configureOperation.apply

def configureTransition (linked : Linked mode.record.model event) :
    CausalEditTransition linked.signature linked.signature where
  source := linked.target
  target := ⟨"configure-empty-occurrence-equations", linked.configureRecord⟩
  operation := .replacingMechanisms linked.configureOperation
  realized := rfl

/--
Reindex the source prior onto the newly created roots.  The reference evaluator
is supplied explicitly so the operation carries its semantic provenance.
-/
def reindexBeliefOperation (linked : Linked mode.record.model event) :
    BeliefReindexing.CertifiedOperation
      linked.configureTransition.target.record where
  OriginSignature := S
  origin := .prior mode.record.model
  assignment := linked.rootAssignment
  reference := fun assignment =>
    linked.configureTransition.target.record.model.evalUnder
      linked.configureTransition.target.record.intervention.value
      (linked.rootAssignment assignment)
  interventionPolicy := .preserve (fun _ => rfl)

def reindexBeliefRecord (linked : Linked mode.record.model event) :
    CausalEpistemicRecord linked.signature :=
  linked.reindexBeliefOperation.apply

/--
The from-empty route reconstructs the source SCM prior on its newly created
root coordinates before atomic world actions are compiled.
-/
@[simp] theorem reindexBelief_prior_provenance
    (linked : Linked mode.record.model event) :
    linked.reindexBeliefRecord.belief =
      mode.record.model.prior.map linked.rootAssignment :=
  rfl

def reindexBeliefTransition (linked : Linked mode.record.model event) :
    CausalEditTransition linked.signature linked.signature where
  source := linked.configureTransition.target
  target := ⟨"reindex-empty-occurrence-belief", linked.reindexBeliefRecord⟩
  operation := .reindexingBelief linked.reindexBeliefOperation
  realized := rfl

theorem configured_mechanism_worldNode
    (linked : Linked M event)
    (world : OccurrenceWorld S event) (child : Fin S.count)
    (parents : linked.signature.ParentValues (linked.worldNode world child))
    (latents : linked.target.record.model.latent.Inputs
      (linked.worldNode world child)) :
    cast (linked.worldNodeValue_eq world child)
        (linked.configuredModel.mechanism
          (linked.worldNode world child) parents latents) =
      M.mechanism child
        (fun parent edge =>
          cast (linked.worldNodeValue_eq world parent)
            (parents (linked.worldNode world parent)
              (linked.worldNode_directed world parent child edge)))
        (fun root incident =>
          cast (linked.sourceRootValue_eq root)
            (latents (linked.sourceRoot root)
              (linked.worldNode_incident world root child incident))) := by
  change cast (linked.worldNodeValue_eq world child)
      (linked.fiberMechanism (linked.worldNode world child)
        parents latents
        (linked.decodedFiber (linked.worldNode world child))) = _
  have fiberEq := linked.decodedFiber_eq_worldFiber world child
  rw [congrArg
    (linked.fiberMechanism (linked.worldNode world child) parents latents)
    fiberEq]
  simp [fiberMechanism, worldFiber, representedMechanism]

def fiberAction (linked : Linked M event)
    (child : Fin linked.signature.count)
    (fiber : Fiber linked child) :
    Option (linked.signature.Value child) :=
  match fiber.occurrence.world.action fiber.occurrence.node with
  | none => none
  | some value =>
      some (cast
        (Eq.trans
          (linked.worldNodeValue_eq fiber.occurrence.world
            fiber.occurrence.node).symm
          (congrArg linked.signature.Value fiber.represented))
        value)

def combinedAction (linked : Linked M event) :
    AtomicIntervention.Action linked.signature :=
  fun child => linked.fiberAction child (linked.decodedFiber child)

theorem combinedAction_worldNode_none (linked : Linked M event)
    (world : OccurrenceWorld S event) (node : Fin S.count)
    (selected : world.action node = none) :
    linked.combinedAction (linked.worldNode world node) = none := by
  unfold combinedAction
  have fiberEq := linked.decodedFiber_eq_worldFiber world node
  rw [congrArg
    (linked.fiberAction (linked.worldNode world node)) fiberEq]
  simp [fiberAction, worldFiber, selected]

theorem combinedAction_worldNode_some (linked : Linked M event)
    (world : OccurrenceWorld S event) (node : Fin S.count)
    (value : S.Value node) (selected : world.action node = some value) :
    linked.combinedAction (linked.worldNode world node) =
      some (cast (linked.worldNodeValue_eq world node).symm value) := by
  unfold combinedAction
  have fiberEq := linked.decodedFiber_eq_worldFiber world node
  rw [congrArg
    (linked.fiberAction (linked.worldNode world node)) fiberEq]
  simp [fiberAction, worldFiber, selected]

/-! ## Semantic comparison with the reference multiworld -/

/--
At one world/node coordinate, the configured endpoint evaluator equals the
source evaluator under that world's action.  The induction follows source
topological order; selected nodes use `combinedAction`, while unselected nodes
reuse the transported parent and root inputs.
-/
theorem configured_evalUnder_worldNode
    (linked : Linked mode.record.model event)
    (assignment : mode.record.model.latent.Assignment)
    (world : OccurrenceWorld S event) (child : Fin S.count) :
    cast (linked.worldNodeValue_eq world child)
        (linked.configuredModel.evalUnder linked.combinedAction
          (linked.rootAssignment assignment)
          (linked.worldNode world child)) =
      mode.record.model.evalUnder world.action assignment child := by
  change cast (linked.worldNodeValue_eq world child)
      (linked.configuredModel.evalNodeUnder linked.combinedAction
        (linked.rootAssignment assignment)
        (linked.worldNode world child)) =
    mode.record.model.evalNodeUnder world.action assignment child
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : world.action child with
  | some value =>
      rw [linked.combinedAction_worldNode_some world child value selected]
      simp
  | none =>
      rw [linked.combinedAction_worldNode_none world child selected]
      rw [linked.configured_mechanism_worldNode world child]
      congr 1
      · funext parent edge
        exact linked.configured_evalUnder_worldNode
          assignment world parent
      · funext root incident
        exact linked.rootAssignment_at assignment root
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/--
Assemble the coordinatewise comparison into equality with the encoded
reference multiworld assignment.  This is the endpoint-level result consumed
by the from-empty execution route.
-/
theorem configured_evalUnder_eq_reference
    (linked : Linked mode.record.model event)
    (assignment : mode.record.model.latent.Assignment) :
    linked.configuredModel.evalUnder linked.combinedAction
        (linked.rootAssignment assignment) =
      linked.coordinates.transportObserved
        (OccurrenceMultiworld.Encoding.encodeAssignment
          (World mode.record.model event)
          ((World mode.record.model event).eval assignment)) := by
  let actual :=
    linked.configuredModel.evalUnder linked.combinedAction
      (linked.rootAssignment assignment)
  let reference :=
    OccurrenceMultiworld.Encoding.encodeAssignment
      (World mode.record.model event)
      ((World mode.record.model event).eval assignment)
  have back :
      linked.coordinates.untransportObserved actual = reference := by
    funext index
    let occurrence :=
      OccurrenceMultiworld.Encoding.decode index
    have evaluated :=
      linked.configured_evalUnder_worldNode assignment
        occurrence.world occurrence.node
    change cast (linked.coordinates.value_eq index).symm
        (actual (linked.coordinates.nodeEquiv.toFun index)) =
      reference index
    change cast (linked.coordinates.value_eq index).symm
        (actual (linked.encodedNode index)) =
      (World mode.record.model event).eval assignment occurrence
    have encoded :
        linked.encodedNode index =
          linked.worldNode occurrence.world occurrence.node := by
      unfold worldNode
      rw [OccurrenceMultiworld.Encoding.encode_decode]
    apply eq_of_heq
    exact HEq.trans (cast_heq _ _)
      (HEq.trans
        (dependentApplyHEq actual encoded)
        (HEq.trans (cast_heq _ _).symm (heq_of_eq evaluated)))
  calc
    actual =
        linked.coordinates.transportObserved
          (linked.coordinates.untransportObserved actual) :=
      (AtomicIntervention.SameCoordinates.transportObserved_untransportObserved
        linked.coordinates actual).symm
    _ = linked.coordinates.transportObserved reference :=
      congrArg linked.coordinates.transportObserved back

end Linked

end EmptyOccurrenceConstruction

end Causality
end Thesis
