import Thesis.Causality.ExecutedMultiworld.Creation

namespace Thesis
namespace Causality

open Probability

/-!
Executable directed and latent linking with occurrence-coordinate equivalences.

The preceding creation phase produces isolated observed-node copies and any
needed latent roots.  This file installs the missing graph edges through real
`relate` transitions.  Its reading order is: generic recursive installers for
directed and latent edge lists; enumeration of the links required by every
occurrence copy; composition of those installers; then coordinate and root
equivalences with the semantic occurrence-multiworld encoding.  The last
equivalences are what let later code compare an executable endpoint with the
reference multiworld model without identifying their dependent signatures.
-/

/-! ## Generic executable linking -/

/-!
Both builders below carry more than a target mode.  Their `roots`, `node`,
`preserves`, and `installs` fields are induction invariants: each recursive
`relate` step may change a dependent signature, so later steps need explicit
maps back to the original coordinates.
-/

/-- A rank-respecting directed edge to be installed by a real `relate` edit. -/
structure DirectedEdge (S : ObservedSignature) where
  parent : Fin S.count
  child : Fin S.count
  earlier : parent.val < child.val

namespace DirectedEdge

def afterAdd (edge : DirectedEdge S) (added : DirectedEdge S) :
    DirectedEdge
      (DirectedLink.addSignature S added.parent added.child added.earlier) :=
  ⟨edge.parent, edge.child, edge.earlier⟩

end DirectedEdge

/-- The endpoint of installing a finite list of directed links one at a time. -/
structure DirectedLinksConstruction {S : ObservedSignature}
    (source : CausalMode S) (edges : List (DirectedEdge S)) where
  signature : ObservedSignature
  target : CausalMode signature
  path : CausalEditPath source target
  roots : AtomicIntervention.SameRoots source target
  count_eq : signature.count = S.count
  node : Fin S.count -> Fin signature.count
  node_val : forall sourceNode, (node sourceNode).val = sourceNode.val
  value_eq : forall sourceNode,
    signature.Value (node sourceNode) = S.Value sourceNode
  preserves : forall parent child,
    S.directed parent child = true ->
      signature.directed (node parent) (node child) = true
  installs : forall edge, edge ∈ edges ->
    signature.directed (node edge.parent) (node edge.child) = true
  latentPreserves : forall sourceRoot child,
    source.record.model.latent.incident sourceRoot child = true ->
      target.record.model.latent.incident
        (roots.rootEquiv.toFun sourceRoot) (node child) = true

namespace DirectedLinksConstruction

/-- Turn one edge specification into the primitive directed-link operation. -/
def operation (_mode : CausalMode S) (edge : DirectedEdge S) :
    DirectedLink.RelateOperation S edge.parent edge.child edge.earlier where
  replacement := fun _ _ _ => S.defaultValue edge.child

/--
Install the list from left to right.  In the recursive branch, `afterAdd`
reinterprets each remaining edge in the just-extended signature; the resulting
invariants compose the one-step preservation facts with the tail's facts.
-/
def build {S : ObservedSignature} (source : CausalMode S) :
    (edges : List (DirectedEdge S)) -> DirectedLinksConstruction source edges
  | [] =>
      { signature := S
        target := source
        path := .nil source
        roots := AtomicIntervention.SameRoots.refl source
        count_eq := rfl
        node := fun sourceNode => sourceNode
        node_val := fun _ => rfl
        value_eq := fun _ => rfl
        preserves := fun _ _ edge => edge
        installs := fun _ absent => by simp at absent
        latentPreserves := fun _ _ incident => incident }
  | edge :: rest =>
      let step := (operation source edge).transition source "relate-directed"
      let tail := build step.target (rest.map (fun later => later.afterAdd edge))
      let stepRoots : AtomicIntervention.SameRoots source step.target :=
        { rootEquiv :=
            AtomicIntervention.FinIndexEquiv.refl
              source.record.model.latent.count
          value_eq := fun _ => rfl }
      { signature := tail.signature
        target := tail.target
        path := (CausalEditPath.single step).append tail.path
        roots := stepRoots.trans tail.roots
        count_eq := tail.count_eq
        node := fun sourceNode => tail.node sourceNode
        node_val := tail.node_val
        value_eq := tail.value_eq
        preserves := fun parent child oldEdge =>
          tail.preserves parent child
            (DirectedLink.oldEdge S edge.parent edge.child edge.earlier oldEdge)
        installs := fun requested present => by
          simp only [List.mem_cons] at present
          rcases present with same | later
          · subst requested
            exact tail.preserves edge.parent edge.child
              (DirectedLink.addedEdge S edge.parent edge.child edge.earlier)
          · exact tail.installs (requested.afterAdd edge)
              (List.mem_map_of_mem later)
        latentPreserves := fun sourceRoot child incident => by
          simpa [stepRoots, AtomicIntervention.SameRoots.trans,
            AtomicIntervention.FinIndexEquiv.trans] using
            tail.latentPreserves sourceRoot child incident }
termination_by edges => edges.length
decreasing_by simp

/-- Canonical directed-link installation preserves intervention emptiness. -/
theorem build_noActiveIntervention {S : ObservedSignature}
    (source : CausalMode S)
    (empty : AtomicIntervention.NoActiveIntervention source) :
    (edges : List (DirectedEdge S)) ->
      AtomicIntervention.NoActiveIntervention (build source edges).target
  | [] => by
      rw [build]
      exact empty
  | edge :: rest => by
      let step := (operation source edge).transition source "relate-directed"
      have stepEmpty : AtomicIntervention.NoActiveIntervention step.target :=
        AtomicIntervention.directedRelating_noActiveIntervention source
          edge.parent edge.child edge.earlier (operation source edge)
          "relate-directed" empty
      rw [build]
      dsimp only
      exact build_noActiveIntervention step.target stepEmpty
        (rest.map (fun later => later.afterAdd edge))
termination_by edges => edges.length
decreasing_by simp

end DirectedLinksConstruction

/-- One exogenous-to-endogenous link to be installed by a real `relate` edit. -/
structure LatentEdge {S : ObservedSignature} (mode : CausalMode S) where
  source : Fin mode.record.model.latent.count
  child : Fin S.count

/-- The endpoint of installing a finite list of latent-input links. -/
structure LatentLinksConstruction {S : ObservedSignature}
    (source : CausalMode S) (edges : List (LatentEdge source)) where
  target : CausalMode S
  path : CausalEditPath source target
  roots : AtomicIntervention.SameRoots source target
  preserves : forall sourceRoot child,
    source.record.model.latent.incident sourceRoot child = true ->
      target.record.model.latent.incident
        (roots.rootEquiv.toFun sourceRoot) child = true
  installs : forall edge, edge ∈ edges ->
    target.record.model.latent.incident
      (roots.rootEquiv.toFun edge.source) edge.child = true

namespace LatentLinksConstruction

/-- Turn one root-to-node specification into the primitive latent-link operation. -/
def operation (mode : CausalMode S) (edge : LatentEdge mode) :
    LatentLink.RelateOperation mode.record edge.source edge.child where
  replacement := fun _ _ => S.defaultValue edge.child

/--
The latent analogue of `DirectedLinksConstruction.build`.  It preserves the
observed signature, but still transports root coordinates after each edit so
the final `installs` theorem has the source-root type expected by clients.
-/
def build {S : ObservedSignature} (source : CausalMode S) :
    (edges : List (LatentEdge source)) -> LatentLinksConstruction source edges
  | [] =>
      { target := source
        path := .nil source
        roots := AtomicIntervention.SameRoots.refl source
        preserves := fun _ _ incident => incident
        installs := fun _ absent => by simp at absent }
  | edge :: rest =>
      let step := (operation source edge).transition source "relate-latent"
      let tail := build step.target (rest.map (fun later => by
        exact {
          source := later.source
          child := later.child
        }))
      let stepRoots : AtomicIntervention.SameRoots source step.target :=
        { rootEquiv :=
            AtomicIntervention.FinIndexEquiv.refl
              source.record.model.latent.count
          value_eq := fun _ => rfl }
      { target := tail.target
        path := (CausalEditPath.single step).append tail.path
        roots := stepRoots.trans tail.roots
        preserves := fun sourceRoot child oldIncident =>
          tail.preserves sourceRoot child
            (LatentLink.oldIncident source.record.model edge.source edge.child
              oldIncident)
        installs := fun requested present => by
          simp only [List.mem_cons] at present
          rcases present with same | later
          · subst requested
            exact tail.preserves edge.source edge.child
              (LatentLink.addedIncident source.record.model edge.source edge.child)
          · exact tail.installs
              { source := requested.source
                child := requested.child }
              (List.mem_map_of_mem later) }
termination_by edges => edges.length
decreasing_by simp

/-- Canonical latent-link installation preserves intervention emptiness. -/
theorem build_noActiveIntervention {S : ObservedSignature}
    (source : CausalMode S)
    (empty : AtomicIntervention.NoActiveIntervention source) :
    (edges : List (LatentEdge source)) ->
      AtomicIntervention.NoActiveIntervention (build source edges).target
  | [] => by
      rw [build]
      exact empty
  | edge :: rest => by
      let step := (operation source edge).transition source "relate-latent"
      have stepEmpty : AtomicIntervention.NoActiveIntervention step.target :=
        AtomicIntervention.latentRelating_noActiveIntervention source
          edge.source edge.child (operation source edge) "relate-latent" empty
      rw [build]
      dsimp only
      exact build_noActiveIntervention step.target stepEmpty
        (rest.map (fun later => by
          exact {
            source := later.source
            child := later.child
          }))
termination_by edges => edges.length
decreasing_by simp

end LatentLinksConstruction

/-! ## Links required by occurrence copies -/

/-!
`OccurrenceCopiesConstruction` has already allocated a factual copy and one
copy per counterfactual atom, but its copies are isolated.  The following two
finite lists enumerate exactly the source directed and latent edges to restore
inside every copied world.  No edges are installed between distinct worlds.
-/

def occurrenceDirectedEdge
    (copies : OccurrenceCopiesConstruction template source atoms)
    (occurrence : Fin atoms.length) (parent child : Fin template.count)
    (edge : template.directed parent child = true) :
    DirectedEdge copies.signature where
  parent := copies.copiedNode occurrence parent
  child := copies.copiedNode occurrence child
  earlier := by
    rw [copies.copiedNode_val, copies.copiedNode_val]
    exact Nat.add_lt_add_left (template.directed_earlier edge) _

/--
Enumerate every directed source edge once for each counterfactual occurrence.
The nested finite ranges are an executable finite traversal; `filterMap`
retains precisely those pairs whose Boolean edge test succeeds.
-/
def occurrenceDirectedEdges
    (copies : OccurrenceCopiesConstruction template source atoms) :
    List (DirectedEdge copies.signature) :=
  (List.finRange atoms.length).flatMap fun occurrence =>
    (List.finRange template.count).flatMap fun child =>
      (List.finRange template.count).filterMap fun parent =>
        if edge : template.directed parent child = true then
          some (occurrenceDirectedEdge copies occurrence parent child edge)
        else none

theorem occurrenceDirectedEdge_mem
    (copies : OccurrenceCopiesConstruction template source atoms)
    (occurrence : Fin atoms.length) (parent child : Fin template.count)
    (edge : template.directed parent child = true) :
    occurrenceDirectedEdge copies occurrence parent child edge ∈
      occurrenceDirectedEdges copies := by
  simp only [occurrenceDirectedEdges, List.mem_flatMap]
  refine ⟨occurrence, List.mem_finRange occurrence, ?_⟩
  refine ⟨child, List.mem_finRange child, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨parent, List.mem_finRange parent, ?_⟩
  simp [edge]

/-- Transport a source root through copy creation and directed-link installation. -/
def copiedRoot
    (copies : OccurrenceCopiesConstruction template source atoms)
    (directed : DirectedLinksConstruction copies.target
      (occurrenceDirectedEdges copies))
    (root : Fin source.record.model.latent.count) :
    Fin directed.target.record.model.latent.count :=
  directed.roots.rootEquiv.toFun (copies.roots.rootEquiv.toFun root)

def copiedRootValue_eq
    (copies : OccurrenceCopiesConstruction template source atoms)
    (directed : DirectedLinksConstruction copies.target
      (occurrenceDirectedEdges copies))
    (root : Fin source.record.model.latent.count) :
    directed.target.record.model.latent.Value
        (copiedRoot copies directed root) =
      source.record.model.latent.Value root := by
  exact Eq.trans
    (directed.roots.value_eq (copies.roots.rootEquiv.toFun root)).symm
    (copies.roots.value_eq root).symm

def occurrenceLatentEdge
    {source : CausalMode template}
    (copies : OccurrenceCopiesConstruction template source atoms)
    (directed : DirectedLinksConstruction copies.target
      (occurrenceDirectedEdges copies))
    (occurrence : Fin atoms.length)
    (root : Fin source.record.model.latent.count)
    (child : Fin template.count) :
    LatentEdge directed.target where
  source := copiedRoot copies directed root
  child := directed.node (copies.copiedNode occurrence child)

/--
Enumerate every latent incidence once for each copied occurrence.  The factual
copy's old incidences are already preserved by creation, so this list covers
only the additional worlds.
-/
def occurrenceLatentEdges
    {source : CausalMode template}
    (copies : OccurrenceCopiesConstruction template source atoms)
    (directed : DirectedLinksConstruction copies.target
      (occurrenceDirectedEdges copies)) :
    List (LatentEdge directed.target) :=
  (List.finRange atoms.length).flatMap fun occurrence =>
    (List.finRange source.record.model.latent.count).flatMap fun root =>
      (List.finRange template.count).filterMap fun child =>
        if _incident :
            source.record.model.latent.incident root child = true then
          some (occurrenceLatentEdge copies directed occurrence root child)
        else none

theorem occurrenceLatentEdge_mem
    {source : CausalMode template}
    (copies : OccurrenceCopiesConstruction template source atoms)
    (directed : DirectedLinksConstruction copies.target
      (occurrenceDirectedEdges copies))
    (occurrence : Fin atoms.length)
    (root : Fin source.record.model.latent.count)
    (child : Fin template.count)
    (incident : source.record.model.latent.incident root child = true) :
    occurrenceLatentEdge copies directed occurrence root child ∈
      occurrenceLatentEdges copies directed := by
  simp only [occurrenceLatentEdges, List.mem_flatMap]
  refine ⟨occurrence, List.mem_finRange occurrence, ?_⟩
  refine ⟨root, List.mem_finRange root, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨child, List.mem_finRange child, ?_⟩
  simp [incident]

/--
Isolated copies followed by actual directed and latent `relate` edits.  The
three fields are intentionally retained separately, so their paths and
coordinate-transport certificates remain available to subsequent proofs.
-/
structure LinkedOccurrenceCopies (template : ObservedSignature)
    (source : CausalMode template)
    (atoms : List (CounterfactualAtom template)) where
  copies : OccurrenceCopiesConstruction template source atoms
  directed : DirectedLinksConstruction copies.target
    (occurrenceDirectedEdges copies)
  latent : LatentLinksConstruction directed.target
    (occurrenceLatentEdges copies directed)

namespace LinkedOccurrenceCopies

/--
Build the executable multiworld in the same order used by the theory:
allocate copies, restore directed edges, then restore latent incidences.
-/
def build (template : ObservedSignature) (source : CausalMode template)
    (atoms : List (CounterfactualAtom template)) :
    LinkedOccurrenceCopies template source atoms :=
  let copies := OccurrenceCopiesConstruction.build template source atoms
  let directed := DirectedLinksConstruction.build copies.target
    (occurrenceDirectedEdges copies)
  let latent := LatentLinksConstruction.build directed.target
    (occurrenceLatentEdges copies directed)
  ⟨copies, directed, latent⟩

/--
The canonical occurrence-world linkage preserves an empty intervention through
copy creation and every directed and latent `relate` edit.
-/
theorem build_noActiveIntervention
    (template : ObservedSignature) (source : CausalMode template)
    (atoms : List (CounterfactualAtom template))
    (empty : AtomicIntervention.NoActiveIntervention source) :
    AtomicIntervention.NoActiveIntervention
      (build template source atoms).latent.target := by
  let copies := OccurrenceCopiesConstruction.build template source atoms
  let directed := DirectedLinksConstruction.build copies.target
    (occurrenceDirectedEdges copies)
  have copiesEmpty : AtomicIntervention.NoActiveIntervention copies.target :=
    OccurrenceCopiesConstruction.build_noActiveIntervention
      template source empty atoms
  have directedEmpty :
      AtomicIntervention.NoActiveIntervention directed.target :=
    DirectedLinksConstruction.build_noActiveIntervention copies.target
      copiesEmpty (occurrenceDirectedEdges copies)
  exact LatentLinksConstruction.build_noActiveIntervention directed.target
    directedEmpty (occurrenceLatentEdges copies directed)

abbrev signature
    (linked : LinkedOccurrenceCopies template source atoms) :
    ObservedSignature :=
  linked.directed.signature

abbrev target
    (linked : LinkedOccurrenceCopies template source atoms) :
    CausalMode linked.signature :=
  linked.latent.target

def path (linked : LinkedOccurrenceCopies template source atoms) :
    CausalEditPath source linked.target :=
  linked.copies.path.append
    (linked.directed.path.append linked.latent.path)

def oldNode (linked : LinkedOccurrenceCopies template source atoms)
    (node : Fin template.count) : Fin linked.signature.count :=
  linked.directed.node (linked.copies.oldNode node)

def copiedNode (linked : LinkedOccurrenceCopies template source atoms)
    (occurrence : Fin atoms.length) (node : Fin template.count) :
    Fin linked.signature.count :=
  linked.directed.node (linked.copies.copiedNode occurrence node)

def root (linked : LinkedOccurrenceCopies template source atoms)
    (sourceRoot : Fin source.record.model.latent.count) :
    Fin linked.target.record.model.latent.count :=
  linked.latent.roots.rootEquiv.toFun
    (linked.directed.roots.rootEquiv.toFun
      (linked.copies.roots.rootEquiv.toFun sourceRoot))

theorem count_eq (linked : LinkedOccurrenceCopies template source atoms) :
    linked.signature.count = (atoms.length + 1) * template.count := by
  rw [linked.directed.count_eq, linked.copies.count_eq]
  simp [Nat.add_mul]
  omega

theorem oldNode_val (linked : LinkedOccurrenceCopies template source atoms)
    (node : Fin template.count) :
    (linked.oldNode node).val = node.val := by
  unfold oldNode
  rw [linked.directed.node_val, linked.copies.oldNode_val]

theorem copiedNode_val
    (linked : LinkedOccurrenceCopies template source atoms)
    (occurrence : Fin atoms.length) (node : Fin template.count) :
    (linked.copiedNode occurrence node).val =
      template.count + occurrence.val * template.count + node.val := by
  unfold copiedNode
  rw [linked.directed.node_val, linked.copies.copiedNode_val]

theorem oldValue_eq
    (linked : LinkedOccurrenceCopies template source atoms)
    (node : Fin template.count) :
    linked.signature.Value (linked.oldNode node) = template.Value node :=
  Eq.trans
    (linked.directed.value_eq (linked.copies.oldNode node))
    (linked.copies.oldValue_eq node)

theorem factual_directed
    (linked : LinkedOccurrenceCopies template source atoms)
    (parent child : Fin template.count)
    (edge : template.directed parent child = true) :
    linked.signature.directed
        (linked.oldNode parent) (linked.oldNode child) = true :=
  linked.directed.preserves
    (linked.copies.oldNode parent) (linked.copies.oldNode child)
    (linked.copies.oldDirected parent child edge)

theorem factual_incident
    (linked : LinkedOccurrenceCopies template source atoms)
    (sourceRoot : Fin source.record.model.latent.count)
    (child : Fin template.count)
    (incident : source.record.model.latent.incident sourceRoot child = true) :
    linked.target.record.model.latent.incident
        (linked.root sourceRoot) (linked.oldNode child) = true := by
  exact linked.latent.preserves
    (linked.directed.roots.rootEquiv.toFun
      (linked.copies.roots.rootEquiv.toFun sourceRoot))
    (linked.directed.node (linked.copies.oldNode child))
    (linked.directed.latentPreserves
      (linked.copies.roots.rootEquiv.toFun sourceRoot)
      (linked.copies.oldNode child)
      (linked.copies.oldIncident sourceRoot child incident))

theorem copied_directed
    (linked : LinkedOccurrenceCopies template source atoms)
    (occurrence : Fin atoms.length) (parent child : Fin template.count)
    (edge : template.directed parent child = true) :
    linked.signature.directed
        (linked.copiedNode occurrence parent)
        (linked.copiedNode occurrence child) = true := by
  exact linked.directed.installs
    (occurrenceDirectedEdge linked.copies occurrence parent child edge)
    (occurrenceDirectedEdge_mem linked.copies occurrence parent child edge)

theorem copied_incident
    (linked : LinkedOccurrenceCopies template source atoms)
    (occurrence : Fin atoms.length)
    (sourceRoot : Fin source.record.model.latent.count)
    (child : Fin template.count)
    (incident : source.record.model.latent.incident sourceRoot child = true) :
    linked.target.record.model.latent.incident
        (linked.root sourceRoot)
        (linked.copiedNode occurrence child) = true := by
  exact linked.latent.installs
    (occurrenceLatentEdge linked.copies linked.directed occurrence
      sourceRoot child)
    (occurrenceLatentEdge_mem linked.copies linked.directed occurrence
      sourceRoot child incident)

theorem copiedValue_eq
    (linked : LinkedOccurrenceCopies template source atoms)
    (occurrence : Fin atoms.length) (node : Fin template.count) :
    linked.signature.Value (linked.copiedNode occurrence node) =
      template.Value node :=
  Eq.trans
    (linked.directed.value_eq (linked.copies.copiedNode occurrence node))
    (linked.copies.copiedValue_eq occurrence node)

theorem rootValue_eq
    (linked : LinkedOccurrenceCopies template source atoms)
    (sourceRoot : Fin source.record.model.latent.count) :
    linked.target.record.model.latent.Value (linked.root sourceRoot) =
      source.record.model.latent.Value sourceRoot := by
  exact Eq.trans
    (linked.latent.roots.value_eq
      (linked.directed.roots.rootEquiv.toFun
        (linked.copies.roots.rootEquiv.toFun sourceRoot))).symm
    (Eq.trans
      (linked.directed.roots.value_eq
        (linked.copies.roots.rootEquiv.toFun sourceRoot)).symm
      (linked.copies.roots.value_eq sourceRoot).symm)

end LinkedOccurrenceCopies

/-! ## Coordinate equivalence with occurrence syntax -/

/-!
The executable construction orders its nodes by creation history, while the
reference semantics uses `OccurrenceMultiworld.Encoding`.  The definitions
below prove that these are two presentations of the same finite coordinates:
factual nodes map to the old copy and counterfactual nodes map to their
corresponding occurrence copy.  They also transport the shared source-root
assignment through the accumulated edits.
-/

def LinkedOccurrenceCopies.worldNode
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count) :
    Fin linked.signature.count :=
  match world with
  | .factual => linked.oldNode node
  | .counterfactual occurrence => linked.copiedNode occurrence node

theorem LinkedOccurrenceCopies.worldNode_val
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count) :
    (linked.worldNode world node).val =
      (OccurrenceMultiworld.Encoding.encode
        (⟨world, node⟩ : OccurrenceNode template event)).val := by
  cases world with
  | factual =>
      simp [worldNode, OccurrenceMultiworld.Encoding.encode,
        OccurrenceWorld.index, linked.oldNode_val]
  | counterfactual occurrence =>
      simp only [worldNode]
      rw [linked.copiedNode_val]
      simp [OccurrenceMultiworld.Encoding.encode,
        OccurrenceWorld.index, Nat.add_mul]
      omega

theorem LinkedOccurrenceCopies.worldNode_value_eq
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count) :
    linked.signature.Value (linked.worldNode world node) =
      template.Value node := by
  cases world with
  | factual => exact linked.oldValue_eq node
  | counterfactual occurrence => exact linked.copiedValue_eq occurrence node

theorem LinkedOccurrenceCopies.worldNode_directed
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event)
    (parent child : Fin template.count)
    (edge : template.directed parent child = true) :
    linked.signature.directed
        (linked.worldNode world parent) (linked.worldNode world child) = true := by
  cases world with
  | factual => exact linked.factual_directed parent child edge
  | counterfactual occurrence =>
      exact linked.copied_directed occurrence parent child edge

theorem LinkedOccurrenceCopies.worldNode_incident
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event)
    (sourceRoot : Fin source.record.model.latent.count)
    (child : Fin template.count)
    (incident : source.record.model.latent.incident sourceRoot child = true) :
    linked.target.record.model.latent.incident
        (linked.root sourceRoot) (linked.worldNode world child) = true := by
  cases world with
  | factual => exact linked.factual_incident sourceRoot child incident
  | counterfactual occurrence =>
      exact linked.copied_incident occurrence sourceRoot child incident

/--
The bijection from semantic occurrence indices to the endpoint's dependent
coordinates.  The inverse is a `Fin.cast` because the preceding count theorem
shows the two finite index ranges have equal cardinality.
-/
def LinkedOccurrenceCopies.nodeEquiv
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    AtomicIntervention.NodeEquiv
      (OccurrenceMultiworld.Encoding.signature
        (source.record.model.occurrenceMultiworld event))
      linked.signature where
  toFun := fun index =>
    let node := OccurrenceMultiworld.Encoding.decode index
    linked.worldNode node.world node.node
  invFun := fun node => Fin.cast linked.count_eq node
  left_inv := by
    intro index
    apply Fin.ext
    change (linked.worldNode
      (OccurrenceMultiworld.Encoding.decode index).world
      (OccurrenceMultiworld.Encoding.decode index).node).val = index.val
    rw [linked.worldNode_val]
    exact congrArg Fin.val
      (OccurrenceMultiworld.Encoding.encode_decode index)
  right_inv := by
    intro node
    apply Fin.ext
    change (linked.worldNode
      (OccurrenceMultiworld.Encoding.decode (Fin.cast linked.count_eq node)).world
      (OccurrenceMultiworld.Encoding.decode (Fin.cast linked.count_eq node)).node).val =
        node.val
    rw [linked.worldNode_val]
    have encoded :=
      OccurrenceMultiworld.Encoding.encode_decode
        (Fin.cast linked.count_eq node)
    exact congrArg Fin.val encoded

def LinkedOccurrenceCopies.coordinates
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms) :
    AtomicIntervention.SameCoordinates
      (OccurrenceMultiworld.Encoding.signature
        (source.record.model.occurrenceMultiworld event))
      linked.signature where
  nodeEquiv := linked.nodeEquiv
  value_eq := by
    intro index
    let occurrenceNode := OccurrenceMultiworld.Encoding.decode index
    change occurrenceNode.Value =
      linked.signature.Value
        (linked.worldNode occurrenceNode.world occurrenceNode.node)
    exact (linked.worldNode_value_eq occurrenceNode.world
      occurrenceNode.node).symm

theorem LinkedOccurrenceCopies.coordinates_toFun_encode
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (node : OccurrenceNode template event) :
    linked.coordinates.nodeEquiv.toFun
        (OccurrenceMultiworld.Encoding.encode node) =
      linked.worldNode node.world node.node := by
  simp [coordinates, nodeEquiv,
    OccurrenceMultiworld.Encoding.decode_encode]

theorem LinkedOccurrenceCopies.coordinates_invFun_worldNode
    {event : CounterfactualEvent template}
    (linked : LinkedOccurrenceCopies template source event.atoms)
    (world : OccurrenceWorld template event) (node : Fin template.count) :
    linked.coordinates.nodeEquiv.invFun (linked.worldNode world node) =
      OccurrenceMultiworld.Encoding.encode
        (⟨world, node⟩ : OccurrenceNode template event) := by
  rw [← linked.coordinates_toFun_encode
    (⟨world, node⟩ : OccurrenceNode template event)]
  exact linked.coordinates.nodeEquiv.left_inv _

/--
Compose the root-preservation witnesses from all three construction phases.
This is the root analogue of `coordinates`; it permits a source latent
assignment to be evaluated at the executable endpoint.
-/
def LinkedOccurrenceCopies.roots
    (linked : LinkedOccurrenceCopies template source atoms) :
    AtomicIntervention.SameRoots source linked.target :=
  linked.copies.roots.trans
    (linked.directed.roots.trans linked.latent.roots)

theorem LinkedOccurrenceCopies.roots_toFun
    (linked : LinkedOccurrenceCopies template source atoms)
    (sourceRoot : Fin source.record.model.latent.count) :
    linked.roots.rootEquiv.toFun sourceRoot = linked.root sourceRoot :=
  rfl

def LinkedOccurrenceCopies.rootAssignment
    (linked : LinkedOccurrenceCopies template source atoms)
    (assignment : source.record.model.latent.Assignment) :
    linked.target.record.model.latent.Assignment :=
  linked.roots.transportAssignment assignment

theorem LinkedOccurrenceCopies.rootAssignment_at
    (linked : LinkedOccurrenceCopies template source atoms)
    (assignment : source.record.model.latent.Assignment)
    (sourceRoot : Fin source.record.model.latent.count) :
    cast (linked.rootValue_eq sourceRoot)
        (linked.rootAssignment assignment (linked.root sourceRoot)) =
      assignment sourceRoot := by
  have rootEq := linked.roots_toFun sourceRoot
  have transported :=
    AtomicIntervention.SameRoots.transportAssignment_toFun
      linked.roots assignment sourceRoot
  apply eq_of_heq
  exact HEq.trans (cast_heq _ _)
    (HEq.trans
      (dependentApplyHEq (linked.rootAssignment assignment) rootEq.symm)
      (HEq.trans (cast_heq _ _).symm (heq_of_eq transported)))

end Causality
end Thesis
