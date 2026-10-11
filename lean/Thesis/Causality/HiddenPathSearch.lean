import Thesis.Causality.Reductions

namespace Thesis
namespace Causality

/-!
# Constructive hidden-internal paths and projected latent incidences

The hidden-DAG projection specification records paths in `Prop`.  A later
model construction cannot simply choose one of those paths as executable
relay data.  This module searches the actual finite predecessor list and
returns an explicitly typed path, with its edge and hidden-interior proofs.

Recursion follows incoming arrows and decreases the DAG's supplied natural
rank.  There is no guessed fuel, propositional excluded middle, or extraction
of data from an existential proof.  A specification proof establishes that
the computed option is nonempty; `Option.get` then reads that computed path.

The same search gives Boolean incidences from hidden nodes to observed
children and a checked Boolean bidirected projection.  These are graph-only
ingredients for hidden-node collapse and countermodel relay.  They do not
claim distribution preservation or complete the hidden-DAG theorem.
-/

namespace FiniteHiddenDAG

/-- A supplied successful entry suffices for the finite first-success scan.
The proof follows the option match directly.  In particular it does not use
the library's classical conversion of first-success support to an arbitrary
existential/nonexistential predicate. -/
private theorem findSome?_isSome_of_member {α β : Type}
    (items : List α) (search : α -> Option β) :
    forall item, item ∈ items -> (search item).isSome = true ->
      (items.findSome? search).isSome = true := by
  induction items with
  | nil => intro _item member _found; cases member
  | cons head tail inductionHypothesis =>
      intro item member found
      change (match search head with
        | some value => some value
        | none => tail.findSome? search).isSome = true
      cases atHead : search head with
      | some value => rfl
      | none =>
          have inTail : item ∈ tail := by
            rcases List.mem_cons.mp member with same | inTail
            · subst item
              rw [atHead] at found
              cases found
            · exact inTail
          exact inductionHypothesis item inTail found

/-- Executable path data with exactly the same hidden-interior convention
as `HiddenInternalPath`.  Endpoints need not be hidden, and a path has at
least one actual edge; a vertex is not its own reflexive path. -/
inductive HiddenInternalPathData (H : FiniteHiddenDAG S) :
    Fin H.count -> Fin H.count -> Type
  | direct {source target} (edge : H.edge source target = true) :
      HiddenInternalPathData H source target
  | tail {source middle target}
      (earlierPath : HiddenInternalPathData H source middle)
      (hidden : H.hidden middle = true) (edge : H.edge middle target = true) :
      HiddenInternalPathData H source target

/-- Every stored path satisfies the original projection specification. -/
def HiddenInternalPathData.toSpecification
    {H : FiniteHiddenDAG S} {source target : Fin H.count} :
    HiddenInternalPathData H source target -> H.HiddenInternalPath source target
  | .direct edge => .direct edge
  | .tail earlierPath hidden edge => .tail earlierPath.toSpecification hidden edge

/-- Prefer a direct edge; otherwise scan all actual hidden predecessors of
the target in their finite index order.  Recursive calls occur only under a
verified incoming edge, whose rank inequality establishes termination.
The selected path is therefore determined by the graph, not by a supplied
propositional witness or an arbitrary choice of predecessor. -/
def hiddenInternalPath? (H : FiniteHiddenDAG S) (source target : Fin H.count) :
    Option (HiddenInternalPathData H source target) :=
  if direct : H.edge source target = true then some (.direct direct)
  else (List.finRange H.count).findSome? (fun middle =>
    if hidden : H.hidden middle = true then
      if edge : H.edge middle target = true then
        (H.hiddenInternalPath? source middle).map (fun earlierPath =>
          .tail earlierPath hidden edge)
      else none
    else none)
termination_by H.rank target
decreasing_by exact H.edge_rank_lt edge

/-- Every specification path is found.  At a tail step its actual hidden
predecessor occurs in the finite scan, and the induction hypothesis supplies
the prefix.  This proof stays in `Prop`; it does not choose path data. -/
theorem hiddenInternalPath?_complete (H : FiniteHiddenDAG S)
    {source target : Fin H.count} (path : H.HiddenInternalPath source target) :
    (H.hiddenInternalPath? source target).isSome = true := by
  induction path with
  | direct edge =>
      rw [hiddenInternalPath?, dif_pos edge]
      rfl
  | @tail middle target _earlierPath hidden edge inductionHypothesis =>
      rw [hiddenInternalPath?]
      by_cases direct : H.edge source target = true
      · rw [dif_pos direct]
        rfl
      · rw [dif_neg direct]
        apply findSome?_isSome_of_member _ _ middle (List.mem_finRange middle)
        simpa only [dif_pos hidden, dif_pos edge, Option.isSome_map] using inductionHypothesis

/-- A successful search cannot introduce a spurious projection path. -/
theorem hiddenInternalPath?_sound (H : FiniteHiddenDAG S)
    {source target : Fin H.count}
    (found : (H.hiddenInternalPath? source target).isSome = true) :
    H.HiddenInternalPath source target :=
  ((H.hiddenInternalPath? source target).get found).toSpecification

/-- The Boolean support tag is an exact decision of hidden-internal
reachability, including its nonreflexive endpoint convention. -/
theorem hiddenInternalPath?_iff (H : FiniteHiddenDAG S) (source target : Fin H.count) :
    (H.hiddenInternalPath? source target).isSome = true <->
      H.HiddenInternalPath source target :=
  ⟨H.hiddenInternalPath?_sound, H.hiddenInternalPath?_complete⟩

/-- Read the deterministically searched path once the specification ensures
success.  The `Prop` argument supplies only an `isSome` proof for an existing
computed option; it is not eliminated into a selected existential witness. -/
def HiddenInternalPath.toData {H : FiniteHiddenDAG S} {source target : Fin H.count}
    (path : H.HiddenInternalPath source target) : HiddenInternalPathData H source target :=
  (H.hiddenInternalPath? source target).get (H.hiddenInternalPath?_complete path)

/-- Incidence used when hidden private-noise inputs are exposed as roots.
Only hidden nodes are selected; an observed node's own private noise will be
handled separately by a model collapse.  Multiple observed children are
retained rather than split into independent pairwise inputs. -/
def hiddenInputIncident (H : FiniteHiddenDAG S)
    (hiddenNode : Fin H.count) (child : Fin S.count) : Bool :=
  H.hidden hiddenNode && (H.hiddenInternalPath? hiddenNode (H.observedNode child)).isSome

theorem hiddenInputIncident_iff (H : FiniteHiddenDAG S)
    (hiddenNode : Fin H.count) (child : Fin S.count) :
    H.hiddenInputIncident hiddenNode child = true <->
      H.hidden hiddenNode = true /\ H.HiddenInternalPath hiddenNode (H.observedNode child) := by
  exact Bool.and_eq_true_iff.trans
    (and_congr Iff.rfl (H.hiddenInternalPath?_iff hiddenNode (H.observedNode child)))

/-- Compute the exact bidirected projection by scanning hidden common
ancestors.  Distinctness is explicit, so no reflexive bidirected edge is added. -/
def projectedBidirected? (H : FiniteHiddenDAG S) (left right : Fin S.count) : Bool :=
  decide (left ≠ right) && finAny H.count (fun hiddenNode =>
    H.hiddenInputIncident hiddenNode left && H.hiddenInputIncident hiddenNode right)

theorem projectedBidirected?_iff (H : FiniteHiddenDAG S) (left right : Fin S.count) :
    H.projectedBidirected? left right = true <-> H.projectedBidirected left right := by
  constructor
  · intro selected
    have parts := Bool.and_eq_true_iff.mp selected
    have different : left ≠ right := of_decide_eq_true parts.1
    rcases (finAny_eq_true_iff _).mp parts.2 with ⟨hiddenNode, incident⟩
    have leftIncident := (H.hiddenInputIncident_iff hiddenNode left).mp
      (Bool.and_eq_true_iff.mp incident).1
    have rightIncident := (H.hiddenInputIncident_iff hiddenNode right).mp
      (Bool.and_eq_true_iff.mp incident).2
    exact ⟨different, hiddenNode, leftIncident.1, leftIncident.2, rightIncident.2⟩
  · rintro ⟨different, hiddenNode, hidden, leftPath, rightPath⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true different, (finAny_eq_true_iff _).mpr ?_⟩
    exact ⟨hiddenNode, Bool.and_eq_true_iff.mpr
      ⟨(H.hiddenInputIncident_iff hiddenNode left).mpr ⟨hidden, leftPath⟩,
        (H.hiddenInputIncident_iff hiddenNode right).mpr ⟨hidden, rightPath⟩⟩⟩

/-- Supply the bidirected field of a full latent projection internally.
The directed embedding still has to match the given observed signature;
the hidden-path search proves the bidirected correspondence, not that
unrelated directed graphs have become equal. -/
def computedLatentProjection (H : FiniteHiddenDAG S)
    (directed : H.DirectedProjectionMatches) : FiniteLatentProjection S where
  hiddenDAG := H
  directed_matches := directed
  bidirected := H.projectedBidirected?
  bidirected_matches := H.projectedBidirected?_iff

end FiniteHiddenDAG
end Causality
end Thesis
