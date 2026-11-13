import Thesis.Causality.Counterfactual

namespace Thesis
namespace Causality

open Probability

universe u v

/-!
Occurrence-indexed finite multiworld semantics.

Every syntactic counterfactual atom receives its own world, even when two
atoms carry extensionally equal actions.  All worlds share the source model's
latent roots.  The construction is therefore intensional, finite and does not
need to decide equality of dependent intervention functions.
-/

namespace CounterfactualEvent

/-- Counterfactual atoms in left-to-right syntactic occurrence order. -/
def atoms : CounterfactualEvent S -> List (CounterfactualAtom S)
  | CounterfactualEvent.truth => []
  | CounterfactualEvent.falsity => []
  | CounterfactualEvent.atom counterfactualAtom => [counterfactualAtom]
  | CounterfactualEvent.conj left right => left.atoms ++ right.atoms
  | CounterfactualEvent.disj left right => left.atoms ++ right.atoms
  | CounterfactualEvent.neg event => event.atoms

/--
Evaluate an event from a list containing one complete assignment per atom
occurrence.  Conjunction and disjunction split the list according to syntax,
so repeated actions remain separate occurrences.
-/
def holdsWith : (event : CounterfactualEvent S) ->
    List S.Assignment -> Bool
  | CounterfactualEvent.truth, _ => true
  | CounterfactualEvent.falsity, _ => false
  | CounterfactualEvent.atom counterfactualAtom, assignments =>
      match assignments with
      | [] => false
      | assignment :: _ =>
          decide (assignment counterfactualAtom.node = counterfactualAtom.value)
  | CounterfactualEvent.conj left right, assignments =>
      left.holdsWith (assignments.take left.atoms.length) &&
        right.holdsWith (assignments.drop left.atoms.length)
  | CounterfactualEvent.disj left right, assignments =>
      left.holdsWith (assignments.take left.atoms.length) ||
        right.holdsWith (assignments.drop left.atoms.length)
  | CounterfactualEvent.neg event, assignments => !(event.holdsWith assignments)

theorem atoms_map_eval_append (left right : CounterfactualEvent S)
    (M : FiniteLatentSCM S) (u : M.latent.Assignment) :
    (left.atoms ++ right.atoms).map
        (fun atom => M.evalUnder atom.action u) =
      left.atoms.map (fun atom => M.evalUnder atom.action u) ++
        right.atoms.map (fun atom => M.evalUnder atom.action u) := by
  exact List.map_append

/-- Occurrence-list evaluation is exactly the original shared-unit semantics. -/
theorem holdsWith_atoms_map_eval (event : CounterfactualEvent S)
    (M : FiniteLatentSCM S) (u : M.latent.Assignment) :
    event.holdsWith
        (event.atoms.map (fun atom => M.evalUnder atom.action u)) =
      event.holds M u := by
  induction event with
  | truth => simp [holdsWith, CounterfactualEvent.holds]
  | falsity => simp [holdsWith, CounterfactualEvent.holds]
  | atom counterfactualAtom =>
      simp [atoms, holdsWith, CounterfactualEvent.holds,
        CounterfactualAtom.holds]
  | conj left right leftIH rightIH =>
      simp only [atoms, List.map_append, holdsWith]
      rw [← List.length_map (as := left.atoms)
        (fun atom : CounterfactualAtom S => M.evalUnder atom.action u)]
      rw [List.take_left, List.drop_left]
      rw [leftIH, rightIH]
      rfl
  | disj left right leftIH rightIH =>
      simp only [atoms, List.map_append, holdsWith]
      rw [← List.length_map (as := left.atoms)
        (fun atom : CounterfactualAtom S => M.evalUnder atom.action u)]
      rw [List.take_left, List.drop_left]
      rw [leftIH, rightIH]
      rfl
  | neg event ih =>
      simp only [atoms, holdsWith, holds]
      rw [ih]

end CounterfactualEvent

/-! ## Worlds and nodes -/

/-- The factual world or one counterfactual atom occurrence. -/
inductive OccurrenceWorld (S : ObservedSignature)
    (event : CounterfactualEvent S) where
  | factual
  | counterfactual (occurrence : Fin event.atoms.length)
  deriving DecidableEq

namespace OccurrenceWorld

def enumeration (event : CounterfactualEvent S) :
    List (OccurrenceWorld S event) :=
  .factual :: (List.finRange event.atoms.length).map .counterfactual

theorem enumeration_complete (world : OccurrenceWorld S event) :
    world ∈ enumeration event := by
  cases world with
  | factual => simp [enumeration]
  | counterfactual occurrence => simp [enumeration]

def index {S : ObservedSignature} {event : CounterfactualEvent S} :
    OccurrenceWorld S event -> Fin (event.atoms.length + 1)
  | .factual => ⟨0, Nat.zero_lt_succ _⟩
  | .counterfactual occurrence =>
      ⟨occurrence.val + 1, Nat.succ_lt_succ occurrence.isLt⟩

def ofIndex {S : ObservedSignature} {event : CounterfactualEvent S}
    (index : Fin (event.atoms.length + 1)) :
    OccurrenceWorld S event :=
  Fin.cases .factual (fun occurrence => .counterfactual occurrence) index

@[simp] theorem ofIndex_index {S : ObservedSignature}
    {event : CounterfactualEvent S} (world : OccurrenceWorld S event) :
    ofIndex (S := S) (event := event) world.index = world := by
  cases world <;> rfl

@[simp] theorem index_ofIndex {S : ObservedSignature}
    {event : CounterfactualEvent S}
    (index : Fin (event.atoms.length + 1)) :
    (ofIndex (S := S) (event := event) index).index = index := by
  refine Fin.cases ?_ (fun occurrence => ?_) index
  · rfl
  · rfl

def action {S : ObservedSignature} {event : CounterfactualEvent S} :
    OccurrenceWorld S event ->
      ((node : Fin S.count) -> Option (S.Value node))
  | .factual => FiniteLatentSCM.noIntervention S
  | .counterfactual occurrence => (event.atoms.get occurrence).action

end OccurrenceWorld

/-- One observed node in one occurrence-indexed world. -/
structure OccurrenceNode (S : ObservedSignature)
    (event : CounterfactualEvent S) where
  world : OccurrenceWorld S event
  node : Fin S.count
  deriving DecidableEq

namespace OccurrenceNode

def Value (node : OccurrenceNode S event) := S.Value node.node

def rank (node : OccurrenceNode S event) : Nat := node.node.val

def enumeration (event : CounterfactualEvent S) :
    List (OccurrenceNode S event) :=
  (OccurrenceWorld.enumeration event).flatMap fun world =>
    (List.finRange S.count).map fun node => ⟨world, node⟩

theorem enumeration_complete (node : OccurrenceNode S event) :
    node ∈ enumeration event := by
  rw [enumeration, List.mem_flatMap]
  exact ⟨node.world, OccurrenceWorld.enumeration_complete node.world,
    by simp⟩

/-- Exactly the nodes belonging to syntactic counterfactual occurrences. -/
def counterfactualEnumeration (event : CounterfactualEvent S) :
    List (OccurrenceNode S event) :=
  (List.finRange event.atoms.length).flatMap fun occurrence =>
    (List.finRange S.count).map fun node =>
      ⟨OccurrenceWorld.counterfactual occurrence, node⟩

theorem counterfactualEnumeration_complete
    {S : ObservedSignature} {event : CounterfactualEvent S}
    (occurrence : Fin event.atoms.length) (node : Fin S.count) :
    (⟨OccurrenceWorld.counterfactual (S := S) (event := event) occurrence, node⟩ :
      OccurrenceNode S event) ∈ counterfactualEnumeration event := by
  rw [counterfactualEnumeration, List.mem_flatMap]
  exact ⟨occurrence, List.mem_finRange occurrence, by simp⟩

theorem factual_not_mem_counterfactualEnumeration
    {S : ObservedSignature} {event : CounterfactualEvent S}
    (node : Fin S.count) :
    (⟨OccurrenceWorld.factual (S := S) (event := event), node⟩ :
      OccurrenceNode S event) ∉
      counterfactualEnumeration event := by
  simp [counterfactualEnumeration]

end OccurrenceNode

/-- Apply a dependent function along an equality of its indices. -/
theorem dependentApplyHEq {α : Type _} {β : α -> Type _}
    (f : (value : α) -> β value) {left right : α}
    (equal : left = right) :
    f left ≍ f right := by
  cases equal
  rfl

/-! ## Direct combined multiworld model -/

structure OccurrenceMultiworld (S : ObservedSignature.{u})
    (event : CounterfactualEvent S) where
  model : FiniteLatentSCM.{u, v} S

namespace OccurrenceMultiworld

abbrev Assignment (_W : OccurrenceMultiworld S event) :=
  (node : OccurrenceNode S event) -> node.Value

abbrev LatentAssignment (W : OccurrenceMultiworld S event) :=
  W.model.latent.Assignment

def action (_W : OccurrenceMultiworld S event)
    (world : OccurrenceWorld S event) :=
  world.action

def directed (W : OccurrenceMultiworld S event)
    (parent child : OccurrenceNode S event) : Bool :=
  if _same : parent.world = child.world then
    mutilatedDirected S
      (FiniteLatentSCM.cutOf S (W.action child.world))
      parent.node child.node
  else false

theorem directed_same_world (W : OccurrenceMultiworld S event)
    {parent child : OccurrenceNode S event}
    (edge : W.directed parent child = true) :
    parent.world = child.world := by
  unfold directed at edge
  split at edge
  · assumption
  · simp at edge

theorem directed_rank_lt (W : OccurrenceMultiworld S event)
    {parent child : OccurrenceNode S event}
    (edge : W.directed parent child = true) :
    parent.rank < child.rank := by
  unfold directed at edge
  split at edge
  · exact mutilatedDirected_earlier S
      (FiniteLatentSCM.cutOf S (W.action child.world)) edge
  · simp at edge

def incident (W : OccurrenceMultiworld S event)
    (source : Fin W.model.latent.count)
    (child : OccurrenceNode S event) : Bool :=
  if FiniteLatentSCM.cutOf S (W.action child.world) child.node then false
  else W.model.latent.incident source child.node

def mechanism (W : OccurrenceMultiworld S event)
    (child : OccurrenceNode S event)
    (parents : (parent : OccurrenceNode S event) ->
      W.directed parent child = true -> parent.Value)
    (latents : (source : Fin W.model.latent.count) ->
      W.incident source child = true -> W.model.latent.Value source) :
    child.Value :=
  match selected : W.action child.world child.node with
  | some value => value
  | none =>
      W.model.mechanism child.node
        (fun parent edge => parents ⟨child.world, parent⟩ (by
          simp [directed, selected, FiniteLatentSCM.cutOf,
            mutilatedDirected, edge]))
        (fun source incident => latents source (by
          simp [OccurrenceMultiworld.incident, selected,
            FiniteLatentSCM.cutOf, incident]))

def eval (W : OccurrenceMultiworld S event)
    (u : W.LatentAssignment) : W.Assignment :=
  fun node => W.model.evalUnder (W.action node.world) u node.node

theorem eval_satisfies_mechanism (W : OccurrenceMultiworld S event)
    (u : W.LatentAssignment) (child : OccurrenceNode S event) :
    W.eval u child = W.mechanism child
      (fun parent _edge => W.eval u parent)
      (fun source _edge => u source) := by
  cases child with
  | mk world child =>
      cases world with
      | factual =>
          change W.model.evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u child =
            W.model.mechanism child
              (fun parent _edge => W.model.evalNodeUnder
                (FiniteLatentSCM.noIntervention S) u parent)
              (fun source _edge => u source)
          rw [FiniteLatentSCM.evalNodeUnder]
          rfl
      | counterfactual occurrence =>
          cases selected :
              W.action (.counterfactual occurrence) child with
          | some value =>
              simp only [eval, mechanism, FiniteLatentSCM.evalUnder]
              rw [selected]
              change W.model.evalNodeUnder
                  (W.action (.counterfactual occurrence)) u child = value
              rw [FiniteLatentSCM.evalNodeUnder]
              simp [FiniteLatentSCM.equationUnder, selected]
          | none =>
              simp only [eval, mechanism, FiniteLatentSCM.evalUnder]
              rw [selected]
              change W.model.evalNodeUnder
                  (W.action (.counterfactual occurrence)) u child =
                W.model.mechanism child
                  (fun parent _edge =>
                    W.model.evalNodeUnder
                      (W.action (.counterfactual occurrence)) u parent)
                  (fun source _edge => u source)
              rw [FiniteLatentSCM.evalNodeUnder]
              simp [FiniteLatentSCM.equationUnder, selected]

def factualProjection (W : OccurrenceMultiworld S event)
    (assignment : W.Assignment) : S.Assignment :=
  fun node => assignment ⟨.factual, node⟩

def occurrenceProjection (W : OccurrenceMultiworld S event)
    (assignment : W.Assignment) (occurrence : Fin event.atoms.length) :
    S.Assignment :=
  fun node => assignment ⟨.counterfactual occurrence, node⟩

def occurrenceAssignments (W : OccurrenceMultiworld S event)
    (assignment : W.Assignment) : List S.Assignment :=
  List.ofFn (fun occurrence => W.occurrenceProjection assignment occurrence)

private theorem ofFn_get_map {α β : Type _} (items : List α) (f : α → β) :
    List.ofFn (fun index => f (items.get index)) = items.map f := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      rw [List.ofFn_succ]
      simp only [List.get_eq_getElem, List.map_cons]
      congr

def eventPredicate (W : OccurrenceMultiworld S event) :
    W.Assignment -> Bool :=
  fun assignment => event.holdsWith (W.occurrenceAssignments assignment)

@[simp] theorem occurrenceProjection_eval
    (W : OccurrenceMultiworld S event) (u : W.LatentAssignment)
    (occurrence : Fin event.atoms.length) :
    W.occurrenceProjection (W.eval u) occurrence =
      W.model.evalUnder (event.atoms.get occurrence).action u := by
  rfl

theorem occurrenceAssignments_eval
    (W : OccurrenceMultiworld S event) (u : W.LatentAssignment) :
    W.occurrenceAssignments (W.eval u) =
      event.atoms.map (fun atom => W.model.evalUnder atom.action u) := by
  change List.ofFn (fun occurrence =>
    W.model.evalUnder (event.atoms.get occurrence).action u) =
      event.atoms.map (fun atom => W.model.evalUnder atom.action u)
  exact ofFn_get_map event.atoms
    (fun atom => W.model.evalUnder atom.action u)

theorem eventPredicate_eval (W : OccurrenceMultiworld S event)
    (u : W.LatentAssignment) :
    W.eventPredicate (W.eval u) = event.holds W.model u := by
  rw [eventPredicate, occurrenceAssignments_eval]
  exact event.holdsWith_atoms_map_eval W.model u

def jointDist (W : OccurrenceMultiworld S event) :
    FiniteProbRecord W.Assignment :=
  W.model.prior.map W.eval

theorem eventProbability (W : OccurrenceMultiworld S event) :
    QProb.Equiv (W.jointDist.probVal W.eventPredicate)
      (W.model.prior.probVal (event.holds W.model)) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal W.model.prior W.eval W.eventPredicate)
    (FiniteProbRecord.probVal_congr W.model.prior _ _
      (fun u => W.eventPredicate_eval u))

/-! ## Materialization as an ordinary finite-indexed SCM -/

namespace Encoding

def encode {S : ObservedSignature} {event : CounterfactualEvent S}
    (node : OccurrenceNode S event) :
    Fin ((event.atoms.length + 1) * S.count) :=
  ⟨node.world.index.val * S.count + node.node.val, by
    have worldBound := node.world.index.isLt
    have nodeBound := node.node.isLt
    calc
      node.world.index.val * S.count + node.node.val <
          node.world.index.val * S.count + S.count :=
        Nat.add_lt_add_left nodeBound _
      _ = Nat.succ node.world.index.val * S.count :=
        (Nat.succ_mul _ _).symm
      _ ≤ (event.atoms.length + 1) * S.count :=
        Nat.mul_le_mul_right S.count (Nat.succ_le_of_lt worldBound)⟩

def decode {S : ObservedSignature} {event : CounterfactualEvent S}
    (index : Fin ((event.atoms.length + 1) * S.count)) :
    OccurrenceNode S event :=
  if positive : 0 < S.count then
    { world := OccurrenceWorld.ofIndex
        ⟨index.val / S.count,
          (Nat.div_lt_iff_lt_mul positive).2 index.isLt⟩
      node := ⟨index.val % S.count, Nat.mod_lt _ positive⟩ }
  else
    False.elim (by
      have zero : S.count = 0 := Nat.eq_zero_of_not_pos positive
      simpa [zero] using index.isLt)

@[simp] theorem decode_encode {S : ObservedSignature}
    {event : CounterfactualEvent S} (node : OccurrenceNode S event) :
    decode (encode node) = node := by
  have positive : 0 < S.count := Nat.zero_lt_of_lt node.node.isLt
  unfold decode
  rw [dif_pos positive]
  have indexEq :
      (⟨(encode node).val / S.count,
          (Nat.div_lt_iff_lt_mul positive).2 (encode node).isLt⟩ :
        Fin (event.atoms.length + 1)) = node.world.index := by
    apply Fin.ext
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · calc
        node.world.index.val * S.count + node.node.val <
            node.world.index.val * S.count + S.count :=
          Nat.add_lt_add_left node.node.isLt _
        _ = Nat.succ node.world.index.val * S.count :=
          (Nat.succ_mul _ _).symm
  have worldEq :
      OccurrenceWorld.ofIndex
          ⟨(encode node).val / S.count,
            (Nat.div_lt_iff_lt_mul positive).2 (encode node).isLt⟩ =
        node.world := by
    rw [indexEq, OccurrenceWorld.ofIndex_index]
  rw [worldEq]
  congr
  change
    (node.world.index.val * S.count + node.node.val) % S.count =
      node.node.val
  rw [Nat.add_comm]
  rw [Nat.mul_comm node.world.index.val S.count]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt node.node.isLt

@[simp] theorem encode_decode {S : ObservedSignature}
    {event : CounterfactualEvent S}
    (index : Fin ((event.atoms.length + 1) * S.count)) :
    encode (decode index) = index := by
  by_cases positive : 0 < S.count
  · unfold decode
    rw [dif_pos positive]
    apply Fin.ext
    simp only [encode, OccurrenceWorld.index_ofIndex]
    rw [Nat.mul_comm (index.val / S.count) S.count]
    exact Nat.div_add_mod index.val S.count
  · have zero : S.count = 0 := Nat.eq_zero_of_not_pos positive
    have impossible : False := by simpa [zero] using index.isLt
    exact impossible.elim

def valueEnumeration (node : OccurrenceNode S event) :
    List node.Value :=
  S.valueEnumeration node.node

theorem valueEnumeration_complete (node : OccurrenceNode S event)
    (value : node.Value) :
    value ∈ valueEnumeration node :=
  S.value_complete node.node value

theorem valueEnumeration_nodup (node : OccurrenceNode S event) :
    (valueEnumeration node).Nodup :=
  S.value_nodup node.node

def defaultValue (node : OccurrenceNode S event) : node.Value :=
  S.defaultValue node.node

def valueDecidableEq (node : OccurrenceNode S event) :
    DecidableEq node.Value :=
  S.valueDecidableEq node.node

def signature (W : OccurrenceMultiworld S event) : ObservedSignature where
  count := (event.atoms.length + 1) * S.count
  Value := fun index => (decode index).Value
  valueEnumeration := fun index => valueEnumeration (decode index)
  value_complete := fun index => valueEnumeration_complete (decode index)
  value_nodup := fun index => valueEnumeration_nodup (decode index)
  defaultValue := fun index => defaultValue (decode index)
  valueDecidableEq := fun index => valueDecidableEq (decode index)
  directed := fun parent child => W.directed (decode parent) (decode child)
  directed_earlier := by
    intro parent child edge
    have sameWorld := W.directed_same_world edge
    have rankEarlier := W.directed_rank_lt edge
    have sameIndex :
        (decode parent).world.index.val =
          (decode child).world.index.val :=
      congrArg
        (fun world : OccurrenceWorld S event => world.index.val) sameWorld
    have parentEncoded := congrArg Fin.val (encode_decode parent)
    have childEncoded := congrArg Fin.val (encode_decode child)
    change
      (decode parent).world.index.val * S.count +
          (decode parent).node.val = parent.val at parentEncoded
    change
      (decode child).world.index.val * S.count +
          (decode child).node.val = child.val at childEncoded
    change (decode parent).node.val < (decode child).node.val at rankEarlier
    rw [sameIndex] at parentEncoded
    omega

def latent (W : OccurrenceMultiworld S event) :
    LatentExtension (signature W) where
  count := W.model.latent.count
  Value := W.model.latent.Value
  valueEnumeration := W.model.latent.valueEnumeration
  value_complete := W.model.latent.value_complete
  valueDecidableEq := W.model.latent.valueDecidableEq
  incident := fun source child => W.incident source (decode child)

def parentValue (W : OccurrenceMultiworld S event)
    (child : Fin (signature W).count)
    (parents : (signature W).ParentValues child)
    (parent : OccurrenceNode S event)
    (edge : W.directed parent (decode child) = true) :
    parent.Value :=
  cast (congrArg (fun node : OccurrenceNode S event => node.Value)
      (decode_encode parent))
    (parents (encode parent) (by simpa [signature] using edge))

def latentValue (W : OccurrenceMultiworld S event)
    (child : Fin (signature W).count)
    (latents : (latent W).Inputs child)
    (source : Fin W.model.latent.count)
    (incident : W.incident source (decode child) = true) :
    W.model.latent.Value source :=
  latents source (by simpa [latent] using incident)

def mechanism (W : OccurrenceMultiworld S event)
    (child : Fin (signature W).count)
    (parents : (signature W).ParentValues child)
    (latents : (latent W).Inputs child) :
    (signature W).Value child :=
  W.mechanism (decode child)
    (fun parent edge => parentValue W child parents parent edge)
    (fun source incident => latentValue W child latents source incident)

/-- The combined occurrence worlds as one ordinary finite latent SCM. -/
def model (W : OccurrenceMultiworld S event) :
    FiniteLatentSCM (signature W) where
  latent := latent W
  factor := W.model.factor
  prior := W.model.prior
  product_law := W.model.product_law
  mechanism := mechanism W

def encodeAssignment (W : OccurrenceMultiworld S event)
    (assignment : W.Assignment) : (signature W).Assignment :=
  fun index => assignment (decode index)

def decodeAssignment (W : OccurrenceMultiworld S event)
    (assignment : (signature W).Assignment) : W.Assignment :=
  fun node =>
    cast (congrArg (fun current : OccurrenceNode S event => current.Value)
      (decode_encode node))
      (assignment (encode node))

def encodeEvent (W : OccurrenceMultiworld S event)
    (predicate : W.Assignment -> Bool) :
    (signature W).Assignment -> Bool :=
  fun assignment => predicate (decodeAssignment W assignment)

theorem decodeAssignment_encodeAssignment
    (W : OccurrenceMultiworld S event) (assignment : W.Assignment) :
    decodeAssignment W (encodeAssignment W assignment) = assignment := by
  funext node
  unfold decodeAssignment encodeAssignment
  apply eq_of_heq
  exact
    (cast_heq
      (congrArg (fun current : OccurrenceNode S event => current.Value)
        (decode_encode node))
      (assignment (decode (encode node)))).trans (by rw [decode_encode])

@[simp] theorem encodeEvent_encodeAssignment
    (W : OccurrenceMultiworld S event)
    (predicate : W.Assignment -> Bool) (assignment : W.Assignment) :
    encodeEvent W predicate (encodeAssignment W assignment) =
      predicate assignment := by
  simp [encodeEvent, decodeAssignment_encodeAssignment]

/-- The materialized SCM evaluator agrees with the direct combined evaluator. -/
theorem model_eval (W : OccurrenceMultiworld S event)
    (u : W.LatentAssignment) (child : Fin (signature W).count) :
    (model W).eval u child = W.eval u (decode child) := by
  change (model W).evalNodeUnder
      (FiniteLatentSCM.noIntervention (signature W)) u child =
    W.eval u (decode child)
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  simp only [FiniteLatentSCM.noIntervention]
  rw [W.eval_satisfies_mechanism u (decode child)]
  unfold model mechanism
  change W.mechanism (decode child)
      (fun parent edge => parentValue W child
        (fun candidate _edge =>
          (model W).evalNodeUnder
            (FiniteLatentSCM.noIntervention (signature W)) u candidate)
        parent edge)
      (fun source incident => latentValue W child
        (fun candidate _incident => u candidate) source incident) =
    W.mechanism (decode child) (fun parent _edge => W.eval u parent)
      (fun source _edge => u source)
  congr 1
  · funext parent edge
    unfold parentValue
    have recursive := model_eval W u (encode parent)
    change (model W).evalNodeUnder
        (FiniteLatentSCM.noIntervention (signature W)) u (encode parent) =
      W.eval u (decode (encode parent)) at recursive
    have evaluatedHEq :
        W.eval u (decode (encode parent)) ≍ W.eval u parent := by
      exact dependentApplyHEq (fun node => W.eval u node)
        (decode_encode parent)
    apply eq_of_heq
    exact (cast_heq _ _).trans
      ((heq_of_eq recursive).trans evaluatedHEq)
termination_by child.val
decreasing_by
  exact (signature W).directed_earlier (by simpa [signature] using edge)

theorem model_eval_eq_encodeAssignment
    (W : OccurrenceMultiworld S event) (u : W.LatentAssignment) :
    (model W).eval u = encodeAssignment W (W.eval u) := by
  funext child
  exact model_eval W u child

theorem model_observationalValue_encodeEvent
    (W : OccurrenceMultiworld S event)
    (predicate : W.Assignment -> Bool) :
    QProb.Equiv
      ((model W).observationalValue (encodeEvent W predicate))
      (W.jointDist.probVal predicate) := by
  exact QProb.equiv_trans
    ((model W).observationalValue_eq (encodeEvent W predicate))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr W.model.prior _ _ (fun u => by
        rw [model_eval_eq_encodeAssignment]
        exact encodeEvent_encodeAssignment W predicate (W.eval u)))
      (QProb.equiv_symm
        (FiniteProbRecord.map_probVal W.model.prior W.eval predicate)))

/-- Materialization preserves the original shared-latent event probability. -/
theorem model_eventProbability (W : OccurrenceMultiworld S event) :
    QProb.Equiv
      ((model W).observationalValue (encodeEvent W W.eventPredicate))
      (W.model.prior.probVal (event.holds W.model)) :=
  QProb.equiv_trans
    (model_observationalValue_encodeEvent W W.eventPredicate)
    W.eventProbability

end Encoding

end OccurrenceMultiworld

namespace FiniteLatentSCM

/-- Build the direct occurrence-indexed combined multiworld specification. -/
def occurrenceMultiworld (M : FiniteLatentSCM S)
    (event : CounterfactualEvent S) : OccurrenceMultiworld S event where
  model := M

end FiniteLatentSCM

namespace CounterfactualQuery

/-- One occurrence list containing the condition first and the outcome second. -/
def combinedEvent (query : CounterfactualQuery S) : CounterfactualEvent S :=
  .conj query.condition query.outcome

def combinedConditionPredicate
    (query : CounterfactualQuery S)
    (W : OccurrenceMultiworld S query.combinedEvent) :
    W.Assignment -> Bool :=
  fun assignment =>
    query.condition.holdsWith
      (List.take query.condition.atoms.length
        (W.occurrenceAssignments assignment))

def combinedOutcomePredicate
    (query : CounterfactualQuery S)
    (W : OccurrenceMultiworld S query.combinedEvent) :
    W.Assignment -> Bool :=
  fun assignment =>
    query.outcome.holdsWith
      (List.drop query.condition.atoms.length
        (W.occurrenceAssignments assignment))

def combinedNumeratorPredicate
    (query : CounterfactualQuery S)
    (W : OccurrenceMultiworld S query.combinedEvent) :
    W.Assignment -> Bool :=
  fun assignment =>
    query.combinedConditionPredicate W assignment &&
      query.combinedOutcomePredicate W assignment

theorem combinedConditionPredicate_eval
    (query : CounterfactualQuery S)
    (W : OccurrenceMultiworld S query.combinedEvent)
    (u : W.LatentAssignment) :
    query.combinedConditionPredicate W (W.eval u) =
      query.condition.holds W.model u := by
  unfold combinedConditionPredicate
  rw [W.occurrenceAssignments_eval]
  simp only [combinedEvent, CounterfactualEvent.atoms, List.map_append]
  rw [← List.length_map
    (as := query.condition.atoms)
    (fun atom : CounterfactualAtom S => W.model.evalUnder atom.action u)]
  rw [List.take_left]
  exact query.condition.holdsWith_atoms_map_eval W.model u

theorem combinedOutcomePredicate_eval
    (query : CounterfactualQuery S)
    (W : OccurrenceMultiworld S query.combinedEvent)
    (u : W.LatentAssignment) :
    query.combinedOutcomePredicate W (W.eval u) =
      query.outcome.holds W.model u := by
  unfold combinedOutcomePredicate
  rw [W.occurrenceAssignments_eval]
  simp only [combinedEvent, CounterfactualEvent.atoms, List.map_append]
  rw [← List.length_map
    (as := query.condition.atoms)
    (fun atom : CounterfactualAtom S => W.model.evalUnder atom.action u)]
  rw [List.drop_left]
  exact query.outcome.holdsWith_atoms_map_eval W.model u

theorem combinedNumeratorPredicate_eval
    (query : CounterfactualQuery S)
    (W : OccurrenceMultiworld S query.combinedEvent)
    (u : W.LatentAssignment) :
    query.combinedNumeratorPredicate W (W.eval u) =
      (query.condition.holds W.model u &&
        query.outcome.holds W.model u) := by
  unfold combinedNumeratorPredicate
  rw [query.combinedConditionPredicate_eval W u,
    query.combinedOutcomePredicate_eval W u]

def combinedWorld (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    OccurrenceMultiworld S query.combinedEvent :=
  M.occurrenceMultiworld query.combinedEvent

def combinedModel (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    FiniteLatentSCM
      (OccurrenceMultiworld.Encoding.signature (query.combinedWorld M)) :=
  OccurrenceMultiworld.Encoding.model (query.combinedWorld M)

def combinedDenominator (query : CounterfactualQuery S)
    (M : FiniteLatentSCM S) :
    QProb :=
  (query.combinedModel M).observationalValue
    (OccurrenceMultiworld.Encoding.encodeEvent (query.combinedWorld M)
      (query.combinedConditionPredicate (query.combinedWorld M)))

def combinedNumerator (query : CounterfactualQuery S)
    (M : FiniteLatentSCM S) :
    QProb :=
  (query.combinedModel M).observationalValue
    (OccurrenceMultiworld.Encoding.encodeEvent (query.combinedWorld M)
      (query.combinedNumeratorPredicate (query.combinedWorld M)))

theorem combinedDenominator_equiv
    (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    QProb.Equiv (query.combinedDenominator M) (query.denominator M) := by
  let W := query.combinedWorld M
  exact QProb.equiv_trans
    (OccurrenceMultiworld.Encoding.model_observationalValue_encodeEvent W
      (query.combinedConditionPredicate W))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal W.model.prior W.eval
        (query.combinedConditionPredicate W))
      (FiniteProbRecord.probVal_congr W.model.prior _ _
        (fun u => query.combinedConditionPredicate_eval W u)))

theorem combinedNumerator_equiv
    (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    QProb.Equiv (query.combinedNumerator M) (query.numerator M) := by
  let W := query.combinedWorld M
  exact QProb.equiv_trans
    (OccurrenceMultiworld.Encoding.model_observationalValue_encodeEvent W
      (query.combinedNumeratorPredicate W))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal W.model.prior W.eval
        (query.combinedNumeratorPredicate W))
      (FiniteProbRecord.probVal_congr W.model.prior _ _
        (fun u => query.combinedNumeratorPredicate_eval W u)))

def combinedDenote (query : CounterfactualQuery S)
    (M : FiniteLatentSCM S) :
    ProbabilityResult.Result :=
  ProbabilityResult.divide (some (query.combinedNumerator M))
    (some (query.combinedDenominator M))

noncomputable def combinedDenote_equivalent
    (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    ProbabilityResult.Equivalent (query.combinedDenote M) (query.denote M) :=
  ProbabilityResult.divide_congr
    (.value (query.combinedNumerator_equiv M))
    (.value (query.combinedDenominator_equiv M))

end CounterfactualQuery

end Causality
end Thesis
