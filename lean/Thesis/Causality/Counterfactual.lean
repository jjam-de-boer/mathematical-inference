import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

open Probability

/-!
An explicit finite two-world representation of model-level counterfactuals.

The factual and counterfactual copies have the same observed value types and
share the original latent roots.  Directed arrows never cross worlds.  In the
counterfactual copy, a hard intervention removes every incoming observed and
latent arrow at a targeted node and replaces its mechanism by the selected
constant.  This is the finite twin-network semantics underlying
`FiniteLatentSCM.counterfactualValue`.
-/

/-- A tagged observed node in one of the two counterfactual worlds. -/
inductive TwinNode (S : ObservedSignature) where
  | factual : Fin S.count -> TwinNode S
  | counterfactual : Fin S.count -> TwinNode S
  deriving DecidableEq

namespace TwinNode

def original : TwinNode S -> Fin S.count
  | .factual i => i
  | .counterfactual i => i

def Value : TwinNode S -> Type _
  | .factual i => S.Value i
  | .counterfactual i => S.Value i

def rank (node : TwinNode S) : Nat := node.original.val

/-- A repetition-free finite enumeration of both observed copies. -/
def enumeration (S : ObservedSignature) : List (TwinNode S) :=
  (List.finRange S.count).map factual ++
    (List.finRange S.count).map counterfactual

theorem enumeration_complete (node : TwinNode S) :
    node ∈ enumeration S := by
  cases node with
  | factual i =>
      simp [enumeration]
  | counterfactual i =>
      simp [enumeration]

theorem enumeration_nodup (S : ObservedSignature) :
    (enumeration S).Nodup := by
  rw [enumeration, List.nodup_append]
  constructor
  · exact List.Pairwise.map factual (fun left right different equal =>
      different (TwinNode.factual.inj equal))
      (Probability.finRange_nodup S.count)
  constructor
  · exact List.Pairwise.map counterfactual
      (fun left right different equal =>
        different (TwinNode.counterfactual.inj equal))
      (Probability.finRange_nodup S.count)
  · intro node factualMember other counterfactualMember worldsEqual
    rcases List.mem_map.mp factualMember with ⟨i, _, nodeEqual⟩
    cases nodeEqual
    rcases List.mem_map.mp counterfactualMember with ⟨j, _, otherEqual⟩
    cases otherEqual
    cases worldsEqual

end TwinNode

/-- The finite directed-and-bidirected graph carried by a twin network. -/
structure TwinGraph (S : ObservedSignature) where
  directed : TwinNode S -> TwinNode S -> Bool
  directed_rank_lt : forall {parent child},
    directed parent child = true -> parent.rank < child.rank
  bidirected : TwinNode S -> TwinNode S -> Bool
  bidirected_symmetric : forall {left right},
    bidirected left right = true -> bidirected right left = true
  bidirected_irreflexive : forall node, bidirected node node = false

/-- A generic explicit two-world construction over one finite latent SCM. -/
structure TwinNetwork.{u, v} (S : ObservedSignature.{u}) where
  model : FiniteLatentSCM.{u, v} S
  intervention : (i : Fin S.count) -> Option (S.Value i)

namespace TwinNetwork

abbrev Assignment (_T : TwinNetwork S) :=
  (node : TwinNode S) -> node.Value

abbrev LatentAssignment (T : TwinNetwork S) := T.model.latent.Assignment

def cut (T : TwinNetwork S) (i : Fin S.count) : Bool :=
  FiniteLatentSCM.cutOf S T.intervention i

/-- Directed arrows are copied within worlds and mutilated only in the second. -/
def directed (T : TwinNetwork S) : TwinNode S -> TwinNode S -> Bool
  | .factual parent, .factual child => S.directed parent child
  | .counterfactual parent, .counterfactual child =>
      mutilatedDirected S T.cut parent child
  | _, _ => false

theorem directed_rank_lt (T : TwinNetwork S) {parent child : TwinNode S}
    (edge : T.directed parent child = true) :
    parent.rank < child.rank := by
  cases parent <;> cases child
  · simpa [TwinNode.rank, TwinNode.original] using S.directed_earlier edge
  · simp [directed] at edge
  · simp [directed] at edge
  · simpa [TwinNode.rank, TwinNode.original] using
      mutilatedDirected_earlier S T.cut edge

theorem no_directed_factual_to_counterfactual (T : TwinNetwork S) (i j) :
    T.directed (.factual i) (.counterfactual j) = false :=
  rfl

theorem no_directed_counterfactual_to_factual (T : TwinNetwork S) (i j) :
    T.directed (.counterfactual i) (.factual j) = false :=
  rfl

/-- Both worlds use the same latent roots; intervention cuts second-world input. -/
def incident (T : TwinNetwork S) (latent : Fin T.model.latent.count) :
    TwinNode S -> Bool
  | .factual child => T.model.latent.incident latent child
  | .counterfactual child =>
      if T.cut child then false else T.model.latent.incident latent child

theorem incident_factual (T : TwinNetwork S) (latent child) :
    T.incident latent (.factual child) =
      T.model.latent.incident latent child :=
  rfl

theorem incident_counterfactual_of_not_cut (T : TwinNetwork S)
    (latent child) (notCut : T.cut child = false) :
    T.incident latent (.counterfactual child) =
      T.model.latent.incident latent child := by
  simp [incident, notCut]

theorem intervention_cuts_counterfactual_directed (T : TwinNetwork S)
    (child : Fin S.count) (value : S.Value child)
    (selected : T.intervention child = some value) (parent) :
    T.directed (.counterfactual parent) (.counterfactual child) = false := by
  simp [directed, mutilatedDirected, cut, FiniteLatentSCM.cutOf, selected]

theorem intervention_cuts_counterfactual_incident (T : TwinNetwork S)
    (child : Fin S.count) (value : S.Value child)
    (selected : T.intervention child = some value) (latent) :
    T.incident latent (.counterfactual child) = false := by
  simp [incident, cut, FiniteLatentSCM.cutOf, selected]

/-- Bidirected edges are the projection of roots shared by two twin nodes. -/
def projectedBidirected (T : TwinNetwork S)
    (left right : TwinNode S) : Bool :=
  !(decide (left = right)) &&
    finAny T.model.latent.count
      (fun latent => T.incident latent left && T.incident latent right)

theorem projectedBidirected_symmetric (T : TwinNetwork S) {left right}
    (edge : T.projectedBidirected left right = true) :
    T.projectedBidirected right left = true := by
  unfold projectedBidirected at edge ⊢
  have unequal : decide (right = left) = decide (left = right) := by
    simp [eq_comm]
  have shared :
      finAny T.model.latent.count
          (fun latent => T.incident latent right && T.incident latent left) =
        finAny T.model.latent.count
          (fun latent => T.incident latent left && T.incident latent right) := by
    apply finAny_congr
    intro latent
    exact Bool.and_comm _ _
  rw [unequal, shared]
  exact edge

theorem projectedBidirected_irreflexive (T : TwinNetwork S) (node) :
    T.projectedBidirected node node = false := by
  simp [projectedBidirected]

def graph (T : TwinNetwork S) : TwinGraph S where
  directed := T.directed
  directed_rank_lt := T.directed_rank_lt
  bidirected := T.projectedBidirected
  bidirected_symmetric := T.projectedBidirected_symmetric
  bidirected_irreflexive := T.projectedBidirected_irreflexive

def ParentValues (T : TwinNetwork S) (child : TwinNode S) :=
  (parent : TwinNode S) -> T.directed parent child = true -> parent.Value

def LatentInputs (T : TwinNetwork S) (child : TwinNode S) :=
  (latent : Fin T.model.latent.count) ->
    T.incident latent child = true -> T.model.latent.Value latent

/-- The copied mechanism, with a constant mechanism at intervened second-world nodes. -/
def mechanism (T : TwinNetwork S) (child : TwinNode S)
    (parents : T.ParentValues child) (latents : T.LatentInputs child) :
    child.Value :=
  match child with
  | .factual i =>
      T.model.mechanism i
        (fun parent edge => parents (.factual parent) edge)
        (fun latent edge => latents latent edge)
  | .counterfactual i =>
      match selected : T.intervention i with
      | some value => value
      | none =>
          T.model.mechanism i
            (fun parent edge => parents (.counterfactual parent) (by
              simp [directed, mutilatedDirected, cut,
                FiniteLatentSCM.cutOf, selected, edge]))
            (fun latent edge => latents latent (by
              simp [incident, cut, FiniteLatentSCM.cutOf, selected, edge]))

/-- Evaluation of both copies under one shared latent assignment. -/
def eval (T : TwinNetwork S) (u : T.LatentAssignment) : T.Assignment
  | .factual i => T.model.eval u i
  | .counterfactual i => T.model.evalUnder T.intervention u i

def factualProjection (T : TwinNetwork S) (assignment : T.Assignment) :
    S.Assignment :=
  fun i => assignment (.factual i)

def counterfactualProjection (T : TwinNetwork S) (assignment : T.Assignment) :
    S.Assignment :=
  fun i => assignment (.counterfactual i)

theorem factualProjection_eval (T : TwinNetwork S) (u : T.LatentAssignment)
    (i : Fin S.count) :
    T.factualProjection (T.eval u) i = T.model.eval u i :=
  rfl

theorem counterfactualProjection_eval (T : TwinNetwork S)
    (u : T.LatentAssignment) (i : Fin S.count) :
    T.counterfactualProjection (T.eval u) i =
      T.model.evalUnder T.intervention u i :=
  rfl

/-- The explicit twin evaluator satisfies every copied structural mechanism. -/
theorem eval_satisfies_mechanism (T : TwinNetwork S)
    (u : T.LatentAssignment) (child : TwinNode S) :
    T.eval u child = T.mechanism child
      (fun parent _edge => T.eval u parent)
      (fun latent _edge => u latent) := by
  cases child with
  | factual i =>
      change T.model.evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u i =
        T.model.mechanism i
          (fun parent _edge => T.model.evalNodeUnder
            (FiniteLatentSCM.noIntervention S) u parent)
          (fun latent _edge => u latent)
      rw [FiniteLatentSCM.evalNodeUnder]
      rfl
  | counterfactual i =>
      cases selected : T.intervention i with
      | some value =>
          simp only [eval, mechanism, FiniteLatentSCM.evalUnder]
          rw [selected]
          change T.model.evalNodeUnder T.intervention u i = value
          rw [FiniteLatentSCM.evalNodeUnder]
          simp [FiniteLatentSCM.equationUnder, selected]

      | none =>
          simp only [eval, mechanism, FiniteLatentSCM.evalUnder]
          rw [selected]
          change T.model.evalNodeUnder T.intervention u i =
            T.model.mechanism i
              (fun parent _edge =>
                T.model.evalNodeUnder T.intervention u parent)
              (fun latent _edge => u latent)
          rw [FiniteLatentSCM.evalNodeUnder]
          simp [FiniteLatentSCM.equationUnder, selected]

/-! ## Materialization as an ordinary finite-indexed SCM -/

namespace Encoding

def encode (S : ObservedSignature) : TwinNode S -> Fin (S.count + S.count)
  | .factual node => ⟨node.val, by omega⟩
  | .counterfactual node => ⟨S.count + node.val, by omega⟩

def decode (S : ObservedSignature) (index : Fin (S.count + S.count)) :
    TwinNode S :=
  if first : index.val < S.count then
    .factual ⟨index.val, first⟩
  else
    .counterfactual ⟨index.val - S.count, by omega⟩

@[simp] theorem decode_encode (S : ObservedSignature) (node : TwinNode S) :
    decode S (encode S node) = node := by
  cases node with
  | factual node => simp [decode, encode]
  | counterfactual node =>
      have notFirst : ¬ S.count + node.val < S.count := by omega
      simp [decode, encode, notFirst]

@[simp] theorem encode_decode (S : ObservedSignature)
    (index : Fin (S.count + S.count)) :
    encode S (decode S index) = index := by
  unfold decode
  split
  · apply Fin.ext
    simp [encode]
  · apply Fin.ext
    simp [encode]
    omega

def valueEnumeration (S : ObservedSignature) (node : TwinNode S) :
    List node.Value :=
  match node with
  | .factual original => S.valueEnumeration original
  | .counterfactual original => S.valueEnumeration original

theorem valueEnumeration_complete (S : ObservedSignature)
    (node : TwinNode S) (value : node.Value) :
    value ∈ valueEnumeration S node := by
  cases node with
  | factual original => exact S.value_complete original value
  | counterfactual original => exact S.value_complete original value

theorem valueEnumeration_nodup (S : ObservedSignature) (node : TwinNode S) :
    (valueEnumeration S node).Nodup := by
  cases node with
  | factual original => exact S.value_nodup original
  | counterfactual original => exact S.value_nodup original

def defaultValue (S : ObservedSignature) (node : TwinNode S) : node.Value :=
  match node with
  | .factual original => S.defaultValue original
  | .counterfactual original => S.defaultValue original

def valueDecidableEq (S : ObservedSignature) (node : TwinNode S) :
    DecidableEq node.Value :=
  match node with
  | .factual original => S.valueDecidableEq original
  | .counterfactual original => S.valueDecidableEq original

def signature (T : TwinNetwork S) : ObservedSignature where
  count := S.count + S.count
  Value := fun index => (decode S index).Value
  valueEnumeration := fun index => valueEnumeration S (decode S index)
  value_complete := fun index => valueEnumeration_complete S (decode S index)
  value_nodup := fun index => valueEnumeration_nodup S (decode S index)
  defaultValue := fun index => defaultValue S (decode S index)
  valueDecidableEq := fun index => valueDecidableEq S (decode S index)
  directed := fun parent child => T.directed (decode S parent) (decode S child)
  directed_earlier := by
    intro parent child edge
    have parentEncoded := congrArg Fin.val (encode_decode S parent)
    have childEncoded := congrArg Fin.val (encode_decode S child)
    cases parentNode : decode S parent with
    | factual parentOriginal =>
        cases childNode : decode S child with
        | factual childOriginal =>
            have rankEarlier := T.directed_rank_lt edge
            simp [parentNode, childNode, TwinNode.rank, TwinNode.original]
              at rankEarlier
            simp [encode, parentNode] at parentEncoded
            simp [encode, childNode] at childEncoded
            omega
        | counterfactual childOriginal =>
            simp [TwinNetwork.directed, parentNode, childNode] at edge
    | counterfactual parentOriginal =>
        cases childNode : decode S child with
        | factual childOriginal =>
            simp [TwinNetwork.directed, parentNode, childNode] at edge
        | counterfactual childOriginal =>
            have rankEarlier := T.directed_rank_lt edge
            simp [parentNode, childNode, TwinNode.rank, TwinNode.original]
              at rankEarlier
            simp [encode, parentNode] at parentEncoded
            simp [encode, childNode] at childEncoded
            omega

def latent (T : TwinNetwork S) : LatentExtension (signature T) where
  count := T.model.latent.count
  Value := T.model.latent.Value
  valueEnumeration := T.model.latent.valueEnumeration
  value_complete := T.model.latent.value_complete
  valueDecidableEq := T.model.latent.valueDecidableEq
  incident := fun source child => T.incident source (decode S child)

def parentValue (T : TwinNetwork S) (child : Fin (signature T).count)
    (parents : (signature T).ParentValues child)
    (parent : TwinNode S) (edge : T.directed parent (decode S child) = true) :
    parent.Value :=
  cast (congrArg TwinNode.Value (decode_encode S parent))
    (parents (encode S parent) (by simpa [signature] using edge))

def latentValue (T : TwinNetwork S) (child : Fin (signature T).count)
    (latents : (latent T).Inputs child)
    (source : Fin T.model.latent.count)
    (incident : T.incident source (decode S child) = true) :
    T.model.latent.Value source :=
  latents source (by simpa [latent] using incident)

def mechanism (T : TwinNetwork S) (child : Fin (signature T).count)
    (parents : (signature T).ParentValues child)
    (latents : (latent T).Inputs child) : (signature T).Value child :=
  T.mechanism (decode S child)
    (fun parent edge => parentValue T child parents parent edge)
    (fun source incident => latentValue T child latents source incident)

/-- The explicit twin graph and mechanisms as a standard finite latent SCM. -/
def model (T : TwinNetwork S) : FiniteLatentSCM (signature T) where
  latent := latent T
  factor := T.model.factor
  prior := T.model.prior
  product_law := T.model.product_law
  mechanism := mechanism T

def encodeAssignment (T : TwinNetwork S) (assignment : T.Assignment) :
    (signature T).Assignment :=
  fun index => assignment (decode S index)

def decodeAssignment (T : TwinNetwork S)
    (assignment : (signature T).Assignment) : T.Assignment :=
  fun node =>
    cast (congrArg TwinNode.Value (decode_encode S node))
      (assignment (encode S node))

def encodeEvent (T : TwinNetwork S) (event : T.Assignment -> Bool) :
    (signature T).Assignment -> Bool :=
  fun assignment => event (decodeAssignment T assignment)

theorem decodeAssignment_encodeAssignment (T : TwinNetwork S)
    (assignment : T.Assignment) :
    decodeAssignment T (encodeAssignment T assignment) = assignment := by
  funext node
  unfold decodeAssignment encodeAssignment
  apply eq_of_heq
  exact (cast_heq (congrArg TwinNode.Value (decode_encode S node))
    (assignment (decode S (encode S node)))).trans (by rw [decode_encode])

@[simp] theorem encodeEvent_encodeAssignment (T : TwinNetwork S)
    (event : T.Assignment -> Bool) (assignment : T.Assignment) :
    encodeEvent T event (encodeAssignment T assignment) = event assignment := by
  simp [encodeEvent, decodeAssignment_encodeAssignment]

/-- The materialized SCM evaluator agrees with the direct shared-root twin. -/
theorem model_eval (T : TwinNetwork S) (u : T.LatentAssignment)
    (child : Fin (signature T).count) :
    (model T).eval u child = T.eval u (decode S child) := by
  change (model T).evalNodeUnder
      (FiniteLatentSCM.noIntervention (signature T)) u child =
    T.eval u (decode S child)
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  simp only [FiniteLatentSCM.noIntervention]
  rw [T.eval_satisfies_mechanism u (decode S child)]
  unfold model mechanism
  change T.mechanism (decode S child)
      (fun parent edge => parentValue T child
        (fun candidate _edge =>
          (model T).evalNodeUnder
            (FiniteLatentSCM.noIntervention (signature T)) u candidate)
        parent edge)
      (fun source incident => latentValue T child
        (fun candidate _incident => u candidate) source incident) =
    T.mechanism (decode S child) (fun parent _edge => T.eval u parent)
      (fun latent _edge => u latent)
  congr 1
  · funext parent edge
    unfold parentValue
    have recursive := model_eval T u (encode S parent)
    change (model T).evalNodeUnder
      (FiniteLatentSCM.noIntervention (signature T)) u (encode S parent) =
        T.eval u (decode S (encode S parent)) at recursive
    simp only
    rw [recursive]
    apply eq_of_heq
    exact (cast_heq (congrArg TwinNode.Value (decode_encode S parent))
      (T.eval u (decode S (encode S parent)))).trans (by
        rw [decode_encode])
termination_by child.val
decreasing_by
  exact (signature T).directed_earlier (by simpa [signature] using edge)

theorem model_eval_eq_encodeAssignment (T : TwinNetwork S)
    (u : T.LatentAssignment) :
    (model T).eval u = encodeAssignment T (T.eval u) := by
  funext child
  exact model_eval T u child

/-- Materialization preserves the probability of every decidable twin event. -/
theorem model_observationalValue_encodeEvent (T : TwinNetwork S)
    (event : T.Assignment -> Bool) :
    QProb.Equiv ((model T).observationalValue (encodeEvent T event))
      ((T.model.prior.map T.eval).probVal event) := by
  exact QProb.equiv_trans
    ((model T).observationalValue_eq (encodeEvent T event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr T.model.prior _ _ (fun u => by
        rw [model_eval_eq_encodeAssignment]
        exact encodeEvent_encodeAssignment T event (T.eval u)))
      (QProb.equiv_symm (FiniteProbRecord.map_probVal T.model.prior T.eval event)))

end Encoding

/-- The unconditioned joint distribution of the factual and hypothetical worlds. -/
def jointDist (T : TwinNetwork S) : FiniteProbRecord T.Assignment :=
  T.model.prior.map T.eval

def factualEvent (T : TwinNetwork S) (event : S.Assignment -> Bool) :
    T.Assignment -> Bool :=
  fun assignment => event (T.factualProjection assignment)

def counterfactualEvent (T : TwinNetwork S) (event : S.Assignment -> Bool) :
    T.Assignment -> Bool :=
  fun assignment => event (T.counterfactualProjection assignment)

def jointEvent (T : TwinNetwork S) (evidence event : S.Assignment -> Bool) :
    T.Assignment -> Bool :=
  fun assignment =>
    T.factualEvent evidence assignment && T.counterfactualEvent event assignment

theorem factual_marginal (T : TwinNetwork S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv ((T.jointDist).probVal (T.factualEvent event))
      (T.model.observationalValue event) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal T.model.prior T.eval (T.factualEvent event))
    (QProb.equiv_symm (T.model.observationalValue_eq event))

theorem counterfactual_marginal (T : TwinNetwork S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv ((T.jointDist).probVal (T.counterfactualEvent event))
      (T.model.interventionalValue T.intervention event) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal T.model.prior T.eval
      (T.counterfactualEvent event))
    (QProb.equiv_symm
      (T.model.interventionalValue_eq T.intervention event))

theorem joint_event_eq (T : TwinNetwork S)
    (evidence event : S.Assignment -> Bool) :
    QProb.Equiv ((T.jointDist).probVal (T.jointEvent evidence event))
      (T.model.prior.probVal (fun u =>
        evidence (T.model.eval u) &&
          event (T.model.evalUnder T.intervention u))) :=
  FiniteProbRecord.map_probVal T.model.prior T.eval
    (T.jointEvent evidence event)

def latentEvidencePositive (T : TwinNetwork S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : T.model.CounterfactualSupported evidence) :
    T.model.prior.EventPositive (fun u => evidence (T.model.eval u)) := by
  simpa [FiniteLatentSCM.CounterfactualSupported,
    FiniteLatentSCM.observationalDist, FiniteProbRecord.EventPositive,
    FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using hEvidence

/-- Abduction conditions the shared roots before both copied worlds are evaluated. -/
def abductedDist (T : TwinNetwork S) (evidence : S.Assignment -> Bool)
    (hEvidence : T.model.CounterfactualSupported evidence) :
    FiniteProbRecord T.Assignment :=
  (T.model.prior.conditionOn (fun u => evidence (T.model.eval u))
    (T.latentEvidencePositive evidence hEvidence)).map T.eval

def abductedCounterfactualValue (T : TwinNetwork S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : T.model.CounterfactualSupported evidence)
    (event : S.Assignment -> Bool) : QProb :=
  (T.abductedDist evidence hEvidence).probVal (T.counterfactualEvent event)

/-- The explicit twin network computes exactly the existing model-level helper. -/
theorem abductedCounterfactualValue_eq_counterfactualValue
    (T : TwinNetwork S) (evidence : S.Assignment -> Bool)
    (hEvidence : T.model.CounterfactualSupported evidence)
    (event : S.Assignment -> Bool) :
    QProb.Equiv
      (T.abductedCounterfactualValue evidence hEvidence event)
      (T.model.counterfactualValue evidence hEvidence T.intervention event) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal
      (T.model.prior.conditionOn (fun u => evidence (T.model.eval u))
        (T.latentEvidencePositive evidence hEvidence))
      T.eval (T.counterfactualEvent event))
    (QProb.equiv_refl _)

end TwinNetwork

namespace FiniteLatentSCM

/-- Construct the explicit factual/counterfactual two-world network. -/
def twinNetwork (M : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i)) :
    TwinNetwork S where
  model := M
  intervention := intervention

end FiniteLatentSCM

/-! ## General finite multiworld query semantics -/

/-- One fixed-value potential-outcome claim `V_action = value`. -/
structure CounterfactualAtom (S : ObservedSignature) where
  action : (i : Fin S.count) -> Option (S.Value i)
  node : Fin S.count
  value : S.Value node

namespace CounterfactualAtom

def holds (atom : CounterfactualAtom S) (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) : Bool :=
  decide (M.evalUnder atom.action u atom.node = atom.value)

end CounterfactualAtom

/-- Finite Boolean combinations of potential outcomes sharing one latent unit. -/
inductive CounterfactualEvent (S : ObservedSignature) where
  | truth
  | falsity
  | atom : CounterfactualAtom S -> CounterfactualEvent S
  | conj : CounterfactualEvent S -> CounterfactualEvent S ->
      CounterfactualEvent S
  | disj : CounterfactualEvent S -> CounterfactualEvent S ->
      CounterfactualEvent S
  | neg : CounterfactualEvent S -> CounterfactualEvent S

namespace CounterfactualEvent

def holds (event : CounterfactualEvent S) (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) : Bool :=
  match event with
  | CounterfactualEvent.truth => true
  | CounterfactualEvent.falsity => false
  | CounterfactualEvent.atom counterfactualAtom =>
      counterfactualAtom.holds M u
  | CounterfactualEvent.conj left right => left.holds M u && right.holds M u
  | CounterfactualEvent.disj left right => left.holds M u || right.holds M u
  | CounterfactualEvent.neg inner => !(inner.holds M u)

def conjunction : List (CounterfactualEvent S) -> CounterfactualEvent S
  | [] => .truth
  | event :: events => .conj event (conjunction events)

theorem conjunction_holds (events : List (CounterfactualEvent S))
    (M : FiniteLatentSCM S) (u : M.latent.Assignment) :
    (conjunction events).holds M u = events.all (fun event => event.holds M u) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      simp [conjunction, holds, ih]

/-- A complete assignment claim in one intervention world. -/
def assignmentClaim
    (action : (i : Fin S.count) -> Option (S.Value i))
    (assignment : S.Assignment) : CounterfactualEvent S :=
  conjunction ((List.finRange S.count).map (fun node =>
    .atom ⟨action, node, assignment node⟩))

private theorem assignment_all_eq {S : ObservedSignature}
    (left right : S.Assignment) :
    (List.finRange S.count).all (fun node => decide (left node = right node)) =
      decide (left = right) := by
  by_cases same : left = right
  · subst right
    simp
  · have allFalse :
        (List.finRange S.count).all
            (fun node => decide (left node = right node)) = false := by
      cases allEqual : (List.finRange S.count).all
          (fun node => decide (left node = right node)) with
      | false => rfl
      | true =>
          exfalso
          apply same
          funext node
          have component :=
            (List.all_eq_true.mp allEqual) node (List.mem_finRange node)
          simpa using component
    simp [allFalse, same]

theorem assignmentClaim_holds
    (action : (i : Fin S.count) -> Option (S.Value i))
    (assignment : S.Assignment) (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) :
    (assignmentClaim action assignment).holds M u =
      decide (M.evalUnder action u = assignment) := by
  rw [assignmentClaim, conjunction_holds]
  simpa [CounterfactualAtom.holds] using
    (assignment_all_eq (M.evalUnder action u) assignment)

def assignmentEventFrom
    (action : (i : Fin S.count) -> Option (S.Value i)) :
    List S.Assignment -> CounterfactualEvent S
  | [] => .falsity
  | assignment :: assignments =>
      .disj (assignmentClaim action assignment)
        (assignmentEventFrom action assignments)

theorem assignmentEventFrom_holds
    (action : (i : Fin S.count) -> Option (S.Value i))
    (assignments : List S.Assignment) (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) :
    (assignmentEventFrom action assignments).holds M u =
      assignments.any (fun assignment =>
        decide (M.evalUnder action u = assignment)) := by
  induction assignments with
  | nil => rfl
  | cons assignment assignments ih =>
      simp [assignmentEventFrom, holds, assignmentClaim_holds, ih]

/-- Compile a Boolean assignment event into a finite potential-outcome formula. -/
def assignmentEvent
    (action : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) : CounterfactualEvent S :=
  assignmentEventFrom action (S.assignmentEnumeration.filter event)

theorem assignmentEvent_holds
    (action : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) :
    (assignmentEvent action event).holds M u =
      event (M.evalUnder action u) := by
  unfold assignmentEvent
  rw [assignmentEventFrom_holds]
  cases selected : event (M.evalUnder action u) with
  | false =>
      apply (List.any_eq_false).mpr
      intro assignment member equal
      have eventTrue := (List.mem_filter.mp member).2
      have same : M.evalUnder action u = assignment := by
        simpa using equal
      rw [← same, selected] at eventTrue
      contradiction
  | true =>
      apply (List.any_eq_true).mpr
      exact ⟨M.evalUnder action u,
        (List.mem_filter.mpr
          ⟨S.assignmentEnumeration_complete _, selected⟩), by simp⟩

end CounterfactualEvent

/-- A finite conditional counterfactual query `P(outcome | condition)`. -/
structure CounterfactualQuery (S : ObservedSignature) where
  outcome : CounterfactualEvent S
  condition : CounterfactualEvent S

namespace CounterfactualQuery

def unconditional (outcome : CounterfactualEvent S) : CounterfactualQuery S where
  outcome := outcome
  condition := .truth

/-- The ordinary one-action, factual-evidence counterfactual query. -/
def singleAction (evidence : S.Assignment -> Bool)
    (action : (i : Fin S.count) -> Option (S.Value i))
    (outcome : S.Assignment -> Bool) : CounterfactualQuery S where
  outcome := CounterfactualEvent.assignmentEvent action outcome
  condition := CounterfactualEvent.assignmentEvent
    (FiniteLatentSCM.noIntervention S) evidence

def denominator (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    QProb :=
  M.prior.probVal (query.condition.holds M)

def numerator (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    QProb :=
  M.prior.probVal (fun u =>
    query.condition.holds M u && query.outcome.holds M u)

/-- Partial semantics retains zero-denominator counterfactual conditions. -/
def denote (query : CounterfactualQuery S) (M : FiniteLatentSCM S) :
    ProbabilityResult.Result :=
  ProbabilityResult.divide (some (query.numerator M))
    (some (query.denominator M))

theorem singleAction_condition_holds
    (evidence : S.Assignment -> Bool)
    (action : (i : Fin S.count) -> Option (S.Value i))
    (outcome : S.Assignment -> Bool) (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) :
    (singleAction evidence action outcome).condition.holds M u =
      evidence (M.eval u) := by
  simpa [singleAction, FiniteLatentSCM.eval] using
    (CounterfactualEvent.assignmentEvent_holds
      (FiniteLatentSCM.noIntervention S) evidence M u)

theorem singleAction_outcome_holds
    (evidence : S.Assignment -> Bool)
    (action : (i : Fin S.count) -> Option (S.Value i))
    (outcome : S.Assignment -> Bool) (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) :
    (singleAction evidence action outcome).outcome.holds M u =
      outcome (M.evalUnder action u) := by
  simpa [singleAction] using
    (CounterfactualEvent.assignmentEvent_holds action outcome M u)

/-- The general query syntax recovers the original one-action helper exactly. -/
noncomputable def singleAction_denote_eq_counterfactualValue
    (M : FiniteLatentSCM S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (action : (i : Fin S.count) -> Option (S.Value i))
    (outcome : S.Assignment -> Bool) :
    ProbabilityResult.Equivalent
      ((singleAction evidence action outcome).denote M)
      (some (M.counterfactualValue evidence hEvidence action outcome)) := by
  let query := singleAction evidence action outcome
  have numeratorEquivalent : QProb.Equiv (query.numerator M)
      (M.prior.probVal (fun u =>
        evidence (M.eval u) && outcome (M.evalUnder action u))) :=
    FiniteProbRecord.probVal_congr M.prior _ _ (fun u => by
      rw [singleAction_condition_holds, singleAction_outcome_holds])
  have denominatorEquivalent : QProb.Equiv (query.denominator M)
      (M.prior.probVal (fun u => evidence (M.eval u))) :=
    FiniteProbRecord.probVal_congr M.prior _ _ (fun u =>
      singleAction_condition_holds evidence action outcome M u)
  have positive :
      0 < (M.prior.probVal (fun u => evidence (M.eval u))).num := by
    simpa [FiniteLatentSCM.CounterfactualSupported,
      FiniteLatentSCM.observationalDist, FiniteProbRecord.EventPositive,
      FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using
      hEvidence
  have queryToRatio : ProbabilityResult.Equivalent (query.denote M)
      (ProbabilityResult.divide
        (some (M.prior.probVal (fun u =>
          evidence (M.eval u) && outcome (M.evalUnder action u))))
        (some (M.prior.probVal (fun u => evidence (M.eval u))))) :=
    ProbabilityResult.divide_congr
      (.value numeratorEquivalent) (.value denominatorEquivalent)
  exact ProbabilityResult.trans queryToRatio (by
    simp only [ProbabilityResult.divide, positive, ↓reduceDIte]
    exact .value (QProb.equiv_symm
      (M.counterfactualValue_eq evidence hEvidence action outcome)))

/-- The same one-action query is computed by the explicit shared-noise twin. -/
noncomputable def singleAction_denote_eq_twinNetwork
    (M : FiniteLatentSCM S) (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (action : (i : Fin S.count) -> Option (S.Value i))
    (outcome : S.Assignment -> Bool) :
    ProbabilityResult.Equivalent
      ((singleAction evidence action outcome).denote M)
      (some ((M.twinNetwork action).abductedCounterfactualValue
        evidence hEvidence outcome)) :=
  ProbabilityResult.trans
    (singleAction_denote_eq_counterfactualValue
      M evidence hEvidence action outcome)
    (.value (QProb.equiv_symm
      ((M.twinNetwork action).abductedCounterfactualValue_eq_counterfactualValue
        evidence hEvidence outcome)))

end CounterfactualQuery

end Causality
end Thesis
