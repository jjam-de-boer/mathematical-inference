import Thesis.Causality.Model

namespace Thesis
namespace Causality

open Probability

/-!
Finite reductions used around the causal correspondence.

The first construction projects an arbitrary finite all-directed hidden DAG
to an observed directed-and-bidirected graph.  Internal vertices of a
projecting path must be hidden.  The second construction turns an already
functional Bayesian network with one independent seed per observed node into
a Markovian `FiniteLatentSCM`.

Neither construction asserts the external completeness theorem.  The final
section separately proves the functional-representation result that produces
finite response-function seeds from arbitrary rational CPT rows.
-/

/--
A finite all-directed DAG together with an embedding of the observed nodes.
Every node is classified as hidden or as an embedded observed node. `rank`
supplies an explicit acyclicity witness.
-/
structure FiniteHiddenDAG (S : ObservedSignature) where
  count : Nat
  observedNode : Fin S.count -> Fin count
  observedNode_injective : Function.Injective observedNode
  hidden : Fin count -> Bool
  observed_not_hidden : forall i, hidden (observedNode i) = false
  node_classified : forall node,
    hidden node = true \/ Exists fun i => observedNode i = node
  edge : Fin count -> Fin count -> Bool
  rank : Fin count -> Nat
  edge_rank_lt : forall {i j}, edge i j = true -> rank i < rank j

namespace FiniteHiddenDAG

/--
A directed path whose internal vertices are hidden.  The initial and final
vertices need not be hidden, which permits latent-to-observed and
observed-to-observed projected paths.
-/
inductive HiddenInternalPath (H : FiniteHiddenDAG S) :
    Fin H.count -> Fin H.count -> Prop
  | direct {i j} : H.edge i j = true -> HiddenInternalPath H i j
  | tail {i j k} :
      HiddenInternalPath H i j ->
      H.hidden j = true ->
      H.edge j k = true ->
      HiddenInternalPath H i k

theorem HiddenInternalPath.rank_lt (H : FiniteHiddenDAG S) {i j}
    (path : H.HiddenInternalPath i j) : H.rank i < H.rank j := by
  induction path with
  | direct edge => exact H.edge_rank_lt edge
  | tail _ _ edge ih =>
      exact Nat.lt_trans ih (H.edge_rank_lt edge)

theorem HiddenInternalPath.irreflexive (H : FiniteHiddenDAG S) (i) :
    Not (H.HiddenInternalPath i i) := by
  intro path
  exact (Nat.lt_irrefl (H.rank i)) path.rank_lt

/-- A projected observed arrow is a hidden-internal directed path. -/
def projectedDirected (H : FiniteHiddenDAG S)
    (i j : Fin S.count) : Prop :=
  H.HiddenInternalPath (H.observedNode i) (H.observedNode j)

/--
A projected bidirected edge is witnessed by a hidden common ancestor with
hidden-internal directed paths to two distinct observed endpoints.
-/
def projectedBidirected (H : FiniteHiddenDAG S)
    (i j : Fin S.count) : Prop :=
  i ≠ j /\
    Exists fun latent : Fin H.count =>
      H.hidden latent = true /\
      H.HiddenInternalPath latent (H.observedNode i) /\
      H.HiddenInternalPath latent (H.observedNode j)

theorem projectedBidirected_symmetric (H : FiniteHiddenDAG S) {i j}
    (edge : H.projectedBidirected i j) : H.projectedBidirected j i := by
  rcases edge with ⟨hne, latent, hidden, left, right⟩
  exact ⟨Ne.symm hne, latent, hidden, right, left⟩

theorem projectedBidirected_irreflexive (H : FiniteHiddenDAG S) (i) :
    Not (H.projectedBidirected i i) := by
  intro edge
  exact edge.1 rfl

/-- The signature's directed graph is exactly the directed latent projection. -/
def DirectedProjectionMatches (H : FiniteHiddenDAG S) : Prop :=
  forall i j, S.directed i j = true <-> H.projectedDirected i j

theorem directed_projection_iff (H : FiniteHiddenDAG S)
    (hMatches : H.DirectedProjectionMatches) (i j) :
    S.directed i j = true <-> H.projectedDirected i j :=
  hMatches i j

end FiniteHiddenDAG

/--
An exact latent projection packages a full hidden DAG with the proof that the
observed signature's directed arrows are precisely its projected arrows.
-/
structure FiniteLatentProjection (S : ObservedSignature) where
  hiddenDAG : FiniteHiddenDAG S
  directed_matches : hiddenDAG.DirectedProjectionMatches
  bidirected : Fin S.count -> Fin S.count -> Bool
  bidirected_matches : forall i j,
    bidirected i j = true <-> hiddenDAG.projectedBidirected i j

namespace FiniteLatentProjection

/-- The observed ADMG obtained by hiding the full graph's hidden vertices. -/
def observedGraph (P : FiniteLatentProjection S) : ObservedGraph S where
  bidirected := P.bidirected
  bidirected_symmetric := by
    intro i j edge
    apply (P.bidirected_matches j i).mpr
    exact P.hiddenDAG.projectedBidirected_symmetric
      ((P.bidirected_matches i j).mp edge)
  bidirected_irreflexive := by
    intro i
    cases edgeEq : P.bidirected i i with
    | false => rfl
    | true =>
        exact (P.hiddenDAG.projectedBidirected_irreflexive i
          ((P.bidirected_matches i i).mp edgeEq)).elim

theorem observedGraph_directed_iff (P : FiniteLatentProjection S) (i j) :
    P.observedGraph.DirectedEdge i j <->
      P.hiddenDAG.projectedDirected i j :=
  P.directed_matches i j

theorem observedGraph_bidirected_iff (P : FiniteLatentProjection S) (i j) :
    P.observedGraph.bidirected i j = true <->
      P.hiddenDAG.projectedBidirected i j :=
  P.bidirected_matches i j

end FiniteLatentProjection

/--
A finite functional Bayesian network with one independent random seed per
observed node.  Parent inputs are restricted by the signature, and the exact
joint seed law is supplied together with its product-law proof.
-/
structure FunctionalCBN.{u} (S : ObservedSignature.{u}) where
  Seed : Fin S.count -> Type u
  seedEnumeration : (i : Fin S.count) -> List (Seed i)
  seed_complete : forall i seed, seed ∈ seedEnumeration i
  seedDecidableEq : (i : Fin S.count) -> DecidableEq (Seed i)
  factor : (i : Fin S.count) -> FiniteProbRecord (Seed i)
  prior : FiniteProbRecord ((i : Fin S.count) -> Seed i)
  product_law :
    forall events : (i : Fin S.count) -> Seed i -> Bool,
      QProb.Equiv
        (prior.probVal
          (FiniteProduct.rectangularEvent S.count Seed events))
        (FiniteProduct.qProduct S.count
          (fun i => (factor i).probVal (events i)))
  mechanism :
    (child : Fin S.count) -> S.ParentValues child -> Seed child -> S.Value child

namespace FunctionalCBN

instance (B : FunctionalCBN S) (i : Fin S.count) : DecidableEq (B.Seed i) :=
  B.seedDecidableEq i

/-- Each Bayesian-network seed becomes a private latent root. -/
def latentExtension (B : FunctionalCBN S) : LatentExtension S where
  count := S.count
  Value := B.Seed
  valueEnumeration := B.seedEnumeration
  value_complete := B.seed_complete
  valueDecidableEq := B.seedDecidableEq
  incident := fun source child => decide (source = child)

theorem latentExtension_incident_iff (B : FunctionalCBN S) (source child) :
    B.latentExtension.incident source child = true <-> source = child := by
  simp [latentExtension]

theorem latentExtension_markovian (B : FunctionalCBN S) :
    B.latentExtension.Markovian := by
  intro source i j hi hj
  have hsi : source = i :=
    (B.latentExtension_incident_iff source i).mp hi
  have hsj : source = j :=
    (B.latentExtension_incident_iff source j).mp hj
  exact hsi.symm.trans hsj

/--
The corresponding Markovian SCM.  This is a data-preserving conversion:
the joint seed record, source factors, and local mechanisms are reused.
-/
def toSCM (B : FunctionalCBN S) : FiniteLatentSCM S where
  latent := B.latentExtension
  factor := B.factor
  prior := B.prior
  product_law := by
    intro events
    simpa [LatentExtension.rectangularEvent, latentExtension] using
      B.product_law events
  mechanism := fun child parents latents =>
    B.mechanism child parents
      (latents child (by simp [latentExtension]))

theorem toSCM_isMarkovian (B : FunctionalCBN S) :
    B.toSCM.IsMarkovian :=
  B.latentExtension_markovian

theorem toSCM_has_no_bidirected (B : FunctionalCBN S) (i j) :
    B.toSCM.observedGraph.bidirected i j = false :=
  B.toSCM.markovian_projection_has_no_bidirected B.toSCM_isMarkovian i j

/-- The converted SCM keeps each local seed distribution definitionally. -/
theorem toSCM_factor_prob (B : FunctionalCBN S) (i)
    (event : B.Seed i -> Bool) :
    QProb.Equiv ((B.toSCM.factor i).probVal event)
      ((B.factor i).probVal event) :=
  QProb.equiv_refl _

/-- The converted SCM keeps the full independent seed law definitionally. -/
theorem toSCM_prior_prob (B : FunctionalCBN S)
    (event : ((i : Fin S.count) -> B.Seed i) -> Bool) :
    QProb.Equiv (B.toSCM.prior.probVal event) (B.prior.probVal event) :=
  QProb.equiv_refl _

end FunctionalCBN

/-! ## Generic finite rational CPT functionalisation -/

/--
A finite rational conditional probability table.  Parent configurations are
indexed by an explicit finite type, and every row may initially use its own
rational denominators.
-/
structure FiniteRationalCPT.{u} (S : ObservedSignature.{u}) where
  configCount : Fin S.count -> Nat
  encode : (child : Fin S.count) ->
    S.ParentValues child -> Fin (configCount child)
  decode : (child : Fin S.count) ->
    Fin (configCount child) -> S.ParentValues child
  decode_encode : forall child parents,
    decode child (encode child parents) = parents
  encode_decode : forall child config,
    encode child (decode child config) = config
  row : (child : Fin S.count) -> Fin (configCount child) ->
    CommonDenominator.FiniteQMass (S.Value child)

namespace FiniteRationalCPT

abbrev ResponseSeed (C : FiniteRationalCPT S) (child : Fin S.count) :=
  FiniteProduct.Assignment (C.configCount child) (fun _ => S.Value child)

def rowRecord (C : FiniteRationalCPT S) (child : Fin S.count)
    (config : Fin (C.configCount child)) : FiniteProbRecord (S.Value child) :=
  (C.row child config).toRecord

/--
The exogenous seed for a node is a complete deterministic response table, one
potential output for every parent configuration.  Its law is the product of
the original CPT rows.
-/
def responseFactor (C : FiniteRationalCPT S) (child : Fin S.count) :
    FiniteProbRecord (C.ResponseSeed child) :=
  FiniteProduct.record (C.configCount child) (fun _ => S.Value child)
    (C.rowRecord child)

def responseEnumeration (C : FiniteRationalCPT S)
    (child : Fin S.count) : List (C.ResponseSeed child) :=
  FiniteProduct.enumeration (C.configCount child)
    (fun _ => S.Value child) (fun _ => S.valueEnumeration child)

theorem responseEnumeration_complete (C : FiniteRationalCPT S)
    (child : Fin S.count) (seed : C.ResponseSeed child) :
    seed ∈ C.responseEnumeration child := by
  exact FiniteProduct.enumeration_complete (C.configCount child)
    (fun _ => S.Value child) (fun _ => S.valueEnumeration child)
    (fun _ value => S.value_complete child value) seed

def responseSeedDecidableEq (C : FiniteRationalCPT S)
    (child : Fin S.count) : DecidableEq (C.ResponseSeed child) :=
  FiniteProduct.assignmentDecidableEq (C.configCount child)
    (fun _ => S.Value child) (fun _ => S.valueDecidableEq child)

def responseMechanism (C : FiniteRationalCPT S)
    (child : Fin S.count) (parents : S.ParentValues child)
    (seed : C.ResponseSeed child) : S.Value child :=
  seed (C.encode child parents)

/-- Selecting a response-table coordinate recovers exactly the chosen row. -/
theorem responseFactor_preserves_row (C : FiniteRationalCPT S)
    (child : Fin S.count) (parents : S.ParentValues child)
    (event : S.Value child -> Bool) :
    QProb.Equiv
      ((C.responseFactor child).probVal
        (fun seed => event (C.responseMechanism child parents seed)))
      ((C.rowRecord child (C.encode child parents)).probVal event) := by
  exact FiniteProduct.record_coordinate_probVal (C.configCount child)
    (S.Value child) (C.rowRecord child) (C.encode child parents) event

theorem finiteProduct_rectangular_eq_finAll (n : Nat)
    (Value : Fin n -> Type u) (events : (i : Fin n) -> Value i -> Bool)
    (assignment : FiniteProduct.Assignment n Value) :
    FiniteProduct.rectangularEvent n Value events assignment =
      finAll n (fun i => events i (assignment i)) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [FiniteProduct.rectangularEvent, finAll,
        ih (fun i => Value i.castSucc) (fun i => events i.castSucc)
          (fun i => assignment i.castSucc), Bool.and_comm]

def responsePrior (C : FiniteRationalCPT S) :
    FiniteProbRecord ((child : Fin S.count) -> C.ResponseSeed child) :=
  FiniteProduct.record S.count C.ResponseSeed C.responseFactor

/--
Every finite rational CPT has a functional Bayesian-network representation
with one independent response-function seed per observed node.
-/
def toFunctionalCBN (C : FiniteRationalCPT S) : FunctionalCBN S where
  Seed := C.ResponseSeed
  seedEnumeration := C.responseEnumeration
  seed_complete := C.responseEnumeration_complete
  seedDecidableEq := C.responseSeedDecidableEq
  factor := C.responseFactor
  prior := C.responsePrior
  product_law := by
    intro events
    exact FiniteProduct.record_rectangular_probVal
      S.count C.ResponseSeed C.responseFactor events
  mechanism := C.responseMechanism

def toSCM (C : FiniteRationalCPT S) : FiniteLatentSCM S :=
  C.toFunctionalCBN.toSCM

theorem toSCM_isMarkovian (C : FiniteRationalCPT S) :
    C.toSCM.IsMarkovian :=
  C.toFunctionalCBN.toSCM_isMarkovian

/-- The final SCM retains every original rational CPT row. -/
theorem toSCM_preserves_row (C : FiniteRationalCPT S)
    (child : Fin S.count) (parents : S.ParentValues child)
    (event : S.Value child -> Bool) :
    QProb.Equiv
      ((C.toSCM.factor child).probVal
        (fun seed => event (C.responseMechanism child parents seed)))
      ((C.row child (C.encode child parents)).toRecord.probVal event) := by
  exact C.responseFactor_preserves_row child parents event

/--
The response-table event that makes one observed node take its value in a
fixed complete assignment.  The parent configuration is read from that same
assignment.
-/
def responseSingletonEvent (C : FiniteRationalCPT S)
    (assignment : S.Assignment) (child : Fin S.count) :
    C.ResponseSeed child -> Bool :=
  fun seed => FiniteProbRecord.singletonEvent (assignment child)
    (C.responseMechanism child
      (fun parent _ => assignment parent) seed)

/-- If every selected response agrees with an assignment, SCM evaluation does. -/
theorem toSCM_evalNode_eq_of_responseSingletons
    (C : FiniteRationalCPT S)
    (seeds : C.toSCM.latent.Assignment) (assignment : S.Assignment)
    (agreements : forall child,
      C.responseMechanism child (fun parent _ => assignment parent)
        (seeds child) = assignment child)
    (child : Fin S.count) :
    C.toSCM.evalNodeUnder (FiniteLatentSCM.noIntervention S) seeds child =
      assignment child := by
  rw [FiniteLatentSCM.evalNodeUnder]
  simp only [FiniteLatentSCM.equationUnder,
    FiniteLatentSCM.noIntervention]
  change C.responseMechanism child
      (fun parent edge =>
        C.toSCM.evalNodeUnder (FiniteLatentSCM.noIntervention S) seeds parent)
      (seeds child) = assignment child
  have parentsAgree :
      (fun (parent : Fin S.count)
          (_edge : S.directed parent child = true) =>
          C.toSCM.evalNodeUnder (FiniteLatentSCM.noIntervention S) seeds parent) =
        (fun (parent : Fin S.count)
          (_edge : S.directed parent child = true) => assignment parent) := by
    funext parent edge
    exact C.toSCM_evalNode_eq_of_responseSingletons
      seeds assignment agreements parent
  rw [parentsAgree]
  exact agreements child
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- Complete SCM evaluation agrees with an assignment exactly when every
selected response-table coordinate agrees with it. -/
theorem toSCM_eval_eq_iff_responseSingletons
    (C : FiniteRationalCPT S)
    (seeds : C.toSCM.latent.Assignment) (assignment : S.Assignment) :
    C.toSCM.eval seeds = assignment <->
      forall child,
        C.responseMechanism child (fun parent _ => assignment parent)
          (seeds child) = assignment child := by
  constructor
  · intro evaluated child
    have childEq := congrFun evaluated child
    unfold FiniteLatentSCM.eval FiniteLatentSCM.evalUnder at childEq
    rw [FiniteLatentSCM.evalNodeUnder] at childEq
    simp only [FiniteLatentSCM.equationUnder,
      FiniteLatentSCM.noIntervention] at childEq
    change C.responseMechanism child
        (fun parent edge =>
          C.toSCM.evalNodeUnder (FiniteLatentSCM.noIntervention S) seeds parent)
        (seeds child) = assignment child at childEq
    have parentsAgree :
        (fun (parent : Fin S.count)
            (_edge : S.directed parent child = true) =>
          C.toSCM.evalNodeUnder (FiniteLatentSCM.noIntervention S) seeds parent) =
          (fun (parent : Fin S.count)
            (_edge : S.directed parent child = true) => assignment parent) := by
      funext parent edge
      exact congrFun evaluated parent
    rw [parentsAgree] at childEq
    exact childEq
  · intro agreements
    funext child
    exact C.toSCM_evalNode_eq_of_responseSingletons
      seeds assignment agreements child

/-- The preimage of an observed singleton is the corresponding rectangular
event on the independent response-function seeds. -/
theorem observationalSingleton_preimage_eq_rectangular
    (C : FiniteRationalCPT S) (assignment : S.Assignment) :
    (fun seeds =>
      FiniteProbRecord.singletonEvent assignment (C.toSCM.eval seeds)) =
      C.toSCM.latent.rectangularEvent
        (C.responseSingletonEvent assignment) := by
  funext seeds
  rw [LatentExtension.rectangularEvent,
    finiteProduct_rectangular_eq_finAll]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro observed
    have evaluated : C.toSCM.eval seeds = assignment := by
      simpa [FiniteProbRecord.singletonEvent] using observed
    apply (finAll_eq_true_iff _).2
    intro child
    have agreement :=
      (C.toSCM_eval_eq_iff_responseSingletons seeds assignment).1
        evaluated child
    simp [responseSingletonEvent, FiniteProbRecord.singletonEvent, agreement]
  · intro rectangular
    have agreements : forall child,
        C.responseMechanism child (fun parent _ => assignment parent)
          (seeds child) = assignment child := by
      intro child
      have selected := (finAll_eq_true_iff _).1 rectangular child
      simpa [responseSingletonEvent, FiniteProbRecord.singletonEvent] using
        selected
    have evaluated :=
      (C.toSCM_eval_eq_iff_responseSingletons seeds assignment).2 agreements
    simp [FiniteProbRecord.singletonEvent, evaluated]

/--
The observational singleton law of the functionalized SCM is exactly the
Bayesian-network product of the original conditional-table rows.
-/
theorem toSCM_observational_singleton_factorizes
    (C : FiniteRationalCPT S) (assignment : S.Assignment) :
    QProb.Equiv
      (C.toSCM.observationalValue
        (FiniteProbRecord.singletonEvent assignment))
      (FiniteProduct.qProduct S.count (fun child =>
        (C.rowRecord child
          (C.encode child (fun parent _ => assignment parent))).probVal
            (FiniteProbRecord.singletonEvent (assignment child)))) := by
  have mapped := C.toSCM.observationalValue_eq
    (FiniteProbRecord.singletonEvent assignment)
  have reexpressed : QProb.Equiv
      (C.toSCM.prior.probVal (fun seeds =>
        FiniteProbRecord.singletonEvent assignment (C.toSCM.eval seeds)))
      (C.toSCM.prior.probVal
        (C.toSCM.latent.rectangularEvent
          (C.responseSingletonEvent assignment))) :=
    FiniteProbRecord.probVal_congr C.toSCM.prior _ _ (fun seeds =>
      congrFun (C.observationalSingleton_preimage_eq_rectangular assignment)
        seeds)
  have independent := C.toSCM.product_law
    (C.responseSingletonEvent assignment)
  have rows : QProb.Equiv
      (FiniteProduct.qProduct S.count (fun child =>
        (C.toSCM.factor child).probVal
          (C.responseSingletonEvent assignment child)))
      (FiniteProduct.qProduct S.count (fun child =>
        (C.rowRecord child
          (C.encode child (fun parent _ => assignment parent))).probVal
            (FiniteProbRecord.singletonEvent (assignment child)))) := by
    apply FiniteProduct.qProduct_congr
    intro child
    simpa [responseSingletonEvent] using
      C.toSCM_preserves_row child (fun parent _ => assignment parent)
        (FiniteProbRecord.singletonEvent (assignment child))
  exact QProb.equiv_trans mapped
    (QProb.equiv_trans reexpressed
      (QProb.equiv_trans independent rows))

end FiniteRationalCPT

end Causality
end Thesis
