import Thesis.Causality.Graph
import Thesis.Probability

namespace Thesis
namespace Causality

open Probability

/-!
Finite recursive structural causal models with explicit latent roots.

The observed signature fixes the finite observed variables, their possibly
different value types, and the acyclic directed parent graph.  A model adds a
finite family of latent roots, a product probability law for those roots, and
structural mechanisms typed only over declared parent and incident-latent
inputs.  Bidirected edges are derived by hiding shared latent roots.
-/

namespace ObservedSignature

instance assignmentDecidableEq (S : ObservedSignature) :
    DecidableEq S.Assignment :=
  FiniteProduct.assignmentDecidableEq S.count S.Value S.valueDecidableEq

/-- A repetition-free enumeration of all dependent observed assignments. -/
def assignmentEnumeration (S : ObservedSignature) : List S.Assignment :=
  deduplicate
    (FiniteProduct.enumeration S.count S.Value S.valueEnumeration)

theorem assignmentEnumeration_complete (S : ObservedSignature)
    (assignment : S.Assignment) : assignment ∈ S.assignmentEnumeration := by
  rw [assignmentEnumeration, mem_deduplicate]
  exact FiniteProduct.enumeration_complete S.count S.Value S.valueEnumeration
    S.value_complete assignment

theorem assignmentEnumeration_nodup (S : ObservedSignature) :
    S.assignmentEnumeration.Nodup :=
  deduplicate_nodup _

/-- Keep selected coordinates and replace every other coordinate canonically. -/
def project (S : ObservedSignature) (nodes : NodeSet S)
    (assignment : S.Assignment) : S.Assignment :=
  fun i => if nodes i then assignment i else S.defaultValue i

theorem project_idempotent (S : ObservedSignature) (nodes : NodeSet S)
    (assignment : S.Assignment) :
    S.project nodes (S.project nodes assignment) = S.project nodes assignment := by
  funext i
  cases selected : nodes i <;>
    simp [project, selected]

end ObservedSignature

/-- Latent roots and their directed incidence into observed mechanisms. -/
structure LatentExtension.{u, v} (S : ObservedSignature.{u}) where
  count : Nat
  Value : Fin count -> Type v
  valueEnumeration : (l : Fin count) -> List (Value l)
  value_complete : forall l value, value ∈ valueEnumeration l
  valueDecidableEq : (l : Fin count) -> DecidableEq (Value l)
  incident : Fin count -> Fin S.count -> Bool

namespace LatentExtension

instance (L : LatentExtension S) (l : Fin L.count) : DecidableEq (L.Value l) :=
  L.valueDecidableEq l

abbrev Assignment (L : LatentExtension S) :=
  (l : Fin L.count) -> L.Value l

def Inputs (L : LatentExtension S) (child : Fin S.count) :=
  (l : Fin L.count) -> L.incident l child = true -> L.Value l

def rectangularEvent (L : LatentExtension S)
    (events : (l : Fin L.count) -> L.Value l -> Bool)
    (u : L.Assignment) : Bool :=
  FiniteProduct.rectangularEvent L.count L.Value events u

/-- Two observed nodes are confounded exactly when a hidden root feeds both. -/
def projectedBidirected (L : LatentExtension S)
    (i j : Fin S.count) : Bool :=
  !(Nat.beq i.val j.val) &&
    finAny L.count (fun latent => L.incident latent i && L.incident latent j)

theorem projectedBidirected_symmetric (L : LatentExtension S) {i j}
    (h : L.projectedBidirected i j = true) :
    L.projectedBidirected j i = true := by
  have hany :
      finAny L.count (fun latent => L.incident latent i && L.incident latent j) =
        finAny L.count (fun latent => L.incident latent j && L.incident latent i) :=
    finAny_congr (fun latent => Bool.and_comm _ _)
  unfold projectedBidirected at h ⊢
  rw [natBeq_comm j.val i.val, ← hany]
  exact h

theorem projectedBidirected_irreflexive (L : LatentExtension S) (i) :
    L.projectedBidirected i i = false := by
  unfold projectedBidirected
  rw [natBeq_refl]
  rfl

def observedGraph (L : LatentExtension S) : ObservedGraph S where
  bidirected := L.projectedBidirected
  bidirected_symmetric := L.projectedBidirected_symmetric
  bidirected_irreflexive := L.projectedBidirected_irreflexive

/-- Every hidden source is private to at most one observed mechanism. -/
def Markovian (L : LatentExtension S) : Prop :=
  forall l i j,
    L.incident l i = true -> L.incident l j = true -> i = j

/-- Every hidden source has at most two distinct observed children. -/
def CanonicalSemiMarkovian (L : LatentExtension S) : Prop :=
  forall l i j k,
    L.incident l i = true ->
    L.incident l j = true ->
    L.incident l k = true ->
    i = j \/ i = k \/ j = k

theorem markovian_has_no_bidirected (L : LatentExtension S)
    (hMarkov : L.Markovian) (i j : Fin S.count) :
    L.projectedBidirected i j = false := by
  cases edgeEq : L.projectedBidirected i j with
  | false => rfl
  | true =>
      have edge : L.projectedBidirected i j = true := edgeEq
      have hne : i ≠ j := by
        intro equal
        subst j
        simp [projectedBidirected] at edge
      have hany :
          finAny L.count
              (fun latent => L.incident latent i && L.incident latent j) =
            true := by
        exact (Bool.and_eq_true_iff.mp edge).2
      have witness : Exists fun latent : Fin L.count =>
          L.incident latent i = true /\ L.incident latent j = true := by
        rcases (finAny_eq_true_iff _).mp hany with ⟨latent, hlatent⟩
        exact ⟨latent, Bool.and_eq_true_iff.mp hlatent⟩
      rcases witness with ⟨latent, hi, hj⟩
      exact (hne (hMarkov latent i j hi hj)).elim

def expandedEdge (L : LatentExtension S) :=
  Causality.expandedEdge S L.count L.incident

theorem expandedEdge_rank_lt (L : LatentExtension S) {i j}
    (h : L.expandedEdge i j = true) : i.rank < j.rank :=
  Causality.expandedEdge_rank_lt S L.count L.incident h

end LatentExtension

/--
A finite latent-root SCM over a fixed observed signature.

`product_law` is the exact finite independence condition: every rectangular
event in the joint latent assignment has probability equal to the product of
its source-wise probabilities.  Because the sample space is the dependent
product of the source value types, this characterizes the supplied joint
prior as the product of the factors.
-/
structure FiniteLatentSCM.{u, v} (S : ObservedSignature.{u}) where
  latent : LatentExtension.{u, v} S
  factor : (l : Fin latent.count) -> FiniteProbRecord (latent.Value l)
  prior : FiniteProbRecord latent.Assignment
  product_law :
    forall events : (l : Fin latent.count) -> latent.Value l -> Bool,
      QProb.Equiv
        (prior.probVal (latent.rectangularEvent events))
        (FiniteProduct.qProduct latent.count
          (fun l => (factor l).probVal (events l)))
  mechanism :
    (child : Fin S.count) ->
      S.ParentValues child -> latent.Inputs child -> S.Value child

namespace FiniteLatentSCM

def IsMarkovian (M : FiniteLatentSCM S) : Prop := M.latent.Markovian

def IsCanonicalSemiMarkovian (M : FiniteLatentSCM S) : Prop :=
  M.latent.CanonicalSemiMarkovian

theorem markovian_isCanonicalSemiMarkovian (M : FiniteLatentSCM S)
    (markovian : M.IsMarkovian) : M.IsCanonicalSemiMarkovian := by
  intro latent i j k hi hj _hk
  exact Or.inl (markovian latent i j hi hj)

def observedGraph (M : FiniteLatentSCM S) : ObservedGraph S :=
  M.latent.observedGraph

theorem jointPrior_normalizedValue (M : FiniteLatentSCM S) :
    QProb.Equiv (M.prior.probVal topEvent) QProb.one :=
  M.prior.normalization

theorem sourceFactors_normalizedValue (M : FiniteLatentSCM S) (l) :
    QProb.Equiv ((M.factor l).probVal topEvent) QProb.one :=
  (M.factor l).normalization

def noIntervention (S : ObservedSignature) :
    (i : Fin S.count) -> Option (S.Value i) :=
  fun _ => none

def cutOf (S : ObservedSignature)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (i : Fin S.count) : Bool :=
  (target i).isSome

def equationUnder (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (child : Fin S.count) (parents : S.ParentValues child)
    (latents : M.latent.Inputs child) : S.Value child :=
  match target child with
  | some value => value
  | none => M.mechanism child parents latents

/-- Recursive evaluation in the topological order fixed by `S`. -/
def evalPrefixUnder (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment) :
    (k : Nat) -> (hk : k <= S.count) -> S.Prefix k hk
  | 0, _ => fun i => Fin.elim0 i
  | k + 1, hk =>
      let hkPrev : k <= S.count := Nat.le_trans (Nat.le_succ k) hk
      let previous := evalPrefixUnder M target u k hkPrev
      let child : Fin S.count := ⟨k, Nat.lt_of_succ_le hk⟩
      let parents : S.ParentValues child := fun parent hEdge =>
        previous ⟨parent.val, S.directed_earlier hEdge⟩
      let latents : M.latent.Inputs child := fun l _ => u l
      let value := M.equationUnder target child parents latents
      FiniteProduct.extend
        (by simpa [child] using value)
        (fun j => by simpa using previous j)

/-- Direct well-founded evaluation, avoiding extensional prefix equality. -/
def evalNodeUnder (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment) (child : Fin S.count) : S.Value child :=
  M.equationUnder target child
    (fun parent _edge => M.evalNodeUnder target u parent)
    (fun latent _ => u latent)
termination_by child.val
decreasing_by
  exact S.directed_earlier _edge

def evalUnder (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment) : S.Assignment :=
  fun child => M.evalNodeUnder target u child

/-- Prefix recursion and direct well-founded evaluation agree pointwise. -/
theorem evalPrefixUnder_eq_evalNodeUnder (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment) (k : Nat) (hk : k <= S.count) (i : Fin k) :
    M.evalPrefixUnder target u k hk i =
      M.evalNodeUnder target u
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      let hkPrev : k <= S.count := Nat.le_trans (Nat.le_succ k) hk
      let child : Fin S.count := ⟨k, Nat.lt_of_succ_le hk⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [evalPrefixUnder, FiniteProduct.extend_last]
        change
          M.equationUnder target child
              (fun parent hEdge =>
                M.evalPrefixUnder target u k hkPrev
                  ⟨parent.val, S.directed_earlier hEdge⟩)
              (fun latent _ => u latent) =
            M.evalNodeUnder target u child
        rw [evalNodeUnder]
        have parentsAgree :
            (fun (parent : Fin S.count)
                (hEdge : S.directed parent child = true) =>
              M.evalPrefixUnder target u k hkPrev
                ⟨parent.val, S.directed_earlier hEdge⟩) =
            (fun (parent : Fin S.count)
                (_edge : S.directed parent child = true) =>
              M.evalNodeUnder target u parent) := by
          funext parent edge
          exact ih hkPrev ⟨parent.val, S.directed_earlier edge⟩
        rw [parentsAgree]
      · simpa [evalPrefixUnder, hkPrev,
          FiniteProduct.extend_castSucc] using ih hkPrev j

/-- A complete prefix is the assignment produced by direct evaluation. -/
theorem evalPrefixUnder_full_eq_evalUnder (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment) :
    M.evalPrefixUnder target u S.count (Nat.le_refl S.count) =
      M.evalUnder target u := by
  funext i
  simpa [evalUnder] using
    M.evalPrefixUnder_eq_evalNodeUnder target u S.count
      (Nat.le_refl S.count) i

def eval (M : FiniteLatentSCM S) (u : M.latent.Assignment) : S.Assignment :=
  M.evalUnder (noIntervention S) u

/-- With no intervention, interventional evaluation is factual evaluation. -/
theorem evalUnder_noIntervention (M : FiniteLatentSCM S)
    (u : M.latent.Assignment) :
    M.evalUnder (noIntervention S) u = M.eval u :=
  rfl

/-- Effectiveness: an intervened variable takes the selected value. -/
theorem evalUnder_effectiveness (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment) (child : Fin S.count) (value : S.Value child)
    (selected : target child = some value) :
    M.evalUnder target u child = value := by
  unfold evalUnder
  rw [evalNodeUnder]
  simp [equationUnder, selected]

/--
Composition at one node: extending an intervention by values already produced
under the base intervention does not change the resulting potential outcome.
-/
theorem evalNodeUnder_composition (M : FiniteLatentSCM S)
    (base extension : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment)
    (keeps : forall i, extension i = none -> base i = none)
    (agrees : forall i value, extension i = some value ->
      M.evalUnder base u i = value)
    (child : Fin S.count) :
    M.evalNodeUnder extension u child = M.evalNodeUnder base u child := by
  rw [evalNodeUnder, evalNodeUnder]
  unfold equationUnder
  cases selected : extension child with
  | some value =>
      have agreement := agrees child value selected
      unfold evalUnder at agreement
      rw [evalNodeUnder] at agreement
      exact agreement.symm
  | none =>
      have baseNone := keeps child selected
      simp only [baseNone]
      congr 1
      funext parent edge
      exact M.evalNodeUnder_composition base extension u keeps agrees parent
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- Assignment-level composition for a proof-carrying intervention extension. -/
theorem evalUnder_composition (M : FiniteLatentSCM S)
    (base extension : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment)
    (keeps : forall i, extension i = none -> base i = none)
    (agrees : forall i value, extension i = some value ->
      M.evalUnder base u i = value) :
    M.evalUnder extension u = M.evalUnder base u := by
  funext child
  exact M.evalNodeUnder_composition base extension u keeps agrees child

/--
Consistency: setting any variables to their factual values leaves the complete
unit-level observed assignment unchanged.
-/
theorem evalUnder_consistency (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (u : M.latent.Assignment)
    (agrees : forall i value, target i = some value -> M.eval u i = value) :
    M.evalUnder target u = M.eval u := by
  exact M.evalUnder_composition (noIntervention S) target u
    (fun _ _ => rfl) (by
      intro i value selected
      simpa [eval] using agrees i value selected)

def observationalDist (M : FiniteLatentSCM S) :
    FiniteProbRecord S.Assignment :=
  M.prior.map M.eval

def observationalValue (M : FiniteLatentSCM S)
    (event : S.Assignment -> Bool) : QProb :=
  M.observationalDist.probVal event

def interventionalDist (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i)) :
    FiniteProbRecord S.Assignment :=
  M.prior.map (M.evalUnder target)

/-- Interventional pushforward through prefix evaluation is the same record. -/
theorem interventionalDist_eq_prefixPushforward (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i)) :
    M.interventionalDist target =
      M.prior.map (fun u =>
        M.evalPrefixUnder target u S.count (Nat.le_refl S.count)) := by
  unfold interventionalDist
  congr 1
  funext u
  exact (M.evalPrefixUnder_full_eq_evalUnder target u).symm

/-- The observational record is the pushforward through complete prefixes. -/
theorem observationalDist_eq_prefixPushforward (M : FiniteLatentSCM S) :
    M.observationalDist =
      M.prior.map (fun u =>
        M.evalPrefixUnder (noIntervention S) u S.count
          (Nat.le_refl S.count)) := by
  unfold observationalDist eval
  congr 1
  funext u
  exact (M.evalPrefixUnder_full_eq_evalUnder (noIntervention S) u).symm

def interventionalValue (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) : QProb :=
  (M.interventionalDist target).probVal event

theorem observationalValue_eq (M : FiniteLatentSCM S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (M.observationalValue event)
      (M.prior.probVal (fun u => event (M.eval u))) :=
  FiniteProbRecord.map_probVal M.prior M.eval event

theorem interventionalValue_eq (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) :
    QProb.Equiv (M.interventionalValue target event)
      (M.prior.probVal (fun u => event (M.evalUnder target u))) :=
  FiniteProbRecord.map_probVal M.prior (M.evalUnder target) event

def CounterfactualSupported (M : FiniteLatentSCM S)
    (evidence : S.Assignment -> Bool) : Prop :=
  M.observationalDist.EventPositive evidence

def counterfactualValue (M : FiniteLatentSCM S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) : QProb :=
  let posterior := M.prior.conditionOn (fun u => evidence (M.eval u)) (by
    simpa [CounterfactualSupported, observationalDist,
      FiniteProbRecord.EventPositive, FiniteProbRecord.map,
      FiniteProbRecord.eventMass_map_labels] using hEvidence)
  posterior.probVal (fun u => event (M.evalUnder target u))

theorem counterfactualValue_eq (M : FiniteLatentSCM S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : M.CounterfactualSupported evidence)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) :
    QProb.Equiv (M.counterfactualValue evidence hEvidence target event)
      (QProb.div
        (M.prior.probVal
          (fun u => evidence (M.eval u) && event (M.evalUnder target u)))
        (M.prior.probVal (fun u => evidence (M.eval u)))
        (by
          simpa [CounterfactualSupported, observationalDist,
            FiniteProbRecord.EventPositive, FiniteProbRecord.map,
            FiniteProbRecord.eventMass_map_labels] using hEvidence)) := by
  unfold counterfactualValue
  exact M.prior.conditionOn_probVal
    (fun u => evidence (M.eval u))
    (fun u => event (M.evalUnder target u)) _

/-- The observed graph after a hard intervention. -/
def mutilatedSignature (_M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i)) :
    ObservedSignature where
  count := S.count
  Value := S.Value
  valueEnumeration := S.valueEnumeration
  value_complete := S.value_complete
  value_nodup := S.value_nodup
  defaultValue := S.defaultValue
  valueDecidableEq := S.valueDecidableEq
  directed := mutilatedDirected S (cutOf S target)
  directed_earlier := mutilatedDirected_earlier S (cutOf S target)

def mutilatedGraph (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i)) :
    ObservedGraph (M.mutilatedSignature target) where
  bidirected := fun i j =>
    !(cutOf S target i) && !(cutOf S target j) &&
      M.observedGraph.bidirected i j
  bidirected_symmetric := by
    intro i j h
    have parts := Bool.and_eq_true_iff.mp h
    have cuts := Bool.and_eq_true_iff.mp parts.1
    apply Bool.and_eq_true_iff.mpr
    exact ⟨Bool.and_eq_true_iff.mpr ⟨cuts.2, cuts.1⟩,
      M.observedGraph.bidirected_symmetric parts.2⟩
  bidirected_irreflexive := by
    intro i
    simp [M.observedGraph.bidirected_irreflexive i]

theorem do_removes_incoming_directed (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (child : Fin S.count) (value : S.Value child)
    (hTarget : target child = some value) (parent : Fin S.count) :
    (M.mutilatedSignature target).directed parent child = false := by
  simp [mutilatedSignature, mutilatedDirected, cutOf, hTarget]

theorem do_removes_incident_bidirected (M : FiniteLatentSCM S)
    (target : (i : Fin S.count) -> Option (S.Value i))
    (child : Fin S.count) (value : S.Value child)
    (hTarget : target child = some value) (other : Fin S.count) :
    (M.mutilatedGraph target).bidirected child other = false := by
  simp [mutilatedGraph, cutOf, hTarget]

theorem markovian_projection_has_no_bidirected (M : FiniteLatentSCM S)
    (hMarkov : M.IsMarkovian) (i j : Fin S.count) :
    M.observedGraph.bidirected i j = false :=
  M.latent.markovian_has_no_bidirected hMarkov i j

end FiniteLatentSCM

end Causality
end Thesis
