import Thesis.Causality.Modalities
import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
Learning and forgetting for dependent finite causal signatures.

The general transition layer accepts an explicit semantic extension witness;
it does not claim that arbitrary new information preserves identifiability.
The concrete construction appends a terminal variable determined solely by
already observed parents and gives it no latent incidence.  That restricted
construction is conservative for events and interventions on the old nodes.
-/

/-- Data for a terminal observed variable learned conservatively. -/
structure TerminalVariableSpec.{u} (S : ObservedSignature.{u}) where
  Value : Type u
  valueEnumeration : List Value
  value_complete : forall value, value ∈ valueEnumeration
  value_nodup : valueEnumeration.Nodup
  defaultValue : Value
  valueDecidableEq : DecidableEq Value
  parents : NodeSet S
  mechanism :
    ((parent : Fin S.count) -> parents parent = true -> S.Value parent) -> Value

namespace TerminalVariableSpec

instance (spec : TerminalVariableSpec S) : DecidableEq spec.Value :=
  spec.valueDecidableEq

/--
Constructive elimination of `Fin (n + 1)` into its terminal point or an old
point. The library's `Fin.lastCases_castSucc` reduction theorem currently
inherits `Classical.choice`; this local eliminator keeps the learning bridge
inside the project's constructive-extensional axiom boundary.
-/
def terminalCases {n : Nat} {motive : Fin (n + 1) -> Sort u}
    (lastCase : motive (Fin.last n))
    (oldCase : (i : Fin n) -> motive i.castSucc)
    (i : Fin (n + 1)) : motive i :=
  if hLast : i = Fin.last n then
    cast (congrArg motive hLast.symm) lastCase
  else
    let old : Fin n :=
      ⟨i.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt)
        (fun valueEq => hLast (Fin.ext valueEq))⟩
    have oldEq : old.castSucc = i := Fin.ext (by rfl)
    cast (congrArg motive oldEq) (oldCase old)

@[simp] theorem terminalCases_last {n : Nat}
    {motive : Fin (n + 1) -> Sort u}
    (lastCase : motive (Fin.last n))
    (oldCase : (i : Fin n) -> motive i.castSucc) :
    terminalCases lastCase oldCase (Fin.last n) = lastCase := by
  simp [terminalCases]

@[simp] theorem terminalCases_castSucc {n : Nat}
    {motive : Fin (n + 1) -> Sort u}
    (lastCase : motive (Fin.last n))
    (oldCase : (i : Fin n) -> motive i.castSucc) (i : Fin n) :
    terminalCases lastCase oldCase i.castSucc = oldCase i := by
  have hNotLast : Not (i.castSucc = Fin.last n) := by
    intro equal
    have valueEqual := congrArg Fin.val equal
    exact (Nat.ne_of_lt i.isLt) valueEqual
  simp [terminalCases, hNotLast]

@[simp] theorem cast_symm_cast {A B : Sort u} (equal : A = B) (value : B) :
    cast equal (cast equal.symm value) = value := by
  cases equal
  rfl

/-- The old nodes embed as the initial segment of the extended signature. -/
def oldNode (_spec : TerminalVariableSpec S) (i : Fin S.count) :
    Fin (S.count + 1) :=
  i.castSucc

/-- The learned variable is terminal in the chosen topological order. -/
def newNode (_spec : TerminalVariableSpec S) : Fin (S.count + 1) :=
  Fin.last S.count

/-- The finite data carried by one coordinate of an observed signature. -/
structure FiniteValueData where
  Value : Type u
  enumeration : List Value
  complete : forall value, value ∈ enumeration
  nodup : enumeration.Nodup
  defaultValue : Value
  valueDecidableEq : DecidableEq Value

def extendedData (spec : TerminalVariableSpec S) :
    Fin (S.count + 1) -> FiniteValueData :=
  terminalCases (motive := fun _ => FiniteValueData)
    { Value := spec.Value
      enumeration := spec.valueEnumeration
      complete := spec.value_complete
      nodup := spec.value_nodup
      defaultValue := spec.defaultValue
      valueDecidableEq := spec.valueDecidableEq }
    (fun i =>
      { Value := S.Value i
        enumeration := S.valueEnumeration i
        complete := S.value_complete i
        nodup := S.value_nodup i
        defaultValue := S.defaultValue i
        valueDecidableEq := S.valueDecidableEq i })

def extendedValue (spec : TerminalVariableSpec S) :
    Fin (S.count + 1) -> Type u :=
  fun i => (spec.extendedData i).Value

def extendedEnumeration (spec : TerminalVariableSpec S) :
    (i : Fin (S.count + 1)) -> List (spec.extendedValue i) :=
  fun i => (spec.extendedData i).enumeration

def extendedDefault (spec : TerminalVariableSpec S) :
    (i : Fin (S.count + 1)) -> spec.extendedValue i :=
  fun i => (spec.extendedData i).defaultValue

def extendedDecidableEq (spec : TerminalVariableSpec S) :
    (i : Fin (S.count + 1)) -> DecidableEq (spec.extendedValue i) :=
  fun i => (spec.extendedData i).valueDecidableEq

/-- Old directed edges are retained; only old nodes may feed the new sink. -/
def extendedDirected (spec : TerminalVariableSpec S) :
    Fin (S.count + 1) -> Fin (S.count + 1) -> Bool :=
  fun parent child =>
    terminalCases (motive := fun _ => Bool)
      (terminalCases (motive := fun _ => Bool) false
        (fun oldParent => spec.parents oldParent) parent)
      (fun oldChild =>
        terminalCases (motive := fun _ => Bool) false
          (fun oldParent => S.directed oldParent oldChild) parent)
      child

theorem extendedDirected_earlier (spec : TerminalVariableSpec S)
    {parent child : Fin (S.count + 1)}
    (edge : spec.extendedDirected parent child = true) :
    parent.val < child.val := by
  refine terminalCases (motive := fun child =>
      spec.extendedDirected parent child = true ->
        parent.val < child.val) ?_ (fun oldChild => ?_) child edge
  · refine terminalCases (motive := fun parent =>
        spec.extendedDirected parent (Fin.last S.count) = true ->
          parent.val < (Fin.last S.count).val) ?_
        (fun oldParent _ => oldParent.isLt) parent
    simp [extendedDirected]
  · refine terminalCases (motive := fun parent =>
        spec.extendedDirected parent oldChild.castSucc = true ->
          parent.val < oldChild.castSucc.val) ?_ (fun oldParent edge => ?_) parent
    · simp [extendedDirected]
    · exact S.directed_earlier (by simpa [extendedDirected] using edge)

/-- The dependent observed signature after learning the terminal variable. -/
def extendSignature (spec : TerminalVariableSpec S) : ObservedSignature where
  count := S.count + 1
  Value := spec.extendedValue
  valueEnumeration := spec.extendedEnumeration
  value_complete := by
    intro i
    exact (spec.extendedData i).complete
  value_nodup := by
    intro i
    exact (spec.extendedData i).nodup
  defaultValue := spec.extendedDefault
  valueDecidableEq := spec.extendedDecidableEq
  directed := spec.extendedDirected
  directed_earlier := spec.extendedDirected_earlier

@[simp] theorem extendSignature_count (spec : TerminalVariableSpec S) :
    spec.extendSignature.count = S.count + 1 :=
  rfl

@[simp] theorem value_oldNode (spec : TerminalVariableSpec S)
    (i : Fin S.count) :
    spec.extendSignature.Value i.castSucc = S.Value i :=
  by simp [extendSignature, extendedValue, extendedData]

@[simp] theorem value_newNode (spec : TerminalVariableSpec S) :
    spec.extendSignature.Value (Fin.last S.count) = spec.Value :=
  by simp [extendSignature, extendedValue, extendedData]

@[simp] theorem directed_old_old (spec : TerminalVariableSpec S)
    (parent child : Fin S.count) :
    spec.extendSignature.directed parent.castSucc child.castSucc =
      S.directed parent child := by
  simp [extendSignature, extendedDirected]

@[simp] theorem directed_old_new (spec : TerminalVariableSpec S)
    (parent : Fin S.count) :
    spec.extendSignature.directed parent.castSucc (Fin.last S.count) =
      spec.parents parent := by
  simp [extendSignature, extendedDirected]

@[simp] theorem directed_new_old (spec : TerminalVariableSpec S)
    (child : Fin S.count) :
    spec.extendSignature.directed (Fin.last S.count) child.castSucc = false := by
  simp [extendSignature, extendedDirected]

@[simp] theorem directed_new_new (spec : TerminalVariableSpec S) :
    spec.extendSignature.directed (Fin.last S.count) (Fin.last S.count) = false := by
  simp [extendSignature, extendedDirected]

/-- Restrict an extended assignment to the old observed coordinates. -/
def restrictAssignment (spec : TerminalVariableSpec S)
    (assignment : spec.extendSignature.Assignment) : S.Assignment :=
  fun i => cast (spec.value_oldNode i) (assignment i.castSucc)

/-- Extend an old assignment by a value for the learned coordinate. -/
def extendAssignment (spec : TerminalVariableSpec S)
    (assignment : S.Assignment) (value : spec.Value) :
    spec.extendSignature.Assignment :=
  FiniteProduct.extend
    (cast spec.value_newNode.symm value)
    (fun i => cast (spec.value_oldNode i).symm (assignment i))

@[simp] theorem restrict_extendAssignment (spec : TerminalVariableSpec S)
    (assignment : S.Assignment) (value : spec.Value) (i : Fin S.count) :
    spec.restrictAssignment (spec.extendAssignment assignment value) i =
      assignment i := by
  simp [restrictAssignment, extendAssignment]

/-- Lift a decidable old-node set while leaving the learned node unselected. -/
def liftNodeSet (spec : TerminalVariableSpec S) (nodes : NodeSet S) :
    NodeSet spec.extendSignature :=
  terminalCases (motive := fun _ => Bool) false nodes

@[simp] theorem liftNodeSet_old (spec : TerminalVariableSpec S)
    (nodes : NodeSet S) (i : Fin S.count) :
    spec.liftNodeSet nodes i.castSucc = nodes i := by
  simp [liftNodeSet]

@[simp] theorem liftNodeSet_new (spec : TerminalVariableSpec S)
    (nodes : NodeSet S) :
    spec.liftNodeSet nodes (Fin.last S.count) = false := by
  simp [liftNodeSet]

/-- Lift an intervention without setting the learned coordinate. -/
def liftIntervention (spec : TerminalVariableSpec S)
    (intervention : HardIntervention S) :
    HardIntervention spec.extendSignature where
  value := fun i =>
    terminalCases (motive := fun i => Option (spec.extendSignature.Value i)) none
      (fun old => Option.map (cast (spec.value_oldNode old).symm)
        (intervention.value old)) i

@[simp] theorem liftIntervention_old (spec : TerminalVariableSpec S)
    (intervention : HardIntervention S) (i : Fin S.count) :
    Option.map (cast (spec.value_oldNode i))
        ((spec.liftIntervention intervention).value i.castSucc) =
      intervention.value i := by
  cases hValue : intervention.value i with
  | none => simp [liftIntervention, hValue]
  | some value => simp [liftIntervention, hValue]

@[simp] theorem liftIntervention_new (spec : TerminalVariableSpec S)
    (intervention : HardIntervention S) :
    (spec.liftIntervention intervention).value (Fin.last S.count) = none := by
  simp [liftIntervention]

/-- Restrict an arbitrary extended intervention to the old coordinates. -/
def restrictIntervention (spec : TerminalVariableSpec S)
    (intervention : HardIntervention spec.extendSignature) :
    HardIntervention S where
  value := fun i => Option.map (cast (spec.value_oldNode i))
    (intervention.value i.castSucc)

@[simp] theorem restrict_liftIntervention (spec : TerminalVariableSpec S)
    (intervention : HardIntervention S) (i : Fin S.count) :
    (spec.restrictIntervention (spec.liftIntervention intervention)).value i =
      intervention.value i :=
  spec.liftIntervention_old intervention i

/-- Lift an old event by ignoring the learned coordinate. -/
def liftEvent (spec : TerminalVariableSpec S)
    (event : S.Assignment -> Bool) :
    spec.extendSignature.Assignment -> Bool :=
  fun assignment => event (spec.restrictAssignment assignment)

/-- Reuse all latent sources and leave the learned sink latently unconnected. -/
def extendLatent (spec : TerminalVariableSpec S) (L : LatentExtension S) :
    LatentExtension spec.extendSignature where
  count := L.count
  Value := L.Value
  valueEnumeration := L.valueEnumeration
  value_complete := L.value_complete
  valueDecidableEq := L.valueDecidableEq
  incident := fun latent child =>
    terminalCases (motive := fun _ => Bool) false
      (fun old => L.incident latent old) child

@[simp] theorem extendLatent_count (spec : TerminalVariableSpec S)
    (L : LatentExtension S) :
    (spec.extendLatent L).count = L.count :=
  rfl

@[simp] theorem extendLatent_value (spec : TerminalVariableSpec S)
    (L : LatentExtension S) (latent : Fin L.count) :
    (spec.extendLatent L).Value latent = L.Value latent :=
  rfl

@[simp] theorem extendLatent_incident_old (spec : TerminalVariableSpec S)
    (L : LatentExtension S) (latent : Fin L.count) (child : Fin S.count) :
    (spec.extendLatent L).incident latent child.castSucc =
      L.incident latent child := by
  simp [extendLatent]

@[simp] theorem extendLatent_incident_new (spec : TerminalVariableSpec S)
    (L : LatentExtension S) (latent : Fin L.count) :
    (spec.extendLatent L).incident latent (Fin.last S.count) = false := by
  simp [extendLatent]

theorem extendLatent_projectedBidirected_old
    (spec : TerminalVariableSpec S) (L : LatentExtension S)
    (i j : Fin S.count) :
    (spec.extendLatent L).projectedBidirected i.castSucc j.castSucc =
      L.projectedBidirected i j := by
  simp [LatentExtension.projectedBidirected, extendLatent]

theorem extendLatent_projectedBidirected_new_left
    (spec : TerminalVariableSpec S) (L : LatentExtension S)
    (i : Fin (S.count + 1)) :
    (spec.extendLatent L).projectedBidirected (Fin.last S.count) i = false := by
  simp [LatentExtension.projectedBidirected, extendLatent, finAny_eq_false_iff]

theorem extendLatent_projectedBidirected_new_right
    (spec : TerminalVariableSpec S) (L : LatentExtension S)
    (i : Fin (S.count + 1)) :
    (spec.extendLatent L).projectedBidirected i (Fin.last S.count) = false := by
  simp [LatentExtension.projectedBidirected, extendLatent, finAny_eq_false_iff]

def extendedBidirected (_spec : TerminalVariableSpec S) (G : ObservedGraph S) :
    Fin (S.count + 1) -> Fin (S.count + 1) -> Bool :=
  fun i j =>
    terminalCases (motive := fun _ => Bool) false
      (fun oldI => terminalCases (motive := fun _ => Bool) false
        (fun oldJ => G.bidirected oldI oldJ) j) i

/-- Extend an ADMG by the learned directed sink and no new bidirected edge. -/
def extendObservedGraph (spec : TerminalVariableSpec S)
    (G : ObservedGraph S) : ObservedGraph spec.extendSignature where
  bidirected := spec.extendedBidirected G
  bidirected_symmetric := by
    intro i j
    refine terminalCases (motive := fun i =>
        spec.extendedBidirected G i j = true ->
          spec.extendedBidirected G j i = true) ?_ (fun oldI edge => ?_) i
    · simp [extendedBidirected]
    · refine terminalCases (motive := fun j =>
        spec.extendedBidirected G oldI.castSucc j = true ->
            spec.extendedBidirected G j oldI.castSucc = true) ?_
        (fun oldJ oldEdge => ?_) j edge
      · simp [extendedBidirected]
      · simpa [extendedBidirected] using
          G.bidirected_symmetric (by simpa [extendedBidirected] using oldEdge)
  bidirected_irreflexive := by
    intro i
    refine terminalCases (motive := fun i =>
      spec.extendedBidirected G i i = false) ?_ (fun old => ?_) i
    · simp [extendedBidirected]
    · simpa [extendedBidirected] using G.bidirected_irreflexive old

@[simp] theorem extendObservedGraph_old
    (spec : TerminalVariableSpec S) (G : ObservedGraph S)
    (i j : Fin S.count) :
    (spec.extendObservedGraph G).bidirected i.castSucc j.castSucc =
      G.bidirected i j := by
  simp [extendObservedGraph, extendedBidirected]

@[simp] theorem extendObservedGraph_new_left
    (spec : TerminalVariableSpec S) (G : ObservedGraph S)
    (i : Fin (S.count + 1)) :
    (spec.extendObservedGraph G).bidirected (Fin.last S.count) i = false := by
  simp [extendObservedGraph, extendedBidirected]

@[simp] theorem extendObservedGraph_new_right
    (spec : TerminalVariableSpec S) (G : ObservedGraph S)
    (i : Fin (S.count + 1)) :
    (spec.extendObservedGraph G).bidirected i (Fin.last S.count) = false := by
  refine terminalCases (motive := fun i =>
      (spec.extendObservedGraph G).bidirected i (Fin.last S.count) = false)
    ?_ (fun old => ?_) i <;>
    simp [extendObservedGraph, extendedBidirected]

theorem extendLatent_incident_true_is_old
    (spec : TerminalVariableSpec S) (L : LatentExtension S)
    (latent : Fin L.count) (child : Fin (S.count + 1))
    (incident : (spec.extendLatent L).incident latent child = true) :
    Exists fun old : Fin S.count =>
      child = old.castSucc ∧ L.incident latent old = true := by
  refine terminalCases (motive := fun child =>
      (spec.extendLatent L).incident latent child = true ->
      Exists fun old : Fin S.count =>
        child = old.castSucc ∧ L.incident latent old = true) ?_
    (fun old oldIncident => ?_) child incident
  · simp [extendLatent]
  · exact ⟨old, rfl, by simpa [extendLatent] using oldIncident⟩

theorem extendLatent_canonical (spec : TerminalVariableSpec S)
    (L : LatentExtension S) (canonical : L.CanonicalSemiMarkovian) :
    (spec.extendLatent L).CanonicalSemiMarkovian := by
  intro latent i j k hi hj hk
  rcases spec.extendLatent_incident_true_is_old L latent i hi with
    ⟨oldI, rfl, oldHi⟩
  rcases spec.extendLatent_incident_true_is_old L latent j hj with
    ⟨oldJ, rfl, oldHj⟩
  rcases spec.extendLatent_incident_true_is_old L latent k hk with
    ⟨oldK, rfl, oldHk⟩
  rcases canonical latent oldI oldJ oldK oldHi oldHj oldHk with
    same | same | same
  · exact Or.inl (congrArg Fin.castSucc same)
  · exact Or.inr (Or.inl (congrArg Fin.castSucc same))
  · exact Or.inr (Or.inr (congrArg Fin.castSucc same))

def oldParentValues (spec : TerminalVariableSpec S) {child : Fin S.count}
    (parents : spec.extendSignature.ParentValues child.castSucc) :
    S.ParentValues child :=
  fun parent edge =>
    cast (spec.value_oldNode parent)
      (parents parent.castSucc (by simpa using edge))

def oldLatentInputs (spec : TerminalVariableSpec S) (L : LatentExtension S)
    {child : Fin S.count}
    (latents : (spec.extendLatent L).Inputs child.castSucc) :
    L.Inputs child :=
  fun latent incident => latents latent (by simpa using incident)

def learnedParentValues (spec : TerminalVariableSpec S)
    (parents : spec.extendSignature.ParentValues (Fin.last S.count)) :
    (parent : Fin S.count) -> spec.parents parent = true -> S.Value parent :=
  fun parent edge =>
    cast (spec.value_oldNode parent)
      (parents parent.castSucc (by simpa using edge))

/-- The old equations are reused; the terminal equation uses only old parents. -/
def extendMechanism (spec : TerminalVariableSpec S) (M : ExactModel S) :
    (child : Fin spec.extendSignature.count) ->
      spec.extendSignature.ParentValues child ->
      (spec.extendLatent M.latent).Inputs child ->
      spec.extendSignature.Value child :=
  fun child =>
    terminalCases (motive := fun child =>
      spec.extendSignature.ParentValues child ->
      (spec.extendLatent M.latent).Inputs child ->
      spec.extendSignature.Value child)
      (fun parents _latents =>
        cast spec.value_newNode.symm
          (spec.mechanism (spec.learnedParentValues parents)))
      (fun old parents latents =>
        cast (spec.value_oldNode old).symm
          (M.mechanism old (spec.oldParentValues parents)
            (spec.oldLatentInputs M.latent latents)))
      child

/-- Append the terminal observed variable to an exact finite SCM. -/
def extendModel (spec : TerminalVariableSpec S) (M : ExactModel S) :
    ExactModel spec.extendSignature where
  latent := spec.extendLatent M.latent
  factor := M.factor
  prior := M.prior
  product_law := M.product_law
  mechanism := spec.extendMechanism M

@[simp] theorem extendModel_prior (spec : TerminalVariableSpec S)
    (M : ExactModel S) :
    (spec.extendModel M).prior = M.prior :=
  rfl

@[simp] theorem extendModel_observedGraph_old
    (spec : TerminalVariableSpec S) (M : ExactModel S)
    (i j : Fin S.count) :
    (spec.extendModel M).observedGraph.bidirected i.castSucc j.castSucc =
      M.observedGraph.bidirected i j :=
  spec.extendLatent_projectedBidirected_old M.latent i j

theorem extendModel_isCanonicalSemiMarkovian
    (spec : TerminalVariableSpec S) (M : ExactModel S)
    (canonical : M.IsCanonicalSemiMarkovian) :
    (spec.extendModel M).IsCanonicalSemiMarkovian :=
  spec.extendLatent_canonical M.latent canonical

/-- Drop the learned coordinate from an arbitrary latent extension. -/
def restrictLatent (spec : TerminalVariableSpec S)
    (L : LatentExtension spec.extendSignature) : LatentExtension S where
  count := L.count
  Value := L.Value
  valueEnumeration := L.valueEnumeration
  value_complete := L.value_complete
  valueDecidableEq := L.valueDecidableEq
  incident := fun latent child => L.incident latent child.castSucc

def extendedOldParentValues (spec : TerminalVariableSpec S)
    {child : Fin S.count} (parents : S.ParentValues child) :
    spec.extendSignature.ParentValues child.castSucc :=
  fun parent =>
    terminalCases (motive := fun parent =>
      spec.extendSignature.directed parent child.castSucc = true ->
      spec.extendSignature.Value parent)
      (fun edge => by simp at edge)
      (fun old edge =>
        cast (spec.value_oldNode old).symm
          (parents old (by simpa using edge)))
      parent

theorem extendedOldParentValues_old (spec : TerminalVariableSpec S)
    {child : Fin S.count} (parents : S.ParentValues child)
    (old : Fin S.count)
    (edge : spec.extendSignature.directed old.castSucc child.castSucc = true) :
    spec.extendedOldParentValues parents old.castSucc edge =
      cast (spec.value_oldNode old).symm
        (parents old (by simpa using edge)) := by
  let lastCase :
      spec.extendSignature.directed (Fin.last S.count) child.castSucc = true ->
        spec.extendSignature.Value (Fin.last S.count) :=
    fun impossible => by simp at impossible
  let oldCase : (parent : Fin S.count) ->
      spec.extendSignature.directed parent.castSucc child.castSucc = true ->
        spec.extendSignature.Value parent.castSucc :=
    fun parent parentEdge =>
      cast (spec.value_oldNode parent).symm
        (parents parent (by simpa using parentEdge))
  change (terminalCases (motive := fun parent =>
      spec.extendSignature.directed parent child.castSucc = true ->
        spec.extendSignature.Value parent)
    lastCase oldCase old.castSucc) edge = oldCase old edge
  have reduction :
      terminalCases (motive := fun parent =>
        spec.extendSignature.directed parent child.castSucc = true ->
          spec.extendSignature.Value parent)
        lastCase oldCase old.castSucc = oldCase old :=
    @terminalCases_castSucc S.count
      (fun parent =>
        spec.extendSignature.directed parent child.castSucc = true ->
          spec.extendSignature.Value parent)
      lastCase oldCase old
  exact congrFun reduction edge

def extendedOldLatentInputs (spec : TerminalVariableSpec S)
    (L : LatentExtension spec.extendSignature) {child : Fin S.count}
    (latents : (spec.restrictLatent L).Inputs child) :
    L.Inputs child.castSucc :=
  fun latent incident => latents latent (by simpa [restrictLatent] using incident)

/-- Restrict an arbitrary model on the learned signature to its old subsystem. -/
def restrictModel (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) : ExactModel S where
  latent := spec.restrictLatent N.latent
  factor := N.factor
  prior := N.prior
  product_law := N.product_law
  mechanism := fun child parents latents =>
    cast (spec.value_oldNode child)
      (N.mechanism child.castSucc
        (spec.extendedOldParentValues parents)
        (spec.extendedOldLatentInputs N.latent latents))

@[simp] theorem restrictModel_prior (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) :
    (spec.restrictModel N).prior = N.prior :=
  rfl

@[simp] theorem restrictModel_observedGraph
    (spec : TerminalVariableSpec S) (N : ExactModel spec.extendSignature)
    (i j : Fin S.count) :
    (spec.restrictModel N).observedGraph.bidirected i j =
      N.observedGraph.bidirected i.castSucc j.castSucc := by
  simp [restrictModel, restrictLatent, FiniteLatentSCM.observedGraph,
    LatentExtension.observedGraph, LatentExtension.projectedBidirected]

theorem restrictModel_isCanonicalSemiMarkovian
    (spec : TerminalVariableSpec S) (N : ExactModel spec.extendSignature)
    (canonical : N.IsCanonicalSemiMarkovian) :
    (spec.restrictModel N).IsCanonicalSemiMarkovian := by
  intro latent i j k hi hj hk
  rcases canonical latent i.castSucc j.castSucc k.castSucc
      (by simpa [restrictModel, restrictLatent] using hi)
      (by simpa [restrictModel, restrictLatent] using hj)
      (by simpa [restrictModel, restrictLatent] using hk) with
    same | same | same
  · exact Or.inl (Fin.castSucc_inj.mp same)
  · exact Or.inr (Or.inl (Fin.castSucc_inj.mp same))
  · exact Or.inr (Or.inr (Fin.castSucc_inj.mp same))

theorem extendModel_compatible (spec : TerminalVariableSpec S)
    (M : ExactModel S) (G : ObservedGraph S)
    (compatible : Compatible M G) :
    Compatible (spec.extendModel M) (spec.extendObservedGraph G) := by
  constructor
  · exact spec.extendModel_isCanonicalSemiMarkovian M compatible.1
  · intro i j
    refine terminalCases (motive := fun i =>
        (spec.extendModel M).observedGraph.bidirected i j =
          (spec.extendObservedGraph G).bidirected i j) ?_
      (fun oldI => ?_) i
    · simpa [FiniteLatentSCM.observedGraph, extendModel,
        LatentExtension.observedGraph] using
        spec.extendLatent_projectedBidirected_new_left M.latent j
    · refine terminalCases (motive := fun j =>
          (spec.extendModel M).observedGraph.bidirected oldI.castSucc j =
            (spec.extendObservedGraph G).bidirected oldI.castSucc j) ?_
        (fun oldJ => ?_) j
      · simpa [FiniteLatentSCM.observedGraph, extendModel,
          LatentExtension.observedGraph] using
          spec.extendLatent_projectedBidirected_new_right M.latent oldI.castSucc
      · exact Eq.trans (spec.extendModel_observedGraph_old M oldI oldJ)
          (Eq.trans (compatible.2 oldI oldJ)
            (spec.extendObservedGraph_old G oldI oldJ).symm)

theorem restrictModel_compatible (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (G : ObservedGraph S)
    (compatible : Compatible N (spec.extendObservedGraph G)) :
    Compatible (spec.restrictModel N) G := by
  constructor
  · exact spec.restrictModel_isCanonicalSemiMarkovian N compatible.1
  · intro i j
    exact Eq.trans (spec.restrictModel_observedGraph N i j)
      (Eq.trans (compatible.2 i.castSucc j.castSucc)
        (spec.extendObservedGraph_old G i j))

/-- Old structural equations evaluate identically after terminal learning. -/
theorem extendModel_evalNodeUnder_old (spec : TerminalVariableSpec S)
    (M : ExactModel S) (intervention : HardIntervention S)
    (u : M.latent.Assignment) (child : Fin S.count) :
    cast (spec.value_oldNode child)
        ((spec.extendModel M).evalNodeUnder
          (spec.liftIntervention intervention).value u child.castSucc) =
      M.evalNodeUnder intervention.value u child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : intervention.value child with
  | some value =>
      simp [liftIntervention, selected]
  | none =>
      simp [liftIntervention, selected, extendModel, extendMechanism]
      apply congrArg (fun parents =>
        M.mechanism child parents (fun latent _ => u latent))
      funext parent edge
      exact spec.extendModel_evalNodeUnder_old M intervention u parent
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- Restriction preserves every old recursive equation of an arbitrary model. -/
theorem restrictModel_evalNodeUnder (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature)
    (intervention : HardIntervention spec.extendSignature)
    (u : N.latent.Assignment) (child : Fin S.count) :
    cast (spec.value_oldNode child)
        (N.evalNodeUnder intervention.value u child.castSucc) =
      (spec.restrictModel N).evalNodeUnder
        (spec.restrictIntervention intervention).value u child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : intervention.value child.castSucc with
  | some value =>
      simp [restrictIntervention, selected]
  | none =>
      simp [restrictIntervention, selected, restrictModel]
      apply congrArg (fun parents =>
        cast (spec.value_oldNode child)
          (N.mechanism child.castSucc parents (fun latent _ => u latent)))
      funext parent edge
      refine terminalCases (motive := fun parent =>
          forall edge : spec.extendSignature.directed parent child.castSucc = true,
            N.evalNodeUnder intervention.value u parent =
              spec.extendedOldParentValues
                (fun oldParent _ =>
                  (spec.restrictModel N).evalNodeUnder
                    (spec.restrictIntervention intervention).value u oldParent)
                parent edge) ?_ (fun old edge => ?_) parent edge
      · intro impossible
        simp at impossible
      · rw [spec.extendedOldParentValues_old]
        let equal := spec.value_oldNode old
        let oldValue := N.evalNodeUnder intervention.value u old.castSucc
        calc
          oldValue = cast equal.symm (cast equal oldValue) :=
            (cast_symm_cast equal.symm oldValue).symm
          _ = cast equal.symm
              ((spec.restrictModel N).evalNodeUnder
                (spec.restrictIntervention intervention).value u old) :=
            congrArg (cast equal.symm)
              (spec.restrictModel_evalNodeUnder N intervention u old)
termination_by child.val
decreasing_by
  exact S.directed_earlier (by simpa using edge)

theorem restrictModel_evalUnder_restrict (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature)
    (intervention : HardIntervention spec.extendSignature)
    (u : N.latent.Assignment) :
    spec.restrictAssignment (N.evalUnder intervention.value u) =
      (spec.restrictModel N).evalUnder
        (spec.restrictIntervention intervention).value u := by
  funext child
  exact spec.restrictModel_evalNodeUnder N intervention u child

theorem restrictModel_liftEvent_evalUnder (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature)
    (intervention : HardIntervention spec.extendSignature)
    (event : S.Assignment -> Bool) (u : N.latent.Assignment) :
    spec.liftEvent event (N.evalUnder intervention.value u) =
      event ((spec.restrictModel N).evalUnder
        (spec.restrictIntervention intervention).value u) := by
  simp [liftEvent, spec.restrictModel_evalUnder_restrict N intervention u]

theorem restrictModel_interventionalValue_old
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature)
    (intervention : HardIntervention spec.extendSignature)
    (event : S.Assignment -> Bool) :
    QProb.Equiv
      (N.interventionalValue intervention.value (spec.liftEvent event))
      ((spec.restrictModel N).interventionalValue
        (spec.restrictIntervention intervention).value event) := by
  exact QProb.equiv_trans
    (N.interventionalValue_eq intervention.value (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr N.prior _ _
        (fun u => spec.restrictModel_liftEvent_evalUnder N intervention event u))
      (QProb.equiv_symm
        ((spec.restrictModel N).interventionalValue_eq
          (spec.restrictIntervention intervention).value event)))

theorem restrict_empty_intervention (spec : TerminalVariableSpec S) :
    (spec.restrictIntervention
      (HardIntervention.empty spec.extendSignature)).value =
      FiniteLatentSCM.noIntervention S := by
  funext child
  simp [restrictIntervention, HardIntervention.empty,
    FiniteLatentSCM.noIntervention]

theorem restrictModel_eval_restrict (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (u : N.latent.Assignment) :
    spec.restrictAssignment (N.eval u) = (spec.restrictModel N).eval u := by
  have preserved := spec.restrictModel_evalUnder_restrict N
    (HardIntervention.empty spec.extendSignature) u
  rw [spec.restrict_empty_intervention] at preserved
  simpa [FiniteLatentSCM.eval, HardIntervention.empty] using preserved

theorem restrictModel_liftEvent_eval (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature)
    (event : S.Assignment -> Bool) (u : N.latent.Assignment) :
    spec.liftEvent event (N.eval u) = event ((spec.restrictModel N).eval u) := by
  simp [liftEvent, spec.restrictModel_eval_restrict N u]

theorem restrictModel_observationalValue_old
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (event : S.Assignment -> Bool) :
    QProb.Equiv
      (N.observationalValue (spec.liftEvent event))
      ((spec.restrictModel N).observationalValue event) := by
  exact QProb.equiv_trans
    (N.observationalValue_eq (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr N.prior _ _
        (fun u => spec.restrictModel_liftEvent_eval N event u))
      (QProb.equiv_symm
        ((spec.restrictModel N).observationalValue_eq event)))

theorem liftNodeSet_disjoint (spec : TerminalVariableSpec S)
    {left right : NodeSet S} (disjoint : NodeSet.Disjoint left right) :
    NodeSet.Disjoint (spec.liftNodeSet left) (spec.liftNodeSet right) := by
  intro i leftSelected
  refine terminalCases (motive := fun i =>
      spec.liftNodeSet left i = true -> spec.liftNodeSet right i = false) ?_
    (fun old selected => ?_) i leftSelected
  · simp
  · simpa using disjoint old (by simpa using selected)

def liftKernel (spec : TerminalVariableSpec S) (kernel : Kernel S) :
    Kernel spec.extendSignature where
  outcome := spec.liftNodeSet kernel.outcome
  action := spec.liftNodeSet kernel.action
  condition := spec.liftNodeSet kernel.condition

def liftJointQuery (spec : TerminalVariableSpec S) (query : JointKernelQuery S) :
    JointKernelQuery spec.extendSignature where
  outcome := spec.liftNodeSet query.outcome
  action := spec.liftNodeSet query.action
  action_outcome_disjoint :=
    spec.liftNodeSet_disjoint query.action_outcome_disjoint

def liftConditionalQuery (spec : TerminalVariableSpec S)
    (query : ConditionalKernelQuery S) :
    ConditionalKernelQuery spec.extendSignature where
  outcome := spec.liftNodeSet query.outcome
  action := spec.liftNodeSet query.action
  condition := spec.liftNodeSet query.condition
  action_outcome_disjoint :=
    spec.liftNodeSet_disjoint query.action_outcome_disjoint
  action_condition_disjoint :=
    spec.liftNodeSet_disjoint query.action_condition_disjoint
  outcome_condition_disjoint :=
    spec.liftNodeSet_disjoint query.outcome_condition_disjoint

theorem liftNodeSet_finAny (spec : TerminalVariableSpec S)
    (nodes : NodeSet S) :
    finAny spec.extendSignature.count (spec.liftNodeSet nodes) =
      finAny S.count nodes := by
  simp [extendSignature, finAny, liftNodeSet]

theorem liftKernel_hasAction (spec : TerminalVariableSpec S)
    (kernel : Kernel S) :
    (spec.liftKernel kernel).hasAction = kernel.hasAction := by
  exact spec.liftNodeSet_finAny kernel.action

theorem liftKernel_intervention (spec : TerminalVariableSpec S)
    (kernel : Kernel S) (reference : spec.extendSignature.Assignment) :
    (spec.liftKernel kernel).intervention reference =
      (spec.liftIntervention
        { value := kernel.intervention (spec.restrictAssignment reference) }).value := by
  funext i
  refine terminalCases (motive := fun i =>
      (spec.liftKernel kernel).intervention reference i =
        (spec.liftIntervention
          { value := kernel.intervention
              (spec.restrictAssignment reference) }).value i)
    ?_ (fun old => ?_) i
  · simp [liftKernel, Kernel.intervention, liftNodeSet, liftIntervention]
  · cases selected : kernel.action old with
    | false =>
        simp [liftKernel, Kernel.intervention, liftNodeSet, liftIntervention,
          selected]
    | true =>
        simp [liftKernel, Kernel.intervention, liftNodeSet, liftIntervention,
          restrictAssignment, selected]

theorem restrict_liftKernel_intervention
    (spec : TerminalVariableSpec S) (kernel : Kernel S)
    (reference : spec.extendSignature.Assignment) :
    (spec.restrictIntervention
      { value := (spec.liftKernel kernel).intervention reference }).value =
      kernel.intervention (spec.restrictAssignment reference) := by
  rw [spec.liftKernel_intervention kernel reference]
  funext i
  exact spec.restrict_liftIntervention
    { value := kernel.intervention (spec.restrictAssignment reference) } i

theorem liftNodeSet_agreesOn (spec : TerminalVariableSpec S)
    (nodes : NodeSet S) (reference sample : spec.extendSignature.Assignment) :
    Kernel.agreesOn (spec.liftNodeSet nodes) reference sample =
      Kernel.agreesOn nodes (spec.restrictAssignment reference)
        (spec.restrictAssignment sample) := by
  unfold Kernel.agreesOn
  simp only [extendSignature, finAll]
  have oldCoordinates :
      finAll S.count (fun i =>
        if spec.liftNodeSet nodes i.castSucc then
          decide (sample i.castSucc = reference i.castSucc)
        else true) =
      finAll S.count (fun i =>
        if nodes i then
          decide (spec.restrictAssignment sample i =
            spec.restrictAssignment reference i)
        else true) := by
    apply finAll_congr
    intro i
    cases selected : nodes i with
    | false => simp [liftNodeSet, selected]
    | true =>
        simp only [liftNodeSet_old, selected, if_true]
        apply decide_eq_decide.mpr
        constructor
        · intro equal
          exact congrArg (cast (spec.value_oldNode i)) equal
        · intro equal
          let valueEqual := spec.value_oldNode i
          have transported := congrArg (cast valueEqual.symm) equal
          simpa [restrictAssignment] using transported
  simpa [liftNodeSet] using oldCoordinates

theorem liftKernel_conditionEvent (spec : TerminalVariableSpec S)
    (kernel : Kernel S) (reference sample : spec.extendSignature.Assignment) :
    (spec.liftKernel kernel).conditionEvent reference sample =
      spec.liftEvent
        (kernel.conditionEvent (spec.restrictAssignment reference)) sample := by
  exact spec.liftNodeSet_agreesOn kernel.condition reference sample

theorem liftKernel_numeratorEvent (spec : TerminalVariableSpec S)
    (kernel : Kernel S) (reference sample : spec.extendSignature.Assignment) :
    (spec.liftKernel kernel).numeratorEvent reference sample =
      spec.liftEvent
        (kernel.numeratorEvent (spec.restrictAssignment reference)) sample := by
  simp [Kernel.numeratorEvent, liftKernel, liftEvent,
    spec.liftNodeSet_agreesOn]

theorem liftKernel_distribution_probVal
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (kernel : Kernel S)
    (reference : spec.extendSignature.Assignment)
    (event : S.Assignment -> Bool) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution N reference).probVal
        (spec.liftEvent event))
      ((kernel.distribution (spec.restrictModel N)
        (spec.restrictAssignment reference)).probVal event) := by
  cases action : kernel.hasAction with
  | false =>
      simpa [Kernel.distribution, spec.liftKernel_hasAction, action] using
        spec.restrictModel_observationalValue_old N event
  | true =>
      have preserved := spec.restrictModel_interventionalValue_old N
        { value := (spec.liftKernel kernel).intervention reference } event
      rw [spec.restrict_liftKernel_intervention kernel reference] at preserved
      simpa [Kernel.distribution, spec.liftKernel_hasAction, action] using preserved

theorem liftKernel_conditionProbability
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (kernel : Kernel S)
    (reference : spec.extendSignature.Assignment) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution N reference).probVal
        ((spec.liftKernel kernel).conditionEvent reference))
      ((kernel.distribution (spec.restrictModel N)
        (spec.restrictAssignment reference)).probVal
          (kernel.conditionEvent (spec.restrictAssignment reference))) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_congr _ _ _
      (fun sample => spec.liftKernel_conditionEvent kernel reference sample))
    (spec.liftKernel_distribution_probVal N kernel reference
      (kernel.conditionEvent (spec.restrictAssignment reference)))

theorem liftKernel_numeratorProbability
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (kernel : Kernel S)
    (reference : spec.extendSignature.Assignment) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution N reference).probVal
        ((spec.liftKernel kernel).numeratorEvent reference))
      ((kernel.distribution (spec.restrictModel N)
        (spec.restrictAssignment reference)).probVal
          (kernel.numeratorEvent (spec.restrictAssignment reference))) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_congr _ _ _
      (fun sample => spec.liftKernel_numeratorEvent kernel reference sample))
    (spec.liftKernel_distribution_probVal N kernel reference
      (kernel.numeratorEvent (spec.restrictAssignment reference)))

/-- A lifted kernel has exactly the partial rational denotation of its restriction. -/
noncomputable def liftKernel_denote
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (kernel : Kernel S)
    (reference : spec.extendSignature.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftKernel kernel).denote N reference)
      (kernel.denote (spec.restrictModel N)
        (spec.restrictAssignment reference)) := by
  exact ProbabilityResult.divide_congr
    (.value (spec.liftKernel_numeratorProbability N kernel reference))
    (.value (spec.liftKernel_conditionProbability N kernel reference))

theorem liftJointQuery_operationKernel
    (spec : TerminalVariableSpec S) (query : JointKernelQuery S) :
    (spec.liftJointQuery query).operationKernel =
      spec.liftKernel query.operationKernel := by
  apply congrArg (fun condition : NodeSet spec.extendSignature =>
    Kernel.mk (spec.liftNodeSet query.outcome)
      (spec.liftNodeSet query.action) condition)
  funext i
  refine terminalCases (motive := fun i =>
      (NodeSet.empty : NodeSet spec.extendSignature) i =
        spec.liftNodeSet query.operationKernel.condition i)
    ?_ (fun old => ?_) i <;>
    simp [JointKernelQuery.operationKernel, NodeSet.empty, liftNodeSet]

theorem liftConditionalQuery_operationKernel
    (spec : TerminalVariableSpec S) (query : ConditionalKernelQuery S) :
    (spec.liftConditionalQuery query).operationKernel =
      spec.liftKernel query.operationKernel :=
  rfl

noncomputable def liftJointQuery_denote
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (query : JointKernelQuery S)
    (reference : spec.extendSignature.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftJointQuery query).sourceTerm.denote N reference)
      (query.sourceTerm.denote (spec.restrictModel N)
        (spec.restrictAssignment reference)) := by
  rw [JointKernelQuery.sourceTerm_eq_operationKernel,
    JointKernelQuery.sourceTerm_eq_operationKernel,
    spec.liftJointQuery_operationKernel query]
  exact spec.liftKernel_denote N query.operationKernel reference

noncomputable def liftConditionalQuery_denote
    (spec : TerminalVariableSpec S)
    (N : ExactModel spec.extendSignature) (query : ConditionalKernelQuery S)
    (reference : spec.extendSignature.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftConditionalQuery query).sourceTerm.denote N reference)
      (query.sourceTerm.denote (spec.restrictModel N)
        (spec.restrictAssignment reference)) := by
  rw [ConditionalKernelQuery.sourceTerm_eq_operationKernel,
    ConditionalKernelQuery.sourceTerm_eq_operationKernel,
    spec.liftConditionalQuery_operationKernel query]
  exact spec.liftKernel_denote N query.operationKernel reference

theorem restrictModel_observationalAgreement
    (spec : TerminalVariableSpec S)
    (left right : ExactModel spec.extendSignature)
    (agreement : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (spec.restrictModel left)
      (spec.restrictModel right) := by
  intro event
  exact QProb.equiv_trans
    (QProb.equiv_symm (spec.restrictModel_observationalValue_old left event))
    (QProb.equiv_trans (agreement (spec.liftEvent event))
      (spec.restrictModel_observationalValue_old right event))

theorem extendModel_evalUnder_restrict (spec : TerminalVariableSpec S)
    (M : ExactModel S) (intervention : HardIntervention S)
    (u : M.latent.Assignment) :
    spec.restrictAssignment
        ((spec.extendModel M).evalUnder
          (spec.liftIntervention intervention).value u) =
      M.evalUnder intervention.value u := by
  funext child
  exact spec.extendModel_evalNodeUnder_old M intervention u child

theorem extendModel_liftEvent_evalUnder (spec : TerminalVariableSpec S)
    (M : ExactModel S) (intervention : HardIntervention S)
    (event : S.Assignment -> Bool) (u : M.latent.Assignment) :
    spec.liftEvent event
        ((spec.extendModel M).evalUnder
          (spec.liftIntervention intervention).value u) =
      event (M.evalUnder intervention.value u) := by
  simp [liftEvent, spec.extendModel_evalUnder_restrict M intervention u]

/-- Every old event has the same interventional probability after learning. -/
theorem extendModel_interventionalValue_old
    (spec : TerminalVariableSpec S) (M : ExactModel S)
    (intervention : HardIntervention S) (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((spec.extendModel M).interventionalValue
        (spec.liftIntervention intervention).value (spec.liftEvent event))
      (M.interventionalValue intervention.value event) := by
  exact QProb.equiv_trans
    ((spec.extendModel M).interventionalValue_eq
      (spec.liftIntervention intervention).value (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr M.prior _ _
        (fun u => spec.extendModel_liftEvent_evalUnder M intervention event u))
      (QProb.equiv_symm (M.interventionalValue_eq intervention.value event)))

theorem lift_empty_intervention (spec : TerminalVariableSpec S) :
    (spec.liftIntervention (HardIntervention.empty S)).value =
      FiniteLatentSCM.noIntervention spec.extendSignature := by
  funext child
  refine terminalCases (motive := fun child =>
      (spec.liftIntervention (HardIntervention.empty S)).value child =
        FiniteLatentSCM.noIntervention spec.extendSignature child)
    ?_ (fun old => ?_) child
  · simp [liftIntervention, HardIntervention.empty,
      FiniteLatentSCM.noIntervention]
  · simp [liftIntervention, HardIntervention.empty,
      FiniteLatentSCM.noIntervention]

theorem extendModel_eval_restrict (spec : TerminalVariableSpec S)
    (M : ExactModel S) (u : M.latent.Assignment) :
    spec.restrictAssignment ((spec.extendModel M).eval u) = M.eval u := by
  have preserved := spec.extendModel_evalUnder_restrict M
    (HardIntervention.empty S) u
  rw [spec.lift_empty_intervention] at preserved
  simpa [FiniteLatentSCM.eval, HardIntervention.empty] using preserved

theorem extendModel_liftEvent_eval (spec : TerminalVariableSpec S)
    (M : ExactModel S) (event : S.Assignment -> Bool)
    (u : M.latent.Assignment) :
    spec.liftEvent event ((spec.extendModel M).eval u) = event (M.eval u) := by
  simp [liftEvent, spec.extendModel_eval_restrict M u]

/-- Every old event has the same observational probability after learning. -/
theorem extendModel_observationalValue_old
    (spec : TerminalVariableSpec S) (M : ExactModel S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((spec.extendModel M).observationalValue (spec.liftEvent event))
      (M.observationalValue event) := by
  exact QProb.equiv_trans
    ((spec.extendModel M).observationalValue_eq (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr M.prior _ _
        (fun u => spec.extendModel_liftEvent_eval M event u))
      (QProb.equiv_symm (M.observationalValue_eq event)))

/-- Execute conservative terminal learning on an epistemic record. -/
def learnRecord (spec : TerminalVariableSpec S) (R : CausalEpistemicRecord S) :
    CausalEpistemicRecord spec.extendSignature where
  model := spec.extendModel R.model
  belief := R.belief
  intervention := spec.liftIntervention R.intervention

@[simp] theorem learnRecord_model (spec : TerminalVariableSpec S)
    (R : CausalEpistemicRecord S) :
    (spec.learnRecord R).model = spec.extendModel R.model :=
  rfl

@[simp] theorem learnRecord_belief (spec : TerminalVariableSpec S)
    (R : CausalEpistemicRecord S) :
    (spec.learnRecord R).belief = R.belief :=
  rfl

/-- Current-belief semantics of every old event is preserved by learning. -/
theorem learnRecord_observedValue_old (spec : TerminalVariableSpec S)
    (R : CausalEpistemicRecord S) (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((spec.learnRecord R).observedValue (spec.liftEvent event))
      (R.observedValue event) := by
  exact QProb.equiv_trans
    ((spec.learnRecord R).observedDist_probVal (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr R.belief _ _ (fun u =>
        spec.extendModel_liftEvent_evalUnder R.model R.intervention event u))
      (QProb.equiv_symm (R.observedDist_probVal event)))

end TerminalVariableSpec

namespace CausalMode

/-- The mode obtained by executing conservative terminal learning. -/
def learnTerminal (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (name : String) : CausalMode spec.extendSignature where
  name := name
  record := spec.learnRecord mode.record

end CausalMode

end Causality
end Thesis
