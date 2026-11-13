import Thesis.Causality.Forgetting.ObservedSink
import Thesis.Causality.PairRoot

namespace Thesis
namespace Causality

open Probability
open CausalEpistemicRecord

/-!
Two-way identifiability for observed directed-sink deletion.

The executable restriction and its semantic preservation live in
`Forgetting.ObservedSink`. This module adds the converse model-class construction:
it extends arbitrary reduced models by a deterministic sink and deterministic
pair roots, then uses that section together with restriction to transport joint
and common-support conditional identifiability in both directions.
-/

namespace ObservedDeletionSpec

/-! ### A semantics-preserving section of observed deletion -/

private def liftedUnitRecord : FiniteProbRecord (ULift.{u} Unit) where
  atoms := [(ULift.up (), 1)]
  den := 1
  den_pos := by omega
  total_mass := rfl

private structure ExtensionLatentData.{u} where
  Value : Type u
  enumeration : List Value
  complete : forall value, value ∈ enumeration
  valueDecidableEq : DecidableEq Value
  factor : FiniteProbRecord Value

private abbrev extensionData {S : ObservedSignature.{u}}
    (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (model.latent.count + pairRootCount graph)) :
    ExtensionLatentData.{u} :=
  Fin.addCases (motive := fun _ => ExtensionLatentData.{u})
    (fun oldSource =>
      { Value := model.latent.Value oldSource
        enumeration := model.latent.valueEnumeration oldSource
        complete := model.latent.value_complete oldSource
        valueDecidableEq := model.latent.valueDecidableEq oldSource
        factor := model.factor oldSource })
    (fun _ =>
      { Value := ULift.{u} Unit
        enumeration := [ULift.up ()]
        complete := fun value => by cases value with | up value => cases value; simp
        valueDecidableEq := inferInstance
        factor := liftedUnitRecord }) source

def extensionLatentValue {S : ObservedSignature.{u}}
    (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (model.latent.count + pairRootCount graph)) : Type u :=
  (extensionData spec graph model source).Value

abbrev oldExtensionRoot (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin model.latent.count) :
    Fin (model.latent.count + pairRootCount graph) :=
  Fin.castAdd (pairRootCount graph) source

abbrev pairExtensionRoot (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (pairRootCount graph)) :
    Fin (model.latent.count + pairRootCount graph) :=
  Fin.natAdd model.latent.count source

@[simp] private theorem extensionData_old (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin model.latent.count) :
    extensionData spec graph model (spec.oldExtensionRoot graph model source) =
      { Value := model.latent.Value source
        enumeration := model.latent.valueEnumeration source
        complete := model.latent.value_complete source
        valueDecidableEq := model.latent.valueDecidableEq source
        factor := model.factor source } := by
  unfold extensionData oldExtensionRoot
  exact Fin.addCases_left source

@[simp] private theorem extensionData_pair (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (pairRootCount graph)) :
    extensionData spec graph model
        (spec.pairExtensionRoot graph model source) =
      { Value := ULift Unit
        enumeration := [ULift.up ()]
        complete := fun value => by
          cases value with | up value => cases value; simp
        valueDecidableEq := inferInstance
        factor := liftedUnitRecord } := by
  unfold extensionData pairExtensionRoot
  exact Fin.addCases_right source

@[simp] theorem extensionLatentValue_old (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin model.latent.count) :
    spec.extensionLatentValue graph model
        (spec.oldExtensionRoot graph model source) =
      model.latent.Value source := by
  simp only [extensionLatentValue, extensionData, oldExtensionRoot,
    Fin.addCases_left]

@[simp] theorem extensionLatentValue_pair (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (pairRootCount graph)) :
    spec.extensionLatentValue graph model
        (spec.pairExtensionRoot graph model source) = ULift.{u} Unit := by
  simp only [extensionLatentValue, extensionData, pairExtensionRoot,
    Fin.addCases_right]

def extensionIncident (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (model.latent.count + pairRootCount graph))
    (child : Fin S.count) : Bool :=
  Fin.addCases (motive := fun _ => Bool)
    (fun oldSource =>
      if retained : child ≠ spec.node then
        model.latent.incident oldSource
          (spec.retainedIndex child retained)
      else false)
    (fun pairSource => pairRootIncident graph pairSource child) source

@[simp] theorem extensionIncident_old (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin model.latent.count) (child : Fin S.count) :
    spec.extensionIncident graph model
        (spec.oldExtensionRoot graph model source) child =
      if retained : child ≠ spec.node then
        model.latent.incident source (spec.retainedIndex child retained)
      else false := by
  simp only [extensionIncident, oldExtensionRoot, Fin.addCases_left]

@[simp] theorem extensionIncident_pair (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (pairRootCount graph)) (child : Fin S.count) :
    spec.extensionIncident graph model
        (spec.pairExtensionRoot graph model source) child =
      pairRootIncident graph source child := by
  simp only [extensionIncident, pairExtensionRoot, Fin.addCases_right]

def extensionLatent (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature) :
    LatentExtension S where
  count := model.latent.count + pairRootCount graph
  Value := spec.extensionLatentValue graph model
  valueEnumeration := fun source =>
    (extensionData spec graph model source).enumeration
  value_complete := fun source =>
    (extensionData spec graph model source).complete
  valueDecidableEq := fun source =>
    (extensionData spec graph model source).valueDecidableEq
  incident := spec.extensionIncident graph model

def extensionFactor (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin (spec.extensionLatent graph model).count) :
    FiniteProbRecord ((spec.extensionLatent graph model).Value source) :=
  Fin.addCases
    (motive := fun source : Fin
      (model.latent.count + pairRootCount graph) =>
        FiniteProbRecord (spec.extensionLatentValue graph model source))
    (fun oldSource =>
      cast (congrArg FiniteProbRecord
        (spec.extensionLatentValue_old graph model oldSource).symm)
        (model.factor oldSource))
    (fun pairSource =>
      cast (congrArg FiniteProbRecord
        (spec.extensionLatentValue_pair graph model pairSource).symm)
        liftedUnitRecord) source

def extensionOldParentValues (spec : ObservedDeletionSpec S)
    {child : Fin S.count} (retained : child ≠ spec.node)
    (parents : S.ParentValues child) :
    spec.signature.ParentValues (spec.retainedIndex child retained) :=
  fun parent edge =>
    parents (selectedEmbed spec.retained parent) (by
      change S.directed (selectedEmbed spec.retained parent)
        (selectedEmbed spec.retained
          (spec.retainedIndex child retained)) = true at edge
      simpa [spec.selectedEmbed_retainedIndex child retained] using edge)

def extensionOldLatentInputs (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    {child : Fin S.count} (retained : child ≠ spec.node)
    (inputs : (spec.extensionLatent graph model).Inputs child) :
    model.latent.Inputs (spec.retainedIndex child retained) :=
  fun source incident =>
    cast (spec.extensionLatentValue_old graph model source)
      (inputs (spec.oldExtensionRoot graph model source) (by
        simpa [extensionLatent, extensionIncident, oldExtensionRoot,
          retained] using incident))

def extensionMechanism (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (child : Fin S.count) (parents : S.ParentValues child)
    (inputs : (spec.extensionLatent graph model).Inputs child) :
    S.Value child :=
  if retained : child ≠ spec.node then
    cast (congrArg S.Value
      (spec.selectedEmbed_retainedIndex child retained))
      (model.mechanism (spec.retainedIndex child retained)
        (spec.extensionOldParentValues retained parents)
        (spec.extensionOldLatentInputs graph model retained inputs))
  else S.defaultValue child

/-- Extend a reduced model by a constant sink and deterministic pair roots. -/
def extendModel (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature) : ExactModel S where
  latent := spec.extensionLatent graph model
  factor := spec.extensionFactor graph model
  prior := FiniteProduct.record
    (spec.extensionLatent graph model).count
    (spec.extensionLatent graph model).Value
    (spec.extensionFactor graph model)
  product_law := FiniteProduct.record_rectangular_probVal
    (spec.extensionLatent graph model).count
    (spec.extensionLatent graph model).Value
    (spec.extensionFactor graph model)
  mechanism := spec.extensionMechanism graph model

theorem extensionIncident_old_retained (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (source : Fin model.latent.count) {child : Fin S.count}
    (incident : (spec.extensionLatent graph model).incident
      (spec.oldExtensionRoot graph model source) child = true) :
    child ≠ spec.node := by
  intro equal
  subst child
  simp [extensionLatent, extensionIncident_old] at incident

theorem extensionLatent_canonical (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (canonical : model.IsCanonicalSemiMarkovian) :
    (spec.extensionLatent graph model).CanonicalSemiMarkovian := by
  intro source i j k hi hj hk
  refine Fin.addCases
    (motive := fun source : Fin (model.latent.count + pairRootCount graph) =>
      (spec.extensionLatent graph model).incident source i = true ->
      (spec.extensionLatent graph model).incident source j = true ->
      (spec.extensionLatent graph model).incident source k = true ->
      i = j ∨ i = k ∨ j = k)
    (fun oldSource hi hj hk => by
      have ri := spec.extensionIncident_old_retained graph model oldSource hi
      have rj := spec.extensionIncident_old_retained graph model oldSource hj
      have rk := spec.extensionIncident_old_retained graph model oldSource hk
      have hi' : model.latent.incident oldSource
          (spec.retainedIndex i ri) = true := by
        change spec.extensionIncident graph model
          (spec.oldExtensionRoot graph model oldSource) i = true at hi
        rw [spec.extensionIncident_old] at hi
        simpa [ri] using hi
      have hj' : model.latent.incident oldSource
          (spec.retainedIndex j rj) = true := by
        change spec.extensionIncident graph model
          (spec.oldExtensionRoot graph model oldSource) j = true at hj
        rw [spec.extensionIncident_old] at hj
        simpa [rj] using hj
      have hk' : model.latent.incident oldSource
          (spec.retainedIndex k rk) = true := by
        change spec.extensionIncident graph model
          (spec.oldExtensionRoot graph model oldSource) k = true at hk
        rw [spec.extensionIncident_old] at hk
        simpa [rk] using hk
      rcases canonical oldSource _ _ _ hi' hj' hk' with same | same | same
      · apply Or.inl
        have embedded := congrArg (selectedEmbed spec.retained) same
        simpa [spec.selectedEmbed_retainedIndex i ri,
          spec.selectedEmbed_retainedIndex j rj] using embedded
      · apply Or.inr; apply Or.inl
        have embedded := congrArg (selectedEmbed spec.retained) same
        simpa [spec.selectedEmbed_retainedIndex i ri,
          spec.selectedEmbed_retainedIndex k rk] using embedded
      · apply Or.inr; apply Or.inr
        have embedded := congrArg (selectedEmbed spec.retained) same
        simpa [spec.selectedEmbed_retainedIndex j rj,
          spec.selectedEmbed_retainedIndex k rk] using embedded)
    (fun pairSource hi hj hk => by
      exact pairRootExtension_canonical graph pairSource i j k
        (by
          change spec.extensionIncident graph model
            (spec.pairExtensionRoot graph model pairSource) i = true at hi
          rw [spec.extensionIncident_pair] at hi
          exact hi)
        (by
          change spec.extensionIncident graph model
            (spec.pairExtensionRoot graph model pairSource) j = true at hj
          rw [spec.extensionIncident_pair] at hj
          exact hj)
        (by
          change spec.extensionIncident graph model
            (spec.pairExtensionRoot graph model pairSource) k = true at hk
          rw [spec.extensionIncident_pair] at hk
          exact hk)) source hi hj hk

private theorem oldRoots_project_only_graph
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (compatible : Compatible model (spec.restrictGraph graph))
    {left right : Fin S.count}
    (different : left ≠ right)
    (oldProjected : finAny model.latent.count (fun source =>
      spec.extensionIncident graph model
          (spec.oldExtensionRoot graph model source) left &&
        spec.extensionIncident graph model
          (spec.oldExtensionRoot graph model source) right) = true) :
    graph.bidirected left right = true := by
  rcases (finAny_eq_true_iff _).mp oldProjected with
    ⟨source, incident⟩
  have parts := Bool.and_eq_true_iff.mp incident
  have leftRetained :=
    spec.extensionIncident_old_retained (graph := graph) (model := model)
      source parts.1
  have rightRetained :=
    spec.extensionIncident_old_retained (graph := graph) (model := model)
      source parts.2
  have modelEdge : model.observedGraph.bidirected
      (spec.retainedIndex left leftRetained)
      (spec.retainedIndex right rightRetained) = true := by
    change
      (!(Nat.beq (spec.retainedIndex left leftRetained).val
          (spec.retainedIndex right rightRetained).val) &&
        finAny model.latent.count (fun latent =>
          model.latent.incident latent
              (spec.retainedIndex left leftRetained) &&
            model.latent.incident latent
              (spec.retainedIndex right rightRetained))) = true
    have beqFalse : Nat.beq
        (spec.retainedIndex left leftRetained).val
        (spec.retainedIndex right rightRetained).val = false := by
      cases selected : Nat.beq
          (spec.retainedIndex left leftRetained).val
          (spec.retainedIndex right rightRetained).val with
      | false => rfl
      | true =>
          have sameReduced : spec.retainedIndex left leftRetained =
              spec.retainedIndex right rightRetained :=
            Fin.ext (Nat.eq_of_beq_eq_true selected)
          have embedded := congrArg (selectedEmbed spec.retained) sameReduced
          have same : left = right := by
            simpa [spec.selectedEmbed_retainedIndex left leftRetained,
              spec.selectedEmbed_retainedIndex right rightRetained] using embedded
          exact (different same).elim
    rw [beqFalse]
    simp only [Bool.not_false, Bool.true_and]
    exact finAny_eq_true_of _ source (by
      simp [extensionIncident_old, leftRetained, rightRetained] at parts
      exact Bool.and_eq_true_iff.mpr parts)
  have graphEdge := compatible.2
    (spec.retainedIndex left leftRetained)
    (spec.retainedIndex right rightRetained)
  rw [modelEdge] at graphEdge
  simpa [restrictGraph, spec.selectedEmbed_retainedIndex left leftRetained,
    spec.selectedEmbed_retainedIndex right rightRetained] using graphEdge.symm

theorem extendModel_observedGraph (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (compatible : Compatible model (spec.restrictGraph graph))
    (left right : Fin S.count) :
    (spec.extendModel graph model).observedGraph.bidirected left right =
      graph.bidirected left right := by
  unfold FiniteLatentSCM.observedGraph LatentExtension.observedGraph
    LatentExtension.projectedBidirected
  cases same : Nat.beq left.val right.val with
  | true =>
      have equal : left = right := Fin.ext (Nat.eq_of_beq_eq_true same)
      subst right
      simp [graph.bidirected_irreflexive]
  | false =>
      simp only [same, Bool.not_false, Bool.true_and]
      have split := finAny_add
        (fun source =>
          spec.extensionIncident graph model
              (spec.oldExtensionRoot graph model source) left &&
            spec.extensionIncident graph model
              (spec.oldExtensionRoot graph model source) right)
        (fun source => pairRootIncident graph source left &&
          pairRootIncident graph source right)
      change
        finAny (model.latent.count + pairRootCount graph)
          (fun source =>
            spec.extensionIncident graph model source left &&
              spec.extensionIncident graph model source right) =
          graph.bidirected left right
      have familyEqual :
          (fun source =>
            spec.extensionIncident graph model source left &&
              spec.extensionIncident graph model source right) =
          Fin.addCases (motive := fun _ => Bool)
            (fun source =>
              spec.extensionIncident graph model
                  (spec.oldExtensionRoot graph model source) left &&
                spec.extensionIncident graph model
                  (spec.oldExtensionRoot graph model source) right)
            (fun source => pairRootIncident graph source left &&
              pairRootIncident graph source right) := by
        funext source
        refine Fin.addCases (motive := fun source =>
            (spec.extensionIncident graph model source left &&
              spec.extensionIncident graph model source right) =
            Fin.addCases (motive := fun _ => Bool)
              (fun old =>
                spec.extensionIncident graph model
                    (spec.oldExtensionRoot graph model old) left &&
                  spec.extensionIncident graph model
                    (spec.oldExtensionRoot graph model old) right)
              (fun pair => pairRootIncident graph pair left &&
                pairRootIncident graph pair right) source)
          (fun old => by simp [oldExtensionRoot])
          (fun pair => by
            simp only [Fin.addCases_right]
            change
              (spec.extensionIncident graph model
                  (spec.pairExtensionRoot graph model pair) left &&
                spec.extensionIncident graph model
                  (spec.pairExtensionRoot graph model pair) right) =
              (pairRootIncident graph pair left &&
                pairRootIncident graph pair right)
            rw [spec.extensionIncident_pair, spec.extensionIncident_pair]) source
      rw [familyEqual, split]
      have pairProjected := pairRootExtension_projected graph left right
      unfold LatentExtension.projectedBidirected pairRootExtension at pairProjected
      rw [same] at pairProjected
      simp only [Bool.not_false, Bool.true_and] at pairProjected
      cases edge : graph.bidirected left right with
      | true => simp [pairProjected, edge]
      | false =>
          have oldFalse : finAny model.latent.count (fun source =>
              spec.extensionIncident graph model
                  (spec.oldExtensionRoot graph model source) left &&
                spec.extensionIncident graph model
                  (spec.oldExtensionRoot graph model source) right) = false := by
            cases old : finAny model.latent.count (fun source =>
                spec.extensionIncident graph model
                    (spec.oldExtensionRoot graph model source) left &&
                  spec.extensionIncident graph model
                    (spec.oldExtensionRoot graph model source) right) with
            | false => rfl
            | true =>
                have impossible := spec.oldRoots_project_only_graph graph model
                  compatible (fun equal => by
                    subst right
                    simp at same) old
                rw [edge] at impossible
                contradiction
          rw [oldFalse, pairProjected, edge]
          rfl

theorem extendModel_compatible (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (compatible : Compatible model (spec.restrictGraph graph)) :
    Compatible (spec.extendModel graph model) graph := by
  constructor
  · exact spec.extensionLatent_canonical graph model compatible.1
  · exact spec.extendModel_observedGraph graph model compatible

def restrictExtensionLatentAssignment (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (assignment : (spec.extensionLatent graph model).Assignment) :
    model.latent.Assignment :=
  fun source => cast (spec.extensionLatentValue_old graph model source)
    (assignment (spec.oldExtensionRoot graph model source))

def extendLatentEvents (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (events : (source : Fin model.latent.count) ->
      model.latent.Value source -> Bool)
    (source : Fin (spec.extensionLatent graph model).count) :
    (spec.extensionLatent graph model).Value source -> Bool :=
  Fin.addCases
    (motive := fun source : Fin
      (model.latent.count + pairRootCount graph) =>
        spec.extensionLatentValue graph model source -> Bool)
    (fun oldSource value =>
      events oldSource
        (cast (spec.extensionLatentValue_old graph model oldSource) value))
    (fun _ _ => true) source

theorem extendLatentEvents_rectangularEvent
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (events : (source : Fin model.latent.count) ->
      model.latent.Value source -> Bool)
    (assignment : (spec.extensionLatent graph model).Assignment) :
    (spec.extensionLatent graph model).rectangularEvent
        (spec.extendLatentEvents graph model events) assignment =
      model.latent.rectangularEvent events
        (spec.restrictExtensionLatentAssignment graph model assignment) := by
  apply Bool.eq_iff_iff.mpr
  change
    FiniteProduct.rectangularEvent
        (spec.extensionLatent graph model).count
        (spec.extensionLatent graph model).Value
        (spec.extendLatentEvents graph model events) assignment = true <->
      FiniteProduct.rectangularEvent model.latent.count model.latent.Value
        events (spec.restrictExtensionLatentAssignment graph model assignment) =
        true
  rw [FiniteProduct.rectangularEvent_eq_true_iff,
    FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro all source
    have selected := all (spec.oldExtensionRoot graph model source)
    simpa [extendLatentEvents, oldExtensionRoot,
      restrictExtensionLatentAssignment] using selected
  · intro all source
    refine Fin.addCases
      (motive := fun source : Fin
        (model.latent.count + pairRootCount graph) =>
          spec.extendLatentEvents graph model events source
            (assignment source) = true)
      (fun oldSource => by
        simpa [extendLatentEvents, oldExtensionRoot,
          restrictExtensionLatentAssignment] using all oldSource)
      (fun pairSource => by
        simp [extendLatentEvents]) source

theorem extensionFactor_old_probVal (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (events : (source : Fin model.latent.count) ->
      model.latent.Value source -> Bool)
    (source : Fin model.latent.count) :
    QProb.Equiv
      ((spec.extensionFactor graph model
          (spec.oldExtensionRoot graph model source)).probVal
        (spec.extendLatentEvents graph model events
          (spec.oldExtensionRoot graph model source)))
      ((model.factor source).probVal (events source)) := by
  unfold extensionFactor
  rw [Fin.addCases_left]
  simpa [extendLatentEvents, oldExtensionRoot] using
    (cast_record_probVal
      (spec.extensionLatentValue_old graph model source).symm
      (model.factor source) (events source))

theorem extensionFactor_pair_probVal (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) (model : ExactModel spec.signature)
    (events : (source : Fin model.latent.count) ->
      model.latent.Value source -> Bool)
    (source : Fin (pairRootCount graph)) :
    QProb.Equiv
      ((spec.extensionFactor graph model
          (spec.pairExtensionRoot graph model source)).probVal
      (spec.extendLatentEvents graph model events
          (spec.pairExtensionRoot graph model source))) QProb.one := by
  unfold extensionFactor
  rw [Fin.addCases_right]
  exact QProb.equiv_trans
    (by
      simpa [extendLatentEvents, pairExtensionRoot] using
        (cast_record_probVal
          (spec.extensionLatentValue_pair graph model source).symm
          liftedUnitRecord topEvent))
    liftedUnitRecord.normalization

theorem extendLatentEvents_qProduct
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (events : (source : Fin model.latent.count) ->
      model.latent.Value source -> Bool) :
    QProb.Equiv
      (FiniteProduct.qProduct (spec.extensionLatent graph model).count
        (fun source => (spec.extensionFactor graph model source).probVal
          (spec.extendLatentEvents graph model events source)))
      (FiniteProduct.qProduct model.latent.count
        (fun source => (model.factor source).probVal (events source))) := by
  let oldValues : Fin model.latent.count -> QProb :=
    fun source => (model.factor source).probVal (events source)
  exact QProb.equiv_trans
    (FiniteProduct.qProduct_congr
      (model.latent.count + pairRootCount graph) (fun source => by
        refine Fin.addCases
          (motive := fun source : Fin
            (model.latent.count + pairRootCount graph) =>
              QProb.Equiv
                ((spec.extensionFactor graph model source).probVal
                  (spec.extendLatentEvents graph model events source))
                (addOnes model.latent.count (pairRootCount graph)
                  oldValues source))
          (fun oldSource => by
            simpa only [Fin.addCases_left, addOnes] using
              spec.extensionFactor_old_probVal graph model events oldSource)
          (fun pairSource => by
            simpa only [Fin.addCases_right, addOnes] using
              spec.extensionFactor_pair_probVal graph model events pairSource)
          source))
    (qProduct_add_ones model.latent.count (pairRootCount graph) oldValues)

theorem extendModel_projectedPrior_probVal
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (event : model.latent.Assignment -> Bool) :
    QProb.Equiv
      (((spec.extendModel graph model).prior.map
        (spec.restrictExtensionLatentAssignment graph model)).probVal event)
      (model.prior.probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons
    ((spec.extendModel graph model).prior.map
      (spec.restrictExtensionLatentAssignment graph model))
    model.prior model.latent.assignmentEnumeration
    model.latent.assignmentEnumeration_nodup
    model.latent.assignmentEnumeration_complete
  intro assignment
  let events := model.latent.assignmentSingletonEvents assignment
  have mapped := FiniteProbRecord.map_probVal
    (spec.extendModel graph model).prior
    (spec.restrictExtensionLatentAssignment graph model)
    (FiniteProbRecord.singletonEvent assignment)
  have eventEquality :
      (fun extended => FiniteProbRecord.singletonEvent assignment
        (spec.restrictExtensionLatentAssignment graph model extended)) =
      (spec.extensionLatent graph model).rectangularEvent
        (spec.extendLatentEvents graph model events) := by
    funext extended
    rw [spec.extendLatentEvents_rectangularEvent graph model events extended]
    exact congrFun
      (model.latent.rectangularEvent_assignmentSingletonEvents assignment).symm
      (spec.restrictExtensionLatentAssignment graph model extended)
  have mappedRectangular := QProb.equiv_trans mapped
    (FiniteProbRecord.probVal_congr (spec.extendModel graph model).prior _ _
      (fun extended => congrFun eventEquality extended))
  have extendedProduct :=
    (spec.extendModel graph model).product_law
      (spec.extendLatentEvents graph model events)
  have oldProduct := model.product_law events
  rw [model.latent.rectangularEvent_assignmentSingletonEvents assignment]
    at oldProduct
  exact QProb.equiv_trans mappedRectangular
    (QProb.equiv_trans extendedProduct
      (QProb.equiv_trans
        (spec.extendLatentEvents_qProduct graph model events)
        (QProb.equiv_symm oldProduct)))

/-- The manufactured full model evaluates every retained equation as before. -/
theorem extendModel_evalNodeUnder_retained
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (intervention : HardIntervention S)
    (assignment : (spec.extendModel graph model).latent.Assignment)
    (child : Fin spec.signature.count) :
    (spec.extendModel graph model).evalNodeUnder intervention.value assignment
        (selectedEmbed spec.retained child) =
      model.evalNodeUnder (spec.restrictIntervention intervention).value
        (spec.restrictExtensionLatentAssignment graph model assignment) child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : intervention.value (selectedEmbed spec.retained child) with
  | some value =>
      simp [restrictIntervention, selected]
  | none =>
      have retained := spec.retained_embed_ne child
      have indexEqual :
          spec.retainedIndex (selectedEmbed spec.retained child) retained =
            child := by
        exact spec.retainedIndex_selectedEmbed child
      simp only [restrictIntervention, selected, extendModel,
        extensionMechanism, dif_pos retained]
      let result : (node : Fin spec.signature.count) ->
          spec.signature.Value node := fun node =>
        model.mechanism node
          (fun parent _ =>
            model.evalNodeUnder
              (spec.restrictIntervention intervention).value
              (spec.restrictExtensionLatentAssignment graph model assignment)
              parent)
          (fun source _ =>
            spec.restrictExtensionLatentAssignment graph model assignment source)
      have atIndex :
          model.mechanism
              (spec.retainedIndex (selectedEmbed spec.retained child) retained)
              (spec.extensionOldParentValues retained (fun parent _edge =>
                (spec.extendModel graph model).evalNodeUnder intervention.value
                  assignment parent))
              (spec.extensionOldLatentInputs graph model retained
                (fun source _ => assignment source)) =
            result
              (spec.retainedIndex (selectedEmbed spec.retained child) retained) := by
        apply congrArg (fun parents =>
          model.mechanism
            (spec.retainedIndex (selectedEmbed spec.retained child) retained)
            parents
            (fun source _ =>
              spec.restrictExtensionLatentAssignment graph model assignment
                source))
        funext parent edge
        exact spec.extendModel_evalNodeUnder_retained graph model intervention
          assignment parent
      calc
        _ = cast
            (congrArg S.Value
              (spec.selectedEmbed_retainedIndex
                (selectedEmbed spec.retained child) retained))
            (result
              (spec.retainedIndex (selectedEmbed spec.retained child)
                retained)) := congrArg _ atIndex
        _ = result child := by
          exact (dependent_apply_eq_cast
            (fun node => S.Value (selectedEmbed spec.retained node))
            indexEqual result).symm
        _ = _ := rfl
termination_by child.val
decreasing_by
  simpa only [indexEqual] using spec.signature.directed_earlier edge

theorem extendModel_evalUnder_restrict
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (intervention : HardIntervention S)
    (assignment : (spec.extendModel graph model).latent.Assignment) :
    spec.restrictAssignment
        ((spec.extendModel graph model).evalUnder intervention.value assignment) =
      model.evalUnder (spec.restrictIntervention intervention).value
        (spec.restrictExtensionLatentAssignment graph model assignment) := by
  funext child
  exact spec.extendModel_evalNodeUnder_retained graph model intervention
    assignment child

theorem extendModel_liftEvent_evalUnder
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (intervention : HardIntervention S)
    (event : spec.signature.Assignment -> Bool)
    (assignment : (spec.extendModel graph model).latent.Assignment) :
    spec.liftEvent event
        ((spec.extendModel graph model).evalUnder intervention.value assignment) =
      event (model.evalUnder (spec.restrictIntervention intervention).value
        (spec.restrictExtensionLatentAssignment graph model assignment)) := by
  simp [liftEvent,
    spec.extendModel_evalUnder_restrict graph model intervention assignment]

theorem extendModel_interventionalValue
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (intervention : HardIntervention S)
    (event : spec.signature.Assignment -> Bool) :
    QProb.Equiv
      ((spec.extendModel graph model).interventionalValue intervention.value
        (spec.liftEvent event))
      (model.interventionalValue
        (spec.restrictIntervention intervention).value event) := by
  exact QProb.equiv_trans
    ((spec.extendModel graph model).interventionalValue_eq intervention.value
      (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr
        (spec.extendModel graph model).prior _ _
        (fun assignment =>
          spec.extendModel_liftEvent_evalUnder graph model intervention event
            assignment))
      (QProb.equiv_trans
        (QProb.equiv_symm
          (FiniteProbRecord.map_probVal
            (spec.extendModel graph model).prior
            (spec.restrictExtensionLatentAssignment graph model)
            (fun assignment => event
              (model.evalUnder
                (spec.restrictIntervention intervention).value assignment))))
        (QProb.equiv_trans
          (spec.extendModel_projectedPrior_probVal graph model
            (fun assignment => event
              (model.evalUnder
                (spec.restrictIntervention intervention).value assignment)))
          (QProb.equiv_symm
            (model.interventionalValue_eq
              (spec.restrictIntervention intervention).value event)))))

theorem extendModel_observationalValue
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (event : spec.signature.Assignment -> Bool) :
    QProb.Equiv
      ((spec.extendModel graph model).observationalValue (spec.liftEvent event))
      (model.observationalValue event) := by
  have preserved := spec.extendModel_interventionalValue graph model
    (HardIntervention.empty S) event
  simpa [FiniteLatentSCM.observationalValue, HardIntervention.empty,
    restrictIntervention, FiniteLatentSCM.noIntervention] using preserved

theorem extendModel_liftKernel_distribution_probVal
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (kernel : Kernel spec.signature) (reference : S.Assignment)
    (event : spec.signature.Assignment -> Bool) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution (spec.extendModel graph model)
        reference).probVal (spec.liftEvent event))
      ((kernel.distribution model (spec.restrictAssignment reference)).probVal
        event) := by
  cases action : kernel.hasAction with
  | false =>
      simpa [Kernel.distribution, spec.liftKernel_hasAction, action] using
        spec.extendModel_observationalValue graph model event
  | true =>
      have preserved := spec.extendModel_interventionalValue graph model
        { value := (spec.liftKernel kernel).intervention reference } event
      rw [spec.restrict_liftKernel_intervention kernel reference] at preserved
      simpa [Kernel.distribution, spec.liftKernel_hasAction, action] using
        preserved

theorem extendModel_liftKernel_conditionProbability
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (kernel : Kernel spec.signature) (reference : S.Assignment) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution (spec.extendModel graph model)
        reference).probVal
          ((spec.liftKernel kernel).conditionEvent reference))
      ((kernel.distribution model (spec.restrictAssignment reference)).probVal
        (kernel.conditionEvent (spec.restrictAssignment reference))) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_congr _ _ _
      (fun sample => spec.liftKernel_conditionEvent kernel reference sample))
    (spec.extendModel_liftKernel_distribution_probVal graph model kernel
      reference (kernel.conditionEvent (spec.restrictAssignment reference)))

theorem extendModel_liftKernel_numeratorProbability
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (kernel : Kernel spec.signature) (reference : S.Assignment) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution (spec.extendModel graph model)
        reference).probVal
          ((spec.liftKernel kernel).numeratorEvent reference))
      ((kernel.distribution model (spec.restrictAssignment reference)).probVal
        (kernel.numeratorEvent (spec.restrictAssignment reference))) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_congr _ _ _
      (fun sample => spec.liftKernel_numeratorEvent kernel reference sample))
    (spec.extendModel_liftKernel_distribution_probVal graph model kernel
      reference (kernel.numeratorEvent (spec.restrictAssignment reference)))

noncomputable def extendModel_liftKernel_denote
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (kernel : Kernel spec.signature) (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftKernel kernel).denote (spec.extendModel graph model) reference)
      (kernel.denote model (spec.restrictAssignment reference)) := by
  exact ProbabilityResult.divide_congr
    (.value (spec.extendModel_liftKernel_numeratorProbability graph model kernel
      reference))
    (.value (spec.extendModel_liftKernel_conditionProbability graph model kernel
      reference))

noncomputable def extendModel_liftJointQuery_denote
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (query : JointKernelQuery spec.signature) (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftJointQuery query).sourceTerm.denote
        (spec.extendModel graph model) reference)
      (query.sourceTerm.denote model (spec.restrictAssignment reference)) := by
  rw [JointKernelQuery.sourceTerm_eq_operationKernel,
    JointKernelQuery.sourceTerm_eq_operationKernel,
    spec.liftJointQuery_operationKernel query]
  exact spec.extendModel_liftKernel_denote graph model query.operationKernel
    reference

noncomputable def extendModel_liftConditionalQuery_denote
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (query : ConditionalKernelQuery spec.signature) (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftConditionalQuery query).sourceTerm.denote
        (spec.extendModel graph model) reference)
      (query.sourceTerm.denote model (spec.restrictAssignment reference)) := by
  rw [ConditionalKernelQuery.sourceTerm_eq_operationKernel,
    ConditionalKernelQuery.sourceTerm_eq_operationKernel,
    spec.liftConditionalQuery_operationKernel query]
  exact spec.extendModel_liftKernel_denote graph model query.operationKernel
    reference

/-- Restore a reduced assignment, fixing the deleted sink to its default. -/
def extendAssignment (spec : ObservedDeletionSpec S)
    (assignment : spec.signature.Assignment) : S.Assignment :=
  fun node => if retained : node ≠ spec.node then
    cast (congrArg S.Value
      (spec.selectedEmbed_retainedIndex node retained))
      (assignment (spec.retainedIndex node retained))
  else S.defaultValue node

@[simp] theorem restrict_extendAssignment (spec : ObservedDeletionSpec S)
    (assignment : spec.signature.Assignment) :
    spec.restrictAssignment (spec.extendAssignment assignment) = assignment := by
  funext child
  let retained := spec.retained_embed_ne child
  have indexEqual :
      spec.retainedIndex (selectedEmbed spec.retained child) retained = child :=
    spec.retainedIndex_selectedEmbed child
  unfold restrictAssignment extendAssignment
  rw [dif_pos retained]
  exact (dependent_apply_eq_cast
    (fun node => S.Value (selectedEmbed spec.retained node))
    indexEqual assignment).symm

theorem extendModel_evalUnder_empty
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature)
    (assignment : (spec.extendModel graph model).latent.Assignment) :
    (spec.extendModel graph model).evalUnder
        (FiniteLatentSCM.noIntervention S) assignment =
      spec.extendAssignment
        (model.evalUnder (FiniteLatentSCM.noIntervention spec.signature)
          (spec.restrictExtensionLatentAssignment graph model assignment)) := by
  funext node
  by_cases retained : node ≠ spec.node
  · let child := spec.retainedIndex node retained
    have coordinateEqual := spec.selectedEmbed_retainedIndex node retained
    have preserved := spec.extendModel_evalNodeUnder_retained graph model
      (HardIntervention.empty S) assignment child
    change
      (spec.extendModel graph model).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) assignment node =
        spec.extendAssignment
          (model.evalUnder (FiniteLatentSCM.noIntervention spec.signature)
            (spec.restrictExtensionLatentAssignment graph model assignment)) node
    rw [extendAssignment, dif_pos retained]
    change
      (spec.extendModel graph model).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) assignment node =
        cast (congrArg S.Value coordinateEqual)
          (model.evalNodeUnder (FiniteLatentSCM.noIntervention spec.signature)
            (spec.restrictExtensionLatentAssignment graph model assignment)
            child)
    exact Eq.trans
      (dependent_apply_eq_cast S.Value coordinateEqual
        (fun oldNode =>
          (spec.extendModel graph model).evalNodeUnder
            (FiniteLatentSCM.noIntervention S) assignment oldNode))
      (congrArg (cast (congrArg S.Value coordinateEqual)) preserved)
  · have equal : node = spec.node := by
      cases decEq node spec.node with
      | isTrue equal => exact equal
      | isFalse different => exact (retained different).elim
    subst node
    rw [FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder]
    simp [FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention,
      extendModel, extensionMechanism, extendAssignment]

theorem extendModel_observationalValue_full
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (model : ExactModel spec.signature) (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((spec.extendModel graph model).observationalValue event)
      (model.observationalValue (fun assignment =>
        event (spec.extendAssignment assignment))) := by
  exact QProb.equiv_trans
    ((spec.extendModel graph model).interventionalValue_eq
      (FiniteLatentSCM.noIntervention S) event)
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr
        (spec.extendModel graph model).prior _ _
        (fun assignment => congrArg event
          (spec.extendModel_evalUnder_empty graph model assignment)))
      (QProb.equiv_trans
        (QProb.equiv_symm
          (FiniteProbRecord.map_probVal
            (spec.extendModel graph model).prior
            (spec.restrictExtensionLatentAssignment graph model)
            (fun assignment => event (spec.extendAssignment
              (model.evalUnder (FiniteLatentSCM.noIntervention spec.signature)
                assignment)))))
        (QProb.equiv_trans
          (spec.extendModel_projectedPrior_probVal graph model
            (fun assignment => event (spec.extendAssignment
              (model.evalUnder (FiniteLatentSCM.noIntervention spec.signature)
                assignment))))
          (QProb.equiv_symm
            (model.interventionalValue_eq
              (FiniteLatentSCM.noIntervention spec.signature)
              (fun assignment => event
                (spec.extendAssignment assignment)))))))

theorem extendModel_observationalAgreement
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (left right : ExactModel spec.signature)
    (agreement : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (spec.extendModel graph left)
      (spec.extendModel graph right) := by
  intro event
  exact QProb.equiv_trans
    (spec.extendModel_observationalValue_full graph left event)
    (QProb.equiv_trans
      (agreement (fun assignment => event (spec.extendAssignment assignment)))
      (QProb.equiv_symm
        (spec.extendModel_observationalValue_full graph right event)))

/-- A retained joint query is identifiable before deletion iff its lift is
identifiable before the sink is removed. -/
theorem liftJointQuery_identifiable_iff
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (query : JointKernelQuery spec.signature) :
    TypeTheoreticIdentifiable graph (spec.liftJointQuery query) <->
      TypeTheoreticIdentifiable (spec.restrictGraph graph) query := by
  constructor
  · intro identifiable left right leftCompatible rightCompatible observational
      assignment
    have extendedEquivalent := identifiable
      (spec.extendModel graph left) (spec.extendModel graph right)
      (spec.extendModel_compatible graph left leftCompatible)
      (spec.extendModel_compatible graph right rightCompatible)
      (spec.extendModel_observationalAgreement graph left right observational)
      (spec.extendAssignment assignment)
    rcases extendedEquivalent with ⟨extendedEquivalent⟩
    have leftBridge : ProbabilityResult.Equivalent
        ((spec.liftJointQuery query).sourceTerm.denote
          (spec.extendModel graph left) (spec.extendAssignment assignment))
        (query.sourceTerm.denote left assignment) := by
      simpa using spec.extendModel_liftJointQuery_denote graph left query
        (spec.extendAssignment assignment)
    have rightBridge : ProbabilityResult.Equivalent
        ((spec.liftJointQuery query).sourceTerm.denote
          (spec.extendModel graph right) (spec.extendAssignment assignment))
        (query.sourceTerm.denote right assignment) := by
      simpa using spec.extendModel_liftJointQuery_denote graph right query
        (spec.extendAssignment assignment)
    exact ⟨ProbabilityResult.trans
      (ProbabilityResult.symm leftBridge)
      (ProbabilityResult.trans extendedEquivalent
        rightBridge)⟩
  · intro identifiable left right leftCompatible rightCompatible observational
      assignment
    have restrictedEquivalent := identifiable
      (spec.restrictModel left) (spec.restrictModel right)
      (spec.restrictModel_compatible left graph leftCompatible)
      (spec.restrictModel_compatible right graph rightCompatible)
      (spec.restrictModel_observationalAgreement left right observational)
      (spec.restrictAssignment assignment)
    rcases restrictedEquivalent with ⟨restrictedEquivalent⟩
    exact ⟨ProbabilityResult.trans
      (spec.liftJointQuery_denote left query assignment)
      (ProbabilityResult.trans restrictedEquivalent
        (ProbabilityResult.symm
          (spec.liftJointQuery_denote right query assignment)))⟩

/-- The same two-way result for conditional kernels on common support. -/
theorem liftConditionalQuery_identifiable_iff
    (spec : ObservedDeletionSpec S) (graph : ObservedGraph S)
    (query : ConditionalKernelQuery spec.signature) :
    TypeTheoreticConditionalIdentifiable graph
        (spec.liftConditionalQuery query) <->
      TypeTheoreticConditionalIdentifiable (spec.restrictGraph graph) query := by
  constructor
  · intro identifiable left right leftCompatible rightCompatible observational
      assignment leftSupported rightSupported
    let reference := spec.extendAssignment assignment
    have leftBridge : ProbabilityResult.Equivalent
        ((spec.liftConditionalQuery query).sourceTerm.denote
          (spec.extendModel graph left) reference)
        (query.sourceTerm.denote left assignment) := by
      simpa [reference] using
        spec.extendModel_liftConditionalQuery_denote graph left query reference
    have rightBridge : ProbabilityResult.Equivalent
        ((spec.liftConditionalQuery query).sourceTerm.denote
          (spec.extendModel graph right) reference)
        (query.sourceTerm.denote right assignment) := by
      simpa [reference] using
        spec.extendModel_liftConditionalQuery_denote graph right query reference
    have extendedLeftSupported :
        (spec.liftConditionalQuery query).sourceTerm.SupportedAt
          (spec.extendModel graph left) reference := by
      rcases leftSupported with ⟨value, supported⟩
      exact ⟨value, ProbabilityResult.trans leftBridge supported⟩
    have extendedRightSupported :
        (spec.liftConditionalQuery query).sourceTerm.SupportedAt
          (spec.extendModel graph right) reference := by
      rcases rightSupported with ⟨value, supported⟩
      exact ⟨value, ProbabilityResult.trans rightBridge supported⟩
    have extendedEquivalent := identifiable
      (spec.extendModel graph left) (spec.extendModel graph right)
      (spec.extendModel_compatible graph left leftCompatible)
      (spec.extendModel_compatible graph right rightCompatible)
      (spec.extendModel_observationalAgreement graph left right observational)
      reference extendedLeftSupported extendedRightSupported
    rcases extendedEquivalent with ⟨extendedEquivalent⟩
    exact ⟨ProbabilityResult.trans (ProbabilityResult.symm leftBridge)
      (ProbabilityResult.trans extendedEquivalent rightBridge)⟩
  · intro identifiable left right leftCompatible rightCompatible observational
      assignment leftSupported rightSupported
    let leftBridge := spec.liftConditionalQuery_denote left query assignment
    let rightBridge := spec.liftConditionalQuery_denote right query assignment
    have restrictedLeftSupported : query.sourceTerm.SupportedAt
        (spec.restrictModel left) (spec.restrictAssignment assignment) := by
      rcases leftSupported with ⟨value, supported⟩
      exact ⟨value, ProbabilityResult.trans
        (ProbabilityResult.symm leftBridge) supported⟩
    have restrictedRightSupported : query.sourceTerm.SupportedAt
        (spec.restrictModel right) (spec.restrictAssignment assignment) := by
      rcases rightSupported with ⟨value, supported⟩
      exact ⟨value, ProbabilityResult.trans
        (ProbabilityResult.symm rightBridge) supported⟩
    have restrictedEquivalent := identifiable
      (spec.restrictModel left) (spec.restrictModel right)
      (spec.restrictModel_compatible left graph leftCompatible)
      (spec.restrictModel_compatible right graph rightCompatible)
      (spec.restrictModel_observationalAgreement left right observational)
      (spec.restrictAssignment assignment) restrictedLeftSupported
        restrictedRightSupported
    rcases restrictedEquivalent with ⟨restrictedEquivalent⟩
    exact ⟨ProbabilityResult.trans leftBridge
      (ProbabilityResult.trans restrictedEquivalent
        (ProbabilityResult.symm rightBridge))⟩


end ObservedDeletionSpec

end Causality
end Thesis
