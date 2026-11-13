import Thesis.Causality.Forgetting.ObservedSink

namespace Thesis
namespace Causality

open Probability
open CausalEpistemicRecord

/-! ## Deletion of an arbitrary unused exogenous root -/

/-- Proof-carrying data for deleting one latent coordinate.  The coordinate is
unused exactly when it is incident to no observed mechanism. -/
structure ExogenousDeletionSpec (model : ExactModel S) where
  retainedCount : Nat
  count_eq : model.latent.count = retainedCount + 1
  source : Fin (retainedCount + 1)
  unused : forall child,
    model.latent.incident (Fin.cast count_eq.symm source) child = false

namespace ExogenousDeletionSpec

variable {S : ObservedSignature} {model : ExactModel S}

/-- Package any unused source without asking the caller for predecessor
arithmetic. -/
def ofUnused (model : ExactModel S) (source : Fin model.latent.count)
    (unused : forall child, model.latent.incident source child = false) :
    ExogenousDeletionSpec model := by
  have positive : 1 <= model.latent.count :=
    Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt source.isLt)
  let countEqual : model.latent.count = model.latent.count - 1 + 1 :=
    (Nat.sub_add_cancel positive).symm
  exact
    { retainedCount := model.latent.count - 1
      count_eq := countEqual
      source := Fin.cast countEqual source
      unused := fun child => by
        simpa [countEqual] using unused child }

/-- Interpret a normalized old latent index in the model's original index type. -/
def oldRoot (spec : ExogenousDeletionSpec model)
    (root : Fin (spec.retainedCount + 1)) : Fin model.latent.count :=
  Fin.cast spec.count_eq.symm root

/-- Normalize an original latent index. -/
def normalizeRoot (spec : ExogenousDeletionSpec model)
    (root : Fin model.latent.count) : Fin (spec.retainedCount + 1) :=
  Fin.cast spec.count_eq root

@[simp] theorem normalize_oldRoot (spec : ExogenousDeletionSpec model)
    (root : Fin (spec.retainedCount + 1)) :
    spec.normalizeRoot (spec.oldRoot root) = root := by
  simp [normalizeRoot, oldRoot]

@[simp] theorem old_normalizeRoot (spec : ExogenousDeletionSpec model)
    (root : Fin model.latent.count) :
    spec.oldRoot (spec.normalizeRoot root) = root := by
  simp [normalizeRoot, oldRoot]

/-- The original index of the source being removed. -/
def deletedRoot (spec : ExogenousDeletionSpec model) :
    Fin model.latent.count := spec.oldRoot spec.source

/-- Embed a reduced root into the original latent family. -/
def embedRoot (spec : ExogenousDeletionSpec model)
    (root : Fin spec.retainedCount) : Fin model.latent.count :=
  spec.oldRoot (FiniteDeletion.embed spec.source root)

theorem embedRoot_ne_deleted (spec : ExogenousDeletionSpec model)
    (root : Fin spec.retainedCount) :
    spec.embedRoot root ≠ spec.deletedRoot := by
  intro equal
  have normalized := congrArg spec.normalizeRoot equal
  have impossible : FiniteDeletion.embed spec.source root = spec.source := by
    simpa [embedRoot, deletedRoot] using normalized
  exact FiniteDeletion.embed_ne_deleted spec.source root impossible

/-- Constructively find the reduced coordinate of a retained old root. -/
def rootIndex (spec : ExogenousDeletionSpec model)
    (root : Fin model.latent.count) (different : root ≠ spec.deletedRoot) :
    Fin spec.retainedCount :=
  FiniteDeletion.index spec.source (spec.normalizeRoot root) (by
    intro equal
    apply different
    have old := congrArg spec.oldRoot equal
    simpa [deletedRoot] using old)

theorem embedRoot_rootIndex (spec : ExogenousDeletionSpec model)
    (root : Fin model.latent.count) (different : root ≠ spec.deletedRoot) :
    spec.embedRoot (spec.rootIndex root different) = root := by
  unfold embedRoot rootIndex
  rw [FiniteDeletion.embed_index]
  exact spec.old_normalizeRoot root

theorem rootIndex_embedRoot (spec : ExogenousDeletionSpec model)
    (root : Fin spec.retainedCount) :
    spec.rootIndex (spec.embedRoot root) (spec.embedRoot_ne_deleted root) =
      root := by
  change FiniteDeletion.index spec.source
      (FiniteDeletion.embed spec.source root) _ = root
  apply FiniteDeletion.embed_injective spec.source
  rw [FiniteDeletion.embed_index]

/-- The latent family after removing the unused source. -/
def reducedLatent (spec : ExogenousDeletionSpec model) : LatentExtension S where
  count := spec.retainedCount
  Value := fun root => model.latent.Value (spec.embedRoot root)
  valueEnumeration := fun root =>
    model.latent.valueEnumeration (spec.embedRoot root)
  value_complete := fun root =>
    model.latent.value_complete (spec.embedRoot root)
  valueDecidableEq := fun root =>
    model.latent.valueDecidableEq (spec.embedRoot root)
  incident := fun root child => model.latent.incident (spec.embedRoot root) child

/-- Marginalize a full latent assignment to the retained roots. -/
def restrictLatentAssignment (spec : ExogenousDeletionSpec model)
    (assignment : model.latent.Assignment) : spec.reducedLatent.Assignment :=
  fun root => assignment (spec.embedRoot root)

/-- Reconstruct the old latent input tuple.  The deleted branch is impossible
because an input proof would contradict `unused`. -/
def oldLatentInputs (spec : ExogenousDeletionSpec model)
    {child : Fin S.count} (inputs : spec.reducedLatent.Inputs child) :
    model.latent.Inputs child :=
  fun root incident => by
    by_cases different : root ≠ spec.deletedRoot
    · let reducedRoot := spec.rootIndex root different
      let coordinateEqual := spec.embedRoot_rootIndex root different
      exact cast (congrArg model.latent.Value coordinateEqual)
        (inputs reducedRoot (by
          change model.latent.incident (spec.embedRoot reducedRoot) child = true
          rw [coordinateEqual]
          exact incident))
    · have equal : root = spec.deletedRoot := by
        cases decEq root spec.deletedRoot with
        | isTrue equal => exact equal
        | isFalse notEqual => exact (different notEqual).elim
      subst root
      have impossible := spec.unused child
      change model.latent.incident spec.deletedRoot child = false at impossible
      rw [incident] at impossible
      contradiction

/-- Extend retained coordinate events by the sure event at the deleted root. -/
def liftLatentEvents (spec : ExogenousDeletionSpec model)
    (events : (root : Fin spec.retainedCount) ->
      model.latent.Value (spec.embedRoot root) -> Bool)
    (root : Fin model.latent.count) : model.latent.Value root -> Bool :=
  fun value => if different : root ≠ spec.deletedRoot then
    events (spec.rootIndex root different)
      (cast (congrArg model.latent.Value
        (spec.embedRoot_rootIndex root different).symm) value)
  else true

theorem liftLatentEvents_embed (spec : ExogenousDeletionSpec model)
    (events : (root : Fin spec.retainedCount) ->
      model.latent.Value (spec.embedRoot root) -> Bool)
    (root : Fin spec.retainedCount)
    (value : model.latent.Value (spec.embedRoot root)) :
    spec.liftLatentEvents events (spec.embedRoot root) value =
      events root value := by
  unfold liftLatentEvents
  rw [dif_pos (spec.embedRoot_ne_deleted root)]
  let reducedRoot := spec.rootIndex (spec.embedRoot root)
    (spec.embedRoot_ne_deleted root)
  have indexEqual : reducedRoot = root := spec.rootIndex_embedRoot root
  exact dependent_event_apply_cast
    (fun index => model.latent.Value (spec.embedRoot index))
    indexEqual events value

theorem liftLatentEvents_deleted (spec : ExogenousDeletionSpec model)
    (events : (root : Fin spec.retainedCount) ->
      model.latent.Value (spec.embedRoot root) -> Bool)
    (value : model.latent.Value spec.deletedRoot) :
    spec.liftLatentEvents events spec.deletedRoot value = true := by
  simp [liftLatentEvents]

theorem liftLatentEvents_rectangularEvent
    (spec : ExogenousDeletionSpec model)
    (events : (root : Fin spec.retainedCount) ->
      model.latent.Value (spec.embedRoot root) -> Bool)
    (assignment : model.latent.Assignment) :
    model.latent.rectangularEvent (spec.liftLatentEvents events) assignment =
      spec.reducedLatent.rectangularEvent events
        (spec.restrictLatentAssignment assignment) := by
  apply Bool.eq_iff_iff.mpr
  rw [LatentExtension.rectangularEvent,
    LatentExtension.rectangularEvent,
    FiniteProduct.rectangularEvent_eq_true_iff,
    FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro all root
    have selected := all (spec.embedRoot root)
    simpa [restrictLatentAssignment,
      spec.liftLatentEvents_embed events root] using selected
  · intro all root
    by_cases different : root ≠ spec.deletedRoot
    · let reducedRoot := spec.rootIndex root different
      let coordinateEqual := spec.embedRoot_rootIndex root different
      have selected := all reducedRoot
      have valueEqual :
          cast (congrArg model.latent.Value coordinateEqual.symm)
              (assignment root) =
            assignment (spec.embedRoot reducedRoot) :=
        cast_dependent_apply_eq model.latent.Value coordinateEqual assignment
      simpa [liftLatentEvents, different, reducedRoot, coordinateEqual,
        valueEqual] using selected
    · simp [liftLatentEvents, different]

def reducedFactor (spec : ExogenousDeletionSpec model)
    (root : Fin spec.reducedLatent.count) :
    FiniteProbRecord (spec.reducedLatent.Value root) :=
  model.factor (spec.embedRoot root)

def reducedPrior (spec : ExogenousDeletionSpec model) :
    FiniteProbRecord spec.reducedLatent.Assignment :=
  model.prior.map spec.restrictLatentAssignment

theorem deletedFactor_probVal_true (spec : ExogenousDeletionSpec model) :
    QProb.Equiv
      ((model.factor spec.deletedRoot).probVal (fun _ => true)) QProb.one := by
  simp only [QProb.Equiv, FiniteProbRecord.probVal, QProb.one,
    Nat.mul_one, Nat.one_mul]
  rw [← (model.factor spec.deletedRoot).total_mass]
  exact FiniteProbRecord.eventMass_top _

theorem liftLatentEvents_qProduct (spec : ExogenousDeletionSpec model)
    (events : (root : Fin spec.retainedCount) ->
      model.latent.Value (spec.embedRoot root) -> Bool) :
    QProb.Equiv
      (FiniteProduct.qProduct model.latent.count (fun root =>
        (model.factor root).probVal (spec.liftLatentEvents events root)))
      (FiniteProduct.qProduct spec.retainedCount (fun root =>
        (spec.reducedFactor root).probVal (events root))) := by
  let oldValues : Fin model.latent.count -> QProb := fun root =>
    (model.factor root).probVal (spec.liftLatentEvents events root)
  let normalizedValues : Fin (spec.retainedCount + 1) -> QProb := fun root =>
    oldValues (spec.oldRoot root)
  have normalized := qProduct_cast spec.count_eq oldValues
  have deletedOne : QProb.Equiv (normalizedValues spec.source) QProb.one := by
    change QProb.Equiv
      ((model.factor spec.deletedRoot).probVal
        (spec.liftLatentEvents events spec.deletedRoot)) QProb.one
    exact QProb.equiv_trans
      (FiniteProbRecord.probVal_congr _ _ (fun _ => true)
        (fun value => spec.liftLatentEvents_deleted events value))
      spec.deletedFactor_probVal_true
  have deletedProduct := FiniteDeletion.qProduct_delete spec.source
    normalizedValues deletedOne
  exact QProb.equiv_trans normalized
    (QProb.equiv_trans deletedProduct
      (FiniteProduct.qProduct_congr spec.retainedCount (fun root => by
        change QProb.Equiv
          ((model.factor (spec.embedRoot root)).probVal
            (spec.liftLatentEvents events (spec.embedRoot root)))
          ((model.factor (spec.embedRoot root)).probVal (events root))
        exact FiniteProbRecord.probVal_congr _ _ _
          (fun value => spec.liftLatentEvents_embed events root value))))

theorem reducedProductLaw (spec : ExogenousDeletionSpec model)
    (events : (root : Fin spec.reducedLatent.count) ->
      spec.reducedLatent.Value root -> Bool) :
    QProb.Equiv
      (spec.reducedPrior.probVal
        (spec.reducedLatent.rectangularEvent events))
      (FiniteProduct.qProduct spec.reducedLatent.count (fun root =>
        (spec.reducedFactor root).probVal (events root))) := by
  have mapped := FiniteProbRecord.map_probVal model.prior
    spec.restrictLatentAssignment
    (spec.reducedLatent.rectangularEvent events)
  have eventCongruence := FiniteProbRecord.probVal_congr model.prior _ _
    (fun assignment =>
      (spec.liftLatentEvents_rectangularEvent events assignment).symm)
  exact QProb.equiv_trans mapped
    (QProb.equiv_trans eventCongruence
      (QProb.equiv_trans (model.product_law (spec.liftLatentEvents events))
        (spec.liftLatentEvents_qProduct events)))

/-- The exact model obtained by marginalizing the unused latent coordinate. -/
def reduceModel (spec : ExogenousDeletionSpec model) : ExactModel S where
  latent := spec.reducedLatent
  factor := spec.reducedFactor
  prior := spec.reducedPrior
  product_law := spec.reducedProductLaw
  mechanism := fun child parents inputs =>
    model.mechanism child parents (spec.oldLatentInputs inputs)

theorem oldLatentInputs_restrict (spec : ExogenousDeletionSpec model)
    {child : Fin S.count} (assignment : model.latent.Assignment) :
    spec.oldLatentInputs
        (fun root (_ : spec.reducedLatent.incident root child = true) =>
          spec.restrictLatentAssignment assignment root) =
      (fun root (_ : model.latent.incident root child = true) =>
        assignment root) := by
  funext root incident
  by_cases different : root ≠ spec.deletedRoot
  · unfold oldLatentInputs
    rw [dif_pos different]
    let coordinateEqual := spec.embedRoot_rootIndex root different
    exact (dependent_apply_eq_cast model.latent.Value coordinateEqual
      assignment).symm
  · have equal : root = spec.deletedRoot := by
      cases decEq root spec.deletedRoot with
      | isTrue equal => exact equal
      | isFalse notEqual => exact (different notEqual).elim
    subst root
    have impossible := spec.unused child
    change model.latent.incident spec.deletedRoot child = false at impossible
    rw [incident] at impossible
    contradiction

/-- Deleting an unused latent root leaves every recursive equation unchanged. -/
theorem reduceModel_evalNodeUnder (spec : ExogenousDeletionSpec model)
    (intervention : HardIntervention S)
    (assignment : model.latent.Assignment) (child : Fin S.count) :
    model.evalNodeUnder intervention.value assignment child =
      spec.reduceModel.evalNodeUnder intervention.value
        (spec.restrictLatentAssignment assignment) child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : intervention.value child with
  | some value => simp
  | none =>
      simp only [reduceModel]
      rw [spec.oldLatentInputs_restrict assignment]
      apply congrArg (fun parents =>
        model.mechanism child parents (fun root _ => assignment root))
      funext parent edge
      exact spec.reduceModel_evalNodeUnder intervention assignment parent
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

theorem reduceModel_evalUnder (spec : ExogenousDeletionSpec model)
    (intervention : HardIntervention S)
    (assignment : model.latent.Assignment) :
    model.evalUnder intervention.value assignment =
      spec.reduceModel.evalUnder intervention.value
        (spec.restrictLatentAssignment assignment) := by
  funext child
  exact spec.reduceModel_evalNodeUnder intervention assignment child

theorem reduceModel_interventionalValue (spec : ExogenousDeletionSpec model)
    (intervention : HardIntervention S) (event : S.Assignment -> Bool) :
    QProb.Equiv (model.interventionalValue intervention.value event)
      (spec.reduceModel.interventionalValue intervention.value event) := by
  exact QProb.equiv_trans
    (model.interventionalValue_eq intervention.value event)
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _
        (fun assignment => congrArg event
          (spec.reduceModel_evalUnder intervention assignment)))
      (QProb.equiv_trans
        (QProb.equiv_symm
          (FiniteProbRecord.map_probVal model.prior
            spec.restrictLatentAssignment
            (fun assignment => event
              (spec.reduceModel.evalUnder intervention.value assignment))))
        (QProb.equiv_symm
          (spec.reduceModel.interventionalValue_eq intervention.value event))))

theorem reduceModel_observationalValue (spec : ExogenousDeletionSpec model)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (model.observationalValue event)
      (spec.reduceModel.observationalValue event) := by
  simpa [FiniteLatentSCM.observationalValue] using
    spec.reduceModel_interventionalValue (HardIntervention.empty S) event

theorem reducedLatent_canonical (spec : ExogenousDeletionSpec model)
    (canonical : model.IsCanonicalSemiMarkovian) :
    spec.reduceModel.IsCanonicalSemiMarkovian := by
  intro root i j k hi hj hk
  exact canonical (spec.embedRoot root) i j k hi hj hk

theorem reduceModel_observedGraph (spec : ExogenousDeletionSpec model)
    (left right : Fin S.count) :
    spec.reduceModel.observedGraph.bidirected left right =
      model.observedGraph.bidirected left right := by
  unfold FiniteLatentSCM.observedGraph LatentExtension.observedGraph
    LatentExtension.projectedBidirected
  apply congrArg (fun projected => !(Nat.beq left.val right.val) && projected)
  let predicate : Fin model.latent.count -> Bool := fun root =>
    model.latent.incident root left && model.latent.incident root right
  let normalized : Fin (spec.retainedCount + 1) -> Bool := fun root =>
    predicate (spec.oldRoot root)
  have normalizedEquality := finAny_cast spec.count_eq predicate
  have deletedFalse : normalized spec.source = false := by
    change (model.latent.incident (spec.oldRoot spec.source) left &&
        model.latent.incident (spec.oldRoot spec.source) right) = false
    have unusedLeft := spec.unused left
    change model.latent.incident (spec.oldRoot spec.source) left = false
      at unusedLeft
    rw [unusedLeft]
    rfl
  have deletedEquality := FiniteDeletion.finAny_delete spec.source
    normalized deletedFalse
  have selectedMatches :
      finAny spec.retainedCount (fun index =>
        normalized (FiniteDeletion.embed spec.source index)) =
      finAny spec.reduceModel.latent.count (fun root =>
        spec.reduceModel.latent.incident root left &&
          spec.reduceModel.latent.incident root right) := by
    rfl
  exact Eq.trans selectedMatches.symm
    (Eq.trans deletedEquality.symm normalizedEquality.symm)

theorem reduceModel_compatible (spec : ExogenousDeletionSpec model)
    (graph : ObservedGraph S) (compatible : Compatible model graph) :
    Compatible spec.reduceModel graph := by
  constructor
  · exact spec.reducedLatent_canonical compatible.1
  · intro left right
    exact Eq.trans (spec.reduceModel_observedGraph left right)
      (compatible.2 left right)

/-- Delete an unused exogenous source from both the prior and the current
epistemic belief, while retaining the observed intervention. -/
def deleteRecord {record : CausalEpistemicRecord S}
    (spec : ExogenousDeletionSpec record.model) : CausalEpistemicRecord S where
  model := spec.reduceModel
  belief := record.belief.map spec.restrictLatentAssignment
  intervention := record.intervention
  stack := record.executedStack .forgetUnusedExogenous

theorem deleteRecord_observedValue
    (record : CausalEpistemicRecord S)
    (spec : ExogenousDeletionSpec record.model)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (record.observedValue event)
      (spec.deleteRecord.observedValue event) := by
  unfold CausalEpistemicRecord.observedValue CausalEpistemicRecord.observedDist
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal record.belief
      (record.model.evalUnder record.intervention.value) event)
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr record.belief _ _
        (fun assignment => congrArg event
          (spec.reduceModel_evalUnder record.intervention assignment)))
      (QProb.equiv_trans
        (QProb.equiv_symm
          (FiniteProbRecord.map_probVal record.belief
            spec.restrictLatentAssignment
            (fun assignment => event
              (spec.reduceModel.evalUnder record.intervention.value
                assignment))))
        (QProb.equiv_symm
          (FiniteProbRecord.map_probVal
            (record.belief.map spec.restrictLatentAssignment)
            (spec.reduceModel.evalUnder record.intervention.value) event))))

end ExogenousDeletionSpec

end Causality
end Thesis
