import Thesis.Causality.ConservativeLearning

namespace Thesis
namespace Causality

open Probability
open CausalEpistemicRecord

/-!
Constructive deletion of an observed directed sink, with shared finite-deletion
helpers used by unused-exogenous deletion.

Incoming directed edges are allowed because they occur only in the deleted
equation. Unused-exogenous deletion lives in `Forgetting.ExogenousRoot`. The
model-extension argument needed for two-way observed identifiability is
isolated in `Thesis.Causality.Forgetting.Identification` so structural-edit
clients do not import it merely to construct a deletion.
-/

theorem dependent_apply_eq_cast {n : Nat} (Value : Fin n -> Type u)
    {left right : Fin n} (equal : left = right)
    (values : (node : Fin n) -> Value node) :
    values right = cast (congrArg Value equal) (values left) := by
  cases equal
  rfl

private theorem dependent_equality_transport {n : Nat}
    (Value : Fin n -> Type u) {left right : Fin n} (equal : left = right)
    (first second : (node : Fin n) -> Value node)
    (atLeft : first left = second left) : first right = second right := by
  cases equal
  exact atLeft

theorem cast_dependent_apply_eq {n : Nat} (Value : Fin n -> Type u)
    {left right : Fin n} (equal : left = right)
    (values : (node : Fin n) -> Value node) :
    cast (congrArg Value equal.symm) (values right) = values left := by
  cases equal
  rfl

theorem dependent_event_apply_cast {n : Nat}
    (Value : Fin n -> Type u) {left right : Fin n} (equal : left = right)
    (events : (node : Fin n) -> Value node -> Bool) (value : Value right) :
    events left (cast (congrArg Value equal.symm) value) =
      events right value := by
  cases equal
  rfl

theorem qProduct_cast {n m : Nat} (equal : n = m)
    (values : Fin n -> QProb) :
    QProb.Equiv (FiniteProduct.qProduct n values)
      (FiniteProduct.qProduct m (fun index => values (Fin.cast equal.symm index))) := by
  cases equal
  exact QProb.equiv_refl _

theorem finAny_cast {n m : Nat} (equal : n = m)
    (predicate : Fin n -> Bool) :
    finAny n predicate =
      finAny m (fun index => predicate (Fin.cast equal.symm index)) := by
  cases equal
  rfl

theorem cast_record_probVal {A B : Type u} (equal : A = B)
    (record : FiniteProbRecord A) (event : A -> Bool) :
    QProb.Equiv
      ((cast (congrArg FiniteProbRecord equal) record).probVal
        (fun value => event (cast equal.symm value)))
      (record.probVal event) := by
  cases equal
  exact QProb.equiv_refl _

namespace LatentExtension

/-- A duplicate-free enumeration of all assignments of a finite latent family. -/
def assignmentEnumeration (latent : LatentExtension S) :
    List latent.Assignment :=
  deduplicate (FiniteProduct.enumeration latent.count latent.Value
    latent.valueEnumeration)

theorem assignmentEnumeration_complete (latent : LatentExtension S)
    (assignment : latent.Assignment) :
    assignment ∈ latent.assignmentEnumeration := by
  rw [assignmentEnumeration, mem_deduplicate]
  exact FiniteProduct.enumeration_complete latent.count latent.Value
    latent.valueEnumeration latent.value_complete assignment

theorem assignmentEnumeration_nodup (latent : LatentExtension S) :
    latent.assignmentEnumeration.Nodup :=
  deduplicate_nodup _

def assignmentSingletonEvents (latent : LatentExtension S)
    (assignment : latent.Assignment) :
    (source : Fin latent.count) -> latent.Value source -> Bool :=
  fun source value => decide (value = assignment source)

theorem rectangularEvent_assignmentSingletonEvents
    (latent : LatentExtension S) (assignment : latent.Assignment) :
    latent.rectangularEvent
        (latent.assignmentSingletonEvents assignment) =
      FiniteProbRecord.singletonEvent assignment := by
  funext candidate
  apply Bool.eq_iff_iff.mpr
  change
    FiniteProduct.rectangularEvent latent.count latent.Value
        (latent.assignmentSingletonEvents assignment) candidate = true <->
      FiniteProbRecord.singletonEvent assignment candidate = true
  rw [FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro equal
    have same : candidate = assignment := by
      funext source
      exact of_decide_eq_true (equal source)
    simp [FiniteProbRecord.singletonEvent, same]
  · intro equal source
    have same : candidate = assignment := by
      simpa [FiniteProbRecord.singletonEvent] using equal
    subst candidate
    simp [assignmentSingletonEvents]

end LatentExtension

namespace FiniteLatentSCM

/-- The supplied product law determines the complete finite latent prior. -/
theorem prior_probVal_canonicalProduct (model : ExactModel S)
    (event : model.latent.Assignment -> Bool) :
    QProb.Equiv (model.prior.probVal event)
      ((FiniteProduct.record model.latent.count model.latent.Value
        model.factor).probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons
    model.prior
    (FiniteProduct.record model.latent.count model.latent.Value model.factor)
    model.latent.assignmentEnumeration
    model.latent.assignmentEnumeration_nodup
    model.latent.assignmentEnumeration_complete
  intro assignment
  let events := model.latent.assignmentSingletonEvents assignment
  have source := model.product_law events
  have canonical := FiniteProduct.record_rectangular_probVal
    model.latent.count model.latent.Value model.factor events
  rw [model.latent.rectangularEvent_assignmentSingletonEvents assignment]
    at source
  change QProb.Equiv
    ((FiniteProduct.record model.latent.count model.latent.Value
      model.factor).probVal (model.latent.rectangularEvent events))
    (FiniteProduct.qProduct model.latent.count
      (fun i => (model.factor i).probVal (events i))) at canonical
  rw [model.latent.rectangularEvent_assignmentSingletonEvents assignment]
    at canonical
  exact QProb.equiv_trans source (QProb.equiv_symm canonical)

end FiniteLatentSCM

def addOnes (n m : Nat) (values : Fin n -> QProb) :
    Fin (n + m) -> QProb :=
  Fin.addCases (motive := fun _ => QProb) values
    (fun _ : Fin m => QProb.one)

theorem qProduct_add_ones (n m : Nat) (values : Fin n -> QProb) :
    QProb.Equiv
      (FiniteProduct.qProduct (n + m) (addOnes n m values))
      (FiniteProduct.qProduct n values) := by
  induction m with
  | zero =>
      have empty : addOnes n 0 values = values := by
        funext i
        refine Fin.addCases (motive := fun i : Fin (n + 0) =>
            addOnes n 0 values i = values i)
          (fun old => by
            simpa [addOnes] using
              (Fin.addCases_left
                (motive := fun _ : Fin (n + 0) => QProb)
                (left := fun old => values old)
                (right := fun _ : Fin 0 => QProb.one) old))
          (fun impossible => Fin.elim0 impossible) i
      simpa [empty] using
        QProb.equiv_refl (FiniteProduct.qProduct n values)
  | succ m ih =>
      have hPrefix :
          (fun i : Fin (n + m) =>
            addOnes n (m + 1) values i.castSucc) =
            addOnes n m values := by
        funext i
        refine Fin.addCases (motive := fun i : Fin (n + m) =>
            addOnes n (m + 1) values i.castSucc =
              addOnes n m values i)
          (fun old => by
            change addOnes n (m + 1) values
                (Fin.castAdd m old).castSucc =
              addOnes n m values (Fin.castAdd m old)
            have coordinate :
                (Fin.castAdd m old).castSucc =
                  Fin.castAdd (m + 1) old := Fin.ext rfl
            rw [coordinate]
            simp only [addOnes, Fin.addCases_left])
          (fun added => by
            change addOnes n (m + 1) values
                (Fin.natAdd n added).castSucc =
              addOnes n m values (Fin.natAdd n added)
            rw [← Fin.natAdd_castSucc]
            simp only [addOnes, Fin.addCases_right]) i
      have hLast :
          addOnes n (m + 1) values (Fin.last (n + m)) = QProb.one := by
        change Fin.addCases (motive := fun _ => QProb) values
            (fun _ : Fin (m + 1) => QProb.one) (Fin.last (n + m)) =
          QProb.one
        have coordinate :
            Fin.last (n + m) = Fin.natAdd n (Fin.last m) := Fin.ext rfl
        rw [coordinate]
        exact Fin.addCases_right (motive := fun _ => QProb)
          (left := values) (right := fun _ : Fin (m + 1) => QProb.one)
          (Fin.last m)
      simp only [Nat.add_succ]
      change QProb.Equiv
        (QProb.mul
          (addOnes n (m + 1) values (Fin.last (n + m)))
          (FiniteProduct.qProduct (n + m)
            (fun i => addOnes n (m + 1) values i.castSucc)))
        (FiniteProduct.qProduct n values)
      rw [hLast, hPrefix]
      exact QProb.equiv_trans
        (QProb.mul_congr (QProb.equiv_refl QProb.one) ih) (by
          simp [QProb.Equiv, QProb.mul, QProb.one])

namespace FiniteDeletion

/-- The order-preserving embedding obtained by deleting one finite coordinate. -/
def embed {n : Nat} (deleted : Fin (n + 1)) (index : Fin n) :
    Fin (n + 1) :=
  if before : index.val < deleted.val then
    ⟨index.val, Nat.lt_trans before deleted.isLt⟩
  else
    ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩

@[simp] theorem embed_deleted_last {n : Nat} (index : Fin n) :
    embed (Fin.last n) index = index.castSucc := by
  apply Fin.ext
  simp [embed]

@[simp] theorem embed_deleted_castSucc {n : Nat} (deleted : Fin (n + 1)) :
    embed deleted.castSucc (Fin.last n) = Fin.last (n + 1) := by
  have notBefore : ¬n < deleted.val := by omega
  apply Fin.ext
  simp [embed, notBefore]

@[simp] theorem embed_deleted_castSucc_prefix {n : Nat}
    (deleted : Fin (n + 1)) (index : Fin n) :
    embed deleted.castSucc index.castSucc = (embed deleted index).castSucc := by
  apply Fin.ext
  by_cases before : index.val < deleted.val <;> simp [embed, before]

theorem embed_ne_deleted {n : Nat} (deleted : Fin (n + 1))
    (index : Fin n) : embed deleted index ≠ deleted := by
  intro equal
  have values := congrArg Fin.val equal
  by_cases before : index.val < deleted.val
  · simp [embed, before] at values
    omega
  · simp [embed, before] at values
    omega

theorem embed_injective {n : Nat} (deleted : Fin (n + 1)) :
    Function.Injective (embed deleted) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  by_cases leftBefore : left.val < deleted.val
  · by_cases rightBefore : right.val < deleted.val
    · simpa [embed, leftBefore, rightBefore] using values
    · simp [embed, leftBefore, rightBefore] at values
      omega
  · by_cases rightBefore : right.val < deleted.val
    · simp [embed, leftBefore, rightBefore] at values
      omega
    · simp [embed, leftBefore, rightBefore] at values
      omega

/-- Constructively recover the reduced coordinate of every retained index. -/
def index {n : Nat} (deleted root : Fin (n + 1))
    (different : root ≠ deleted) : Fin n :=
  if before : root.val < deleted.val then
    ⟨root.val, by omega⟩
  else
    ⟨root.val - 1, by
      have unequal : root.val ≠ deleted.val := by
        intro equal
        exact different (Fin.ext equal)
      omega⟩

@[simp] theorem index_deleted_last_castSucc {n : Nat}
    (root : Fin (n + 1))
    (different : root.castSucc ≠ Fin.last (n + 1)) :
    index (Fin.last (n + 1)) root.castSucc different = root := by
  apply Fin.ext
  simp [index]

@[simp] theorem index_deleted_castSucc_last {n : Nat}
    (deleted : Fin (n + 1))
    (different : Fin.last (n + 1) ≠ deleted.castSucc) :
    index deleted.castSucc (Fin.last (n + 1)) different = Fin.last n := by
  have notBefore : ¬n + 1 < deleted.val := by omega
  apply Fin.ext
  simp [index, notBefore]

@[simp] theorem index_deleted_castSucc_prefix {n : Nat}
    (deleted root : Fin (n + 1))
    (different : root.castSucc ≠ deleted.castSucc) :
    index deleted.castSucc root.castSucc different =
      (index deleted root (fun equal =>
        different (Fin.castSucc_inj.mpr equal))).castSucc := by
  apply Fin.ext
  by_cases before : root.val < deleted.val <;> simp [index, before]

theorem embed_index {n : Nat} (deleted root : Fin (n + 1))
    (different : root ≠ deleted) :
    embed deleted (index deleted root different) = root := by
  have unequal : root.val ≠ deleted.val := by
    intro equal
    exact different (Fin.ext equal)
  apply Fin.ext
  by_cases before : root.val < deleted.val
  · simp [index, before, embed]
  · have deletedBefore : deleted.val < root.val := by omega
    have shiftedNotBefore : ¬root.val - 1 < deleted.val := by omega
    simp [index, before, embed, shiftedNotBefore]
    omega

/-- Removing a factor equal to one leaves a finite probability product intact. -/
theorem qProduct_delete {n : Nat} (deleted : Fin (n + 1))
    (values : Fin (n + 1) -> QProb)
    (deletedOne : QProb.Equiv (values deleted) QProb.one) :
    QProb.Equiv (FiniteProduct.qProduct (n + 1) values)
      (FiniteProduct.qProduct n (fun index => values (embed deleted index))) := by
  induction n with
  | zero =>
      have same : deleted = Fin.last 0 := Fin.ext (by omega)
      subst deleted
      simpa [FiniteProduct.qProduct, QProb.Equiv, QProb.mul, QProb.one] using
        deletedOne
  | succ n ih =>
      refine Fin.lastCases
        (motive := fun deleted : Fin (n + 2) =>
          QProb.Equiv (values deleted) QProb.one ->
            QProb.Equiv (FiniteProduct.qProduct (n + 2) values)
              (FiniteProduct.qProduct (n + 1)
                (fun index => values (embed deleted index))))
        (fun deletedOne => by
          have retainedFamily :
              (fun index : Fin (n + 1) =>
                values (embed (Fin.last (n + 1)) index)) =
              (fun index => values index.castSucc) := by
            funext index
            rw [embed_deleted_last]
          rw [retainedFamily]
          rw [show FiniteProduct.qProduct (n + 2) values =
              QProb.mul (values (Fin.last (n + 1)))
                (FiniteProduct.qProduct (n + 1)
                  (fun index => values index.castSucc)) by rfl]
          exact QProb.equiv_trans
            (QProb.mul_congr deletedOne
              (QProb.equiv_refl
                (FiniteProduct.qProduct (n + 1)
                  (fun index => values index.castSucc))))
            (by simp [QProb.Equiv, QProb.mul, QProb.one]))
        (fun deletedPrefix deletedOne => by
          change QProb.Equiv
            (QProb.mul (values (Fin.last (n + 1)))
              (FiniteProduct.qProduct (n + 1)
                (fun index => values index.castSucc)))
            (QProb.mul
              (values (embed deletedPrefix.castSucc (Fin.last n)))
              (FiniteProduct.qProduct n (fun index =>
                values (embed deletedPrefix.castSucc index.castSucc))))
          simpa only [embed_deleted_castSucc,
              embed_deleted_castSucc_prefix] using
            QProb.mul_congr
              (QProb.equiv_refl (values (Fin.last (n + 1))))
              (ih deletedPrefix (fun index => values index.castSucc)
                deletedOne))
        deleted deletedOne

theorem finAny_delete {n : Nat} (deleted : Fin (n + 1))
    (predicate : Fin (n + 1) -> Bool)
    (deletedFalse : predicate deleted = false) :
    finAny (n + 1) predicate =
      finAny n (fun index => predicate (embed deleted index)) := by
  apply Bool.eq_iff_iff.mpr
  rw [finAny_eq_true_iff, finAny_eq_true_iff]
  constructor
  · rintro ⟨root, selected⟩
    have different : root ≠ deleted := by
      intro equal
      subst root
      rw [deletedFalse] at selected
      contradiction
    exact ⟨index deleted root different, by
      rw [embed_index deleted root different]
      exact selected⟩
  · rintro ⟨index, selected⟩
    exact ⟨embed deleted index, selected⟩

end FiniteDeletion

theorem finAny_add {n m : Nat} (left : Fin n -> Bool)
    (right : Fin m -> Bool) :
    finAny (n + m)
        (Fin.addCases (motive := fun _ => Bool) left right) =
      (finAny n left || finAny m right) := by
  apply Bool.eq_iff_iff.mpr
  rw [finAny_eq_true_iff, Bool.or_eq_true]
  constructor
  · rintro ⟨source, selected⟩
    exact Fin.addCases
      (motive := fun source : Fin (n + m) =>
        Fin.addCases (motive := fun _ => Bool) left right source = true ->
          finAny n left = true ∨ finAny m right = true)
      (fun old selected =>
        Or.inl (finAny_eq_true_of left old (by
          simpa only [Fin.addCases_left] using selected)))
      (fun added selected =>
        Or.inr (finAny_eq_true_of right added (by
          simpa only [Fin.addCases_right] using selected))) source selected
  · intro selected
    rcases selected with old | added
    · rcases (finAny_eq_true_iff left).mp old with ⟨source, sourceSelected⟩
      exact ⟨Fin.castAdd m source, by
        simpa only [Fin.addCases_left] using sourceSelected⟩
    · rcases (finAny_eq_true_iff right).mp added with ⟨source, sourceSelected⟩
      exact ⟨Fin.natAdd n source, by
        simpa only [Fin.addCases_right] using sourceSelected⟩

/-! ## Observed directed-sink deletion -/

/-- Proof-carrying deletion data for one observed directed sink. -/
structure ObservedDeletionSpec (S : ObservedSignature) where
  node : Fin S.count
  noOutgoing : forall child, S.directed node child = false

namespace ObservedDeletionSpec

/-- The old observed coordinates retained after deletion. -/
def retained (spec : ObservedDeletionSpec S) : NodeSet S :=
  fun node => decide (node ≠ spec.node)

theorem retained_eq_true_iff (spec : ObservedDeletionSpec S)
    (node : Fin S.count) :
    spec.retained node = true <-> node ≠ spec.node := by
  simp [retained]

theorem retained_embed_ne (spec : ObservedDeletionSpec S)
    (node : Fin (selectedNodeCount spec.retained)) :
    selectedEmbed spec.retained node ≠ spec.node :=
  (spec.retained_eq_true_iff _).mp (selectedEmbed_mem spec.retained node)

/-- The constructive retained index of an old coordinate distinct from the sink. -/
def retainedIndex (spec : ObservedDeletionSpec S) (node : Fin S.count)
    (retained : node ≠ spec.node) :
    Fin (selectedNodeCount spec.retained) :=
  letI : BEq (Fin S.count) := instBEqOfDecidableEq
  letI : LawfulBEq (Fin S.count) := instLawfulBEq
  let finEquivBEq : EquivBEq (Fin S.count) :=
    equivBEq_of_iff_apply_eq (fun index => index)
      (fun _ _ => beq_iff_eq)
  let nodes := selectedNodeList S spec.retained
  have member : node ∈ nodes :=
    (mem_selectedNodeList spec.retained node).mpr
      ((spec.retained_eq_true_iff node).mpr retained)
  ⟨nodes.idxOf node,
    @List.idxOf_lt_length_of_mem (Fin S.count) node
      instBEqOfDecidableEq finEquivBEq nodes member⟩

theorem selectedEmbed_retainedIndex (spec : ObservedDeletionSpec S)
    (node : Fin S.count) (retained : node ≠ spec.node) :
    selectedEmbed spec.retained (spec.retainedIndex node retained) = node := by
  letI : BEq (Fin S.count) := instBEqOfDecidableEq
  letI : LawfulBEq (Fin S.count) := instLawfulBEq
  have member : node ∈ selectedNodeList S spec.retained :=
    (mem_selectedNodeList spec.retained node).mpr
      ((spec.retained_eq_true_iff node).mpr retained)
  apply beq_iff_eq.mp
  change
    ((selectedNodeList S spec.retained).get
      (spec.retainedIndex node retained) == node) = true
  simpa [List.get_eq_getElem, selectedEmbed, retainedIndex, List.idxOf] using
    (List.findIdx_getElem
      (p := fun value => value == node)
      (xs := selectedNodeList S spec.retained)
      (w := (spec.retainedIndex node retained).isLt))

theorem retainedIndex_selectedEmbed (spec : ObservedDeletionSpec S)
    (node : Fin (selectedNodeCount spec.retained)) :
    spec.retainedIndex (selectedEmbed spec.retained node)
        (spec.retained_embed_ne node) = node := by
  apply selectedEmbed_inj spec.retained
  exact spec.selectedEmbed_retainedIndex _ _

/-- The induced ordered signature after removing the sink. -/
def signature (spec : ObservedDeletionSpec S) : ObservedSignature where
  count := selectedNodeCount spec.retained
  Value := fun node => S.Value (selectedEmbed spec.retained node)
  valueEnumeration := fun node =>
    S.valueEnumeration (selectedEmbed spec.retained node)
  value_complete := fun node =>
    S.value_complete (selectedEmbed spec.retained node)
  value_nodup := fun node =>
    S.value_nodup (selectedEmbed spec.retained node)
  defaultValue := fun node =>
    S.defaultValue (selectedEmbed spec.retained node)
  valueDecidableEq := fun node =>
    S.valueDecidableEq (selectedEmbed spec.retained node)
  directed := fun parent child =>
    S.directed (selectedEmbed spec.retained parent)
      (selectedEmbed spec.retained child)
  directed_earlier := fun edge =>
    selectedEmbed_lt_reflect spec.retained (S.directed_earlier edge)

@[simp] theorem signature_count (spec : ObservedDeletionSpec S) :
    spec.signature.count = selectedNodeCount spec.retained :=
  rfl

@[simp] theorem signature_directed (spec : ObservedDeletionSpec S)
    (parent child : Fin spec.signature.count) :
    spec.signature.directed parent child =
      S.directed (selectedEmbed spec.retained parent)
        (selectedEmbed spec.retained child) :=
  rfl

/-- Restrict an old observed assignment to the retained coordinates. -/
def restrictAssignment (spec : ObservedDeletionSpec S)
    (assignment : S.Assignment) : spec.signature.Assignment :=
  fun node => assignment (selectedEmbed spec.retained node)

/-- Restrict a hard intervention to the retained coordinates. -/
def restrictIntervention (spec : ObservedDeletionSpec S)
    (intervention : HardIntervention S) : HardIntervention spec.signature where
  value := fun node => intervention.value (selectedEmbed spec.retained node)

/-- Lift a retained event to a cylinder event on the original signature. -/
def liftEvent (spec : ObservedDeletionSpec S)
    (event : spec.signature.Assignment -> Bool) : S.Assignment -> Bool :=
  fun assignment => event (spec.restrictAssignment assignment)

/-- Lift a retained node set to the original signature, excluding the sink. -/
def liftNodeSet (spec : ObservedDeletionSpec S)
    (nodes : NodeSet spec.signature) : NodeSet S :=
  fun node => if retained : node ≠ spec.node then
    nodes (spec.retainedIndex node retained)
  else false

@[simp] theorem liftNodeSet_deleted (spec : ObservedDeletionSpec S)
    (nodes : NodeSet spec.signature) :
    spec.liftNodeSet nodes spec.node = false := by
  simp [liftNodeSet]

@[simp] theorem liftNodeSet_embed (spec : ObservedDeletionSpec S)
    (nodes : NodeSet spec.signature) (node : Fin spec.signature.count) :
    spec.liftNodeSet nodes (selectedEmbed spec.retained node) = nodes node := by
  simp [liftNodeSet, spec.retained_embed_ne,
    spec.retainedIndex_selectedEmbed]

/-- Restrict latent incidence to the retained observed coordinates. -/
def restrictLatent (spec : ObservedDeletionSpec S)
    (latent : LatentExtension S) : LatentExtension spec.signature where
  count := latent.count
  Value := latent.Value
  valueEnumeration := latent.valueEnumeration
  value_complete := latent.value_complete
  valueDecidableEq := latent.valueDecidableEq
  incident := fun source child =>
    latent.incident source (selectedEmbed spec.retained child)

theorem oldParent_ne_deleted (spec : ObservedDeletionSpec S)
    {child : Fin spec.signature.count} {parent : Fin S.count}
    (edge : S.directed parent (selectedEmbed spec.retained child) = true) :
    parent ≠ spec.node := by
  intro equal
  subst parent
  rw [spec.noOutgoing] at edge
  contradiction

/-- Reconstruct the original parent tuple for a retained mechanism. -/
def oldParentValues (spec : ObservedDeletionSpec S)
    {child : Fin spec.signature.count}
    (parents : spec.signature.ParentValues child) :
    S.ParentValues (selectedEmbed spec.retained child) :=
  fun parent edge =>
    let retained := spec.oldParent_ne_deleted edge
    let reducedParent := spec.retainedIndex parent retained
    let coordinateEqual :=
      spec.selectedEmbed_retainedIndex parent retained
    cast (congrArg S.Value coordinateEqual)
      (parents reducedParent (by
        change S.directed (selectedEmbed spec.retained reducedParent)
          (selectedEmbed spec.retained child) = true
        rw [coordinateEqual]
        exact edge))

def oldLatentInputs (spec : ObservedDeletionSpec S)
    (latent : LatentExtension S) {child : Fin spec.signature.count}
    (inputs : (spec.restrictLatent latent).Inputs child) :
    latent.Inputs (selectedEmbed spec.retained child) :=
  fun source incident => inputs source incident

/-- Restrict an arbitrary exact model to the induced sink-deleted subsystem. -/
def restrictModel (spec : ObservedDeletionSpec S)
    (model : ExactModel S) : ExactModel spec.signature where
  latent := spec.restrictLatent model.latent
  factor := model.factor
  prior := model.prior
  product_law := model.product_law
  mechanism := fun child parents inputs =>
    model.mechanism (selectedEmbed spec.retained child)
      (spec.oldParentValues parents)
      (spec.oldLatentInputs model.latent inputs)

@[simp] theorem restrictModel_prior (spec : ObservedDeletionSpec S)
    (model : ExactModel S) :
    (spec.restrictModel model).prior = model.prior :=
  rfl

/-- The induced observed graph after deleting the sink. -/
def restrictGraph (spec : ObservedDeletionSpec S)
    (graph : ObservedGraph S) : ObservedGraph spec.signature where
  bidirected := fun left right =>
    graph.bidirected (selectedEmbed spec.retained left)
      (selectedEmbed spec.retained right)
  bidirected_symmetric := graph.bidirected_symmetric
  bidirected_irreflexive := fun node =>
    graph.bidirected_irreflexive (selectedEmbed spec.retained node)

@[simp] theorem restrictModel_observedGraph
    (spec : ObservedDeletionSpec S) (model : ExactModel S)
    (left right : Fin spec.signature.count) :
    (spec.restrictModel model).observedGraph.bidirected left right =
      model.observedGraph.bidirected (selectedEmbed spec.retained left)
        (selectedEmbed spec.retained right) := by
  have beqPreserved :
      Nat.beq left.val right.val =
        Nat.beq (selectedEmbed spec.retained left).val
          (selectedEmbed spec.retained right).val := by
    cases original : Nat.beq left.val right.val with
    | true =>
        have same : left = right :=
          Fin.ext (Nat.eq_of_beq_eq_true original)
        subst right
        simp
    | false =>
        cases retained :
            Nat.beq (selectedEmbed spec.retained left).val
              (selectedEmbed spec.retained right).val with
        | false => rfl
        | true =>
            have sameOld : selectedEmbed spec.retained left =
                selectedEmbed spec.retained right :=
              Fin.ext (Nat.eq_of_beq_eq_true retained)
            have same : left = right := selectedEmbed_inj spec.retained sameOld
            subst right
            simp at original
  change
    (!(Nat.beq left.val right.val) &&
        finAny model.latent.count (fun source =>
          model.latent.incident source (selectedEmbed spec.retained left) &&
            model.latent.incident source
              (selectedEmbed spec.retained right))) =
      (!(Nat.beq (selectedEmbed spec.retained left).val
          (selectedEmbed spec.retained right).val) &&
        finAny model.latent.count (fun source =>
          model.latent.incident source (selectedEmbed spec.retained left) &&
            model.latent.incident source
              (selectedEmbed spec.retained right)))
  rw [beqPreserved]

theorem restrictModel_isCanonicalSemiMarkovian
    (spec : ObservedDeletionSpec S) (model : ExactModel S)
    (canonical : model.IsCanonicalSemiMarkovian) :
    (spec.restrictModel model).IsCanonicalSemiMarkovian := by
  intro source i j k hi hj hk
  rcases canonical source
      (selectedEmbed spec.retained i)
      (selectedEmbed spec.retained j)
      (selectedEmbed spec.retained k)
      hi hj hk with same | same | same
  · exact Or.inl (selectedEmbed_inj spec.retained same)
  · exact Or.inr (Or.inl (selectedEmbed_inj spec.retained same))
  · exact Or.inr (Or.inr (selectedEmbed_inj spec.retained same))

theorem restrictModel_compatible (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (graph : ObservedGraph S)
    (compatible : Compatible model graph) :
    Compatible (spec.restrictModel model) (spec.restrictGraph graph) := by
  constructor
  · exact spec.restrictModel_isCanonicalSemiMarkovian model compatible.1
  · intro i j
    exact Eq.trans (spec.restrictModel_observedGraph model i j)
      (compatible.2 (selectedEmbed spec.retained i)
        (selectedEmbed spec.retained j))

/-- Every retained recursive equation is unchanged by sink deletion. -/
theorem restrictModel_evalNodeUnder (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (intervention : HardIntervention S)
    (assignment : model.latent.Assignment)
    (child : Fin spec.signature.count) :
    model.evalNodeUnder intervention.value assignment
        (selectedEmbed spec.retained child) =
      (spec.restrictModel model).evalNodeUnder
        (spec.restrictIntervention intervention).value assignment child := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases selected : intervention.value (selectedEmbed spec.retained child) with
  | some value =>
      simp [restrictIntervention, selected]
  | none =>
      simp [restrictIntervention, selected, restrictModel]
      apply congrArg (fun parents =>
        model.mechanism (selectedEmbed spec.retained child) parents
          (fun source _ => assignment source))
      funext parent edge
      let retained := spec.oldParent_ne_deleted edge
      let reducedParent := spec.retainedIndex parent retained
      let coordinateEqual :=
        spec.selectedEmbed_retainedIndex parent retained
      have recursive := spec.restrictModel_evalNodeUnder model intervention
        assignment reducedParent
      change
        model.evalNodeUnder intervention.value assignment parent =
          cast (congrArg S.Value coordinateEqual)
            ((spec.restrictModel model).evalNodeUnder
              (spec.restrictIntervention intervention).value assignment
              reducedParent)
      calc
        model.evalNodeUnder intervention.value assignment parent =
            cast (congrArg S.Value coordinateEqual)
              (model.evalNodeUnder intervention.value assignment
                (selectedEmbed spec.retained reducedParent)) := by
          exact dependent_apply_eq_cast S.Value coordinateEqual
            (fun node =>
              model.evalNodeUnder intervention.value assignment node)
        _ = cast (congrArg S.Value coordinateEqual)
              ((spec.restrictModel model).evalNodeUnder
                (spec.restrictIntervention intervention).value assignment
                reducedParent) :=
          congrArg (cast (congrArg S.Value coordinateEqual)) recursive
termination_by child.val
decreasing_by
  apply selectedEmbed_lt_reflect spec.retained
  rw [spec.selectedEmbed_retainedIndex]
  exact S.directed_earlier edge

theorem restrictModel_evalUnder (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (intervention : HardIntervention S)
    (assignment : model.latent.Assignment) :
    spec.restrictAssignment (model.evalUnder intervention.value assignment) =
      (spec.restrictModel model).evalUnder
        (spec.restrictIntervention intervention).value assignment := by
  funext child
  exact spec.restrictModel_evalNodeUnder model intervention assignment child

theorem restrictModel_liftEvent_evalUnder (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (intervention : HardIntervention S)
    (event : spec.signature.Assignment -> Bool)
    (assignment : model.latent.Assignment) :
    spec.liftEvent event (model.evalUnder intervention.value assignment) =
      event ((spec.restrictModel model).evalUnder
        (spec.restrictIntervention intervention).value assignment) := by
  simp [liftEvent, spec.restrictModel_evalUnder model intervention assignment]

theorem restrictModel_interventionalValue (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (intervention : HardIntervention S)
    (event : spec.signature.Assignment -> Bool) :
    QProb.Equiv
      (model.interventionalValue intervention.value (spec.liftEvent event))
      ((spec.restrictModel model).interventionalValue
        (spec.restrictIntervention intervention).value event) := by
  exact QProb.equiv_trans
    (model.interventionalValue_eq intervention.value (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr model.prior _ _
        (fun assignment =>
          spec.restrictModel_liftEvent_evalUnder model intervention event
            assignment))
      (QProb.equiv_symm
        ((spec.restrictModel model).interventionalValue_eq
          (spec.restrictIntervention intervention).value event)))

theorem restrictModel_observationalValue (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (event : spec.signature.Assignment -> Bool) :
    QProb.Equiv
      (model.observationalValue (spec.liftEvent event))
      ((spec.restrictModel model).observationalValue event) := by
  have preserved := spec.restrictModel_interventionalValue model
    (HardIntervention.empty S) event
  simpa [FiniteLatentSCM.observationalValue,
    HardIntervention.empty, restrictIntervention,
    FiniteLatentSCM.noIntervention] using preserved

/-- Delete the sink from a causal epistemic record. -/
def deleteRecord (spec : ObservedDeletionSpec S)
    (record : CausalEpistemicRecord S) :
    CausalEpistemicRecord spec.signature where
  model := spec.restrictModel record.model
  belief := record.belief
  intervention := spec.restrictIntervention record.intervention
  stack := record.acrossStack .forgetUnusedEndogenous

theorem deleteRecord_observedValue (spec : ObservedDeletionSpec S)
    (record : CausalEpistemicRecord S)
    (event : spec.signature.Assignment -> Bool) :
    QProb.Equiv (record.observedValue (spec.liftEvent event))
      ((spec.deleteRecord record).observedValue event) := by
  unfold CausalEpistemicRecord.observedValue
    CausalEpistemicRecord.observedDist
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal record.belief
      (record.model.evalUnder record.intervention.value)
      (spec.liftEvent event))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr record.belief _ _
        (fun assignment =>
          spec.restrictModel_liftEvent_evalUnder record.model
            record.intervention event assignment))
      (QProb.equiv_symm
        (FiniteProbRecord.map_probVal record.belief
          ((spec.deleteRecord record).model.evalUnder
            (spec.deleteRecord record).intervention.value) event)))

theorem liftNodeSet_disjoint (spec : ObservedDeletionSpec S)
    {left right : NodeSet spec.signature}
    (disjoint : NodeSet.Disjoint left right) :
    NodeSet.Disjoint (spec.liftNodeSet left) (spec.liftNodeSet right) := by
  intro node selected
  by_cases retained : node ≠ spec.node
  · have selectedReduced :
        left (spec.retainedIndex node retained) = true := by
      simpa [liftNodeSet, retained] using selected
    simpa [liftNodeSet, retained] using
      disjoint (spec.retainedIndex node retained) selectedReduced
  · simp [liftNodeSet, retained] at selected

def liftKernel (spec : ObservedDeletionSpec S)
    (kernel : Kernel spec.signature) : Kernel S where
  outcome := spec.liftNodeSet kernel.outcome
  action := spec.liftNodeSet kernel.action
  condition := spec.liftNodeSet kernel.condition

def liftJointQuery (spec : ObservedDeletionSpec S)
    (query : JointKernelQuery spec.signature) : JointKernelQuery S where
  outcome := spec.liftNodeSet query.outcome
  action := spec.liftNodeSet query.action
  action_outcome_disjoint :=
    spec.liftNodeSet_disjoint query.action_outcome_disjoint

def liftConditionalQuery (spec : ObservedDeletionSpec S)
    (query : ConditionalKernelQuery spec.signature) :
    ConditionalKernelQuery S where
  outcome := spec.liftNodeSet query.outcome
  action := spec.liftNodeSet query.action
  condition := spec.liftNodeSet query.condition
  action_outcome_disjoint :=
    spec.liftNodeSet_disjoint query.action_outcome_disjoint
  action_condition_disjoint :=
    spec.liftNodeSet_disjoint query.action_condition_disjoint
  outcome_condition_disjoint :=
    spec.liftNodeSet_disjoint query.outcome_condition_disjoint

theorem liftNodeSet_finAny (spec : ObservedDeletionSpec S)
    (nodes : NodeSet spec.signature) :
    finAny S.count (spec.liftNodeSet nodes) =
      finAny spec.signature.count nodes := by
  apply Bool.eq_iff_iff.mpr
  rw [finAny_eq_true_iff, finAny_eq_true_iff]
  constructor
  · rintro ⟨node, selected⟩
    by_cases retained : node ≠ spec.node
    · exact ⟨spec.retainedIndex node retained, by
        simpa [liftNodeSet, retained] using selected⟩
    · simp [liftNodeSet, retained] at selected
  · rintro ⟨node, selected⟩
    exact ⟨selectedEmbed spec.retained node, by
      simpa using selected⟩

theorem liftKernel_hasAction (spec : ObservedDeletionSpec S)
    (kernel : Kernel spec.signature) :
    (spec.liftKernel kernel).hasAction = kernel.hasAction :=
  spec.liftNodeSet_finAny kernel.action

theorem restrict_liftKernel_intervention
    (spec : ObservedDeletionSpec S) (kernel : Kernel spec.signature)
    (reference : S.Assignment) :
    (spec.restrictIntervention
      { value := (spec.liftKernel kernel).intervention reference }).value =
      kernel.intervention (spec.restrictAssignment reference) := by
  funext child
  cases selected : kernel.action child <;>
    simp [restrictIntervention, liftKernel, Kernel.intervention,
      restrictAssignment, selected] <;> rfl

theorem liftNodeSet_agreesOn (spec : ObservedDeletionSpec S)
    (nodes : NodeSet spec.signature) (reference sample : S.Assignment) :
    Kernel.agreesOn (spec.liftNodeSet nodes) reference sample =
      Kernel.agreesOn nodes (spec.restrictAssignment reference)
        (spec.restrictAssignment sample) := by
  unfold Kernel.agreesOn
  apply Bool.eq_iff_iff.mpr
  rw [finAll_eq_true_iff, finAll_eq_true_iff]
  constructor
  · intro all child
    simpa [restrictAssignment] using
      all (selectedEmbed spec.retained child)
  · intro all node
    by_cases retained : node ≠ spec.node
    · simp only [liftNodeSet, dif_pos retained]
      let child := spec.retainedIndex node retained
      have selected := all child
      cases chosen : nodes child with
      | false => simp
      | true =>
          have equalAtRetained :
              sample (selectedEmbed spec.retained child) =
                reference (selectedEmbed spec.retained child) := by
            simpa [restrictAssignment, chosen] using selected
          have coordinateEqual :=
            spec.selectedEmbed_retainedIndex node retained
          have equalAtNode : sample node = reference node :=
            dependent_equality_transport S.Value coordinateEqual sample reference
              equalAtRetained
          simp [equalAtNode]
    · simp [liftNodeSet, retained]

theorem liftKernel_conditionEvent (spec : ObservedDeletionSpec S)
    (kernel : Kernel spec.signature) (reference sample : S.Assignment) :
    (spec.liftKernel kernel).conditionEvent reference sample =
      spec.liftEvent
        (kernel.conditionEvent (spec.restrictAssignment reference)) sample := by
  exact spec.liftNodeSet_agreesOn kernel.condition reference sample

theorem liftKernel_numeratorEvent (spec : ObservedDeletionSpec S)
    (kernel : Kernel spec.signature) (reference sample : S.Assignment) :
    (spec.liftKernel kernel).numeratorEvent reference sample =
      spec.liftEvent
        (kernel.numeratorEvent (spec.restrictAssignment reference)) sample := by
  simp [Kernel.numeratorEvent, liftKernel, liftEvent,
    spec.liftNodeSet_agreesOn]

theorem liftKernel_distribution_probVal (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (kernel : Kernel spec.signature)
    (reference : S.Assignment)
    (event : spec.signature.Assignment -> Bool) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution model reference).probVal
        (spec.liftEvent event))
      ((kernel.distribution (spec.restrictModel model)
        (spec.restrictAssignment reference)).probVal event) := by
  cases action : kernel.hasAction with
  | false =>
      simpa [Kernel.distribution, spec.liftKernel_hasAction, action] using
        spec.restrictModel_observationalValue model event
  | true =>
      have preserved := spec.restrictModel_interventionalValue model
        { value := (spec.liftKernel kernel).intervention reference } event
      rw [spec.restrict_liftKernel_intervention kernel reference] at preserved
      simpa [Kernel.distribution, spec.liftKernel_hasAction, action] using
        preserved

theorem liftKernel_conditionProbability (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (kernel : Kernel spec.signature)
    (reference : S.Assignment) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution model reference).probVal
        ((spec.liftKernel kernel).conditionEvent reference))
      ((kernel.distribution (spec.restrictModel model)
        (spec.restrictAssignment reference)).probVal
          (kernel.conditionEvent (spec.restrictAssignment reference))) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_congr _ _ _
      (fun sample => spec.liftKernel_conditionEvent kernel reference sample))
    (spec.liftKernel_distribution_probVal model kernel reference
      (kernel.conditionEvent (spec.restrictAssignment reference)))

theorem liftKernel_numeratorProbability (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (kernel : Kernel spec.signature)
    (reference : S.Assignment) :
    QProb.Equiv
      (((spec.liftKernel kernel).distribution model reference).probVal
        ((spec.liftKernel kernel).numeratorEvent reference))
      ((kernel.distribution (spec.restrictModel model)
        (spec.restrictAssignment reference)).probVal
          (kernel.numeratorEvent (spec.restrictAssignment reference))) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_congr _ _ _
      (fun sample => spec.liftKernel_numeratorEvent kernel reference sample))
    (spec.liftKernel_distribution_probVal model kernel reference
      (kernel.numeratorEvent (spec.restrictAssignment reference)))

noncomputable def liftKernel_denote (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (kernel : Kernel spec.signature)
    (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftKernel kernel).denote model reference)
      (kernel.denote (spec.restrictModel model)
        (spec.restrictAssignment reference)) := by
  exact ProbabilityResult.divide_congr
    (.value (spec.liftKernel_numeratorProbability model kernel reference))
    (.value (spec.liftKernel_conditionProbability model kernel reference))

theorem liftJointQuery_operationKernel (spec : ObservedDeletionSpec S)
    (query : JointKernelQuery spec.signature) :
    (spec.liftJointQuery query).operationKernel =
      spec.liftKernel query.operationKernel := by
  apply congrArg (fun condition : NodeSet S =>
    Kernel.mk (spec.liftNodeSet query.outcome)
      (spec.liftNodeSet query.action) condition)
  funext node
  simp [liftNodeSet, JointKernelQuery.operationKernel, NodeSet.empty]

@[simp] theorem liftConditionalQuery_operationKernel
    (spec : ObservedDeletionSpec S)
    (query : ConditionalKernelQuery spec.signature) :
    (spec.liftConditionalQuery query).operationKernel =
      spec.liftKernel query.operationKernel :=
  rfl

noncomputable def liftJointQuery_denote (spec : ObservedDeletionSpec S)
    (model : ExactModel S) (query : JointKernelQuery spec.signature)
    (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftJointQuery query).sourceTerm.denote model reference)
      (query.sourceTerm.denote (spec.restrictModel model)
        (spec.restrictAssignment reference)) := by
  rw [JointKernelQuery.sourceTerm_eq_operationKernel,
    JointKernelQuery.sourceTerm_eq_operationKernel,
    spec.liftJointQuery_operationKernel query]
  exact spec.liftKernel_denote model query.operationKernel reference

noncomputable def liftConditionalQuery_denote
    (spec : ObservedDeletionSpec S) (model : ExactModel S)
    (query : ConditionalKernelQuery spec.signature)
    (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      ((spec.liftConditionalQuery query).sourceTerm.denote model reference)
      (query.sourceTerm.denote (spec.restrictModel model)
        (spec.restrictAssignment reference)) := by
  rw [ConditionalKernelQuery.sourceTerm_eq_operationKernel,
    ConditionalKernelQuery.sourceTerm_eq_operationKernel,
    spec.liftConditionalQuery_operationKernel query]
  exact spec.liftKernel_denote model query.operationKernel reference

theorem restrictModel_observationalAgreement
    (spec : ObservedDeletionSpec S) (left right : ExactModel S)
    (agreement : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (spec.restrictModel left)
      (spec.restrictModel right) := by
  intro event
  exact QProb.equiv_trans
    (QProb.equiv_symm (spec.restrictModel_observationalValue left event))
    (QProb.equiv_trans (agreement (spec.liftEvent event))
      (spec.restrictModel_observationalValue right event))

end ObservedDeletionSpec

end Causality
end Thesis
