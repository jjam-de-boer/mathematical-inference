import Thesis.Causality.Learning
import Thesis.Causality.PairRoot

namespace Thesis
namespace Causality

open Probability
open CausalEpistemicRecord

private theorem dependent_apply_eq_cast {n : Nat} (Value : Fin n -> Type u)
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

private theorem cast_dependent_apply_eq {n : Nat} (Value : Fin n -> Type u)
    {left right : Fin n} (equal : left = right)
    (values : (node : Fin n) -> Value node) :
    cast (congrArg Value equal.symm) (values right) = values left := by
  cases equal
  rfl

private theorem dependent_event_apply_cast {n : Nat}
    (Value : Fin n -> Type u) {left right : Fin n} (equal : left = right)
    (events : (node : Fin n) -> Value node -> Bool) (value : Value right) :
    events left (cast (congrArg Value equal.symm) value) =
      events right value := by
  cases equal
  rfl

private theorem qProduct_cast {n m : Nat} (equal : n = m)
    (values : Fin n -> QProb) :
    QProb.Equiv (FiniteProduct.qProduct n values)
      (FiniteProduct.qProduct m (fun index => values (Fin.cast equal.symm index))) := by
  cases equal
  exact QProb.equiv_refl _

private theorem finAny_cast {n m : Nat} (equal : n = m)
    (predicate : Fin n -> Bool) :
    finAny n predicate =
      finAny m (fun index => predicate (Fin.cast equal.symm index)) := by
  cases equal
  rfl

private theorem cast_record_probVal {A B : Type u} (equal : A = B)
    (record : FiniteProbRecord A) (event : A -> Bool) :
    QProb.Equiv
      ((cast (congrArg FiniteProbRecord equal) record).probVal
        (fun value => event (cast equal.symm value)))
      (record.probVal event) := by
  cases equal
  exact QProb.equiv_refl _

namespace LatentExtension

instance assignmentDecidableEq (latent : LatentExtension S) :
    DecidableEq latent.Assignment :=
  FiniteProduct.assignmentDecidableEq latent.count latent.Value
    latent.valueDecidableEq

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

private def addOnes (n m : Nat) (values : Fin n -> QProb) :
    Fin (n + m) -> QProb :=
  Fin.addCases (motive := fun _ => QProb) values
    (fun _ : Fin m => QProb.one)

private theorem qProduct_add_ones (n m : Nat) (values : Fin n -> QProb) :
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

private theorem finAny_add {n m : Nat} (left : Fin n -> Bool)
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

/-!
Constructive deletion of structurally unused causal variables.

Observed deletion removes a directed sink from the dependent finite signature.
Incoming directed edges are allowed: they occur only in the deleted equation.
Exogenous deletion removes a latent root that is incident to no observed
mechanism and pushes the prior and current belief forward along the coordinate
projection.
-/

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
