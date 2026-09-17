import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.DSeparationCorrectness

namespace Thesis
namespace Causality

open Probability

/-!
Constructive ingredients for inhabiting the finite-source soundness interface.

This module proves the graph-independent probability-algebra leaves first.
The d-separation/global-Markov layer and the three causal rules are kept
separate so that each stage can be audited independently.
-/

namespace FiniteLatentSCM

private instance factorizationAssignmentDecidableEq
    (model : FiniteLatentSCM S) : DecidableEq model.latent.Assignment :=
  FiniteProduct.assignmentDecidableEq model.latent.count
    model.latent.Value model.latent.valueDecidableEq

private def factorizationAssignments (model : FiniteLatentSCM S) :
    List model.latent.Assignment := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  exact deduplicate (FiniteProduct.enumeration model.latent.count
    model.latent.Value model.latent.valueEnumeration)

private theorem factorizationAssignments_complete (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    assignment ∈ factorizationAssignments model := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  rw [factorizationAssignments, mem_deduplicate]
  exact FiniteProduct.enumeration_complete model.latent.count
    model.latent.Value model.latent.valueEnumeration
      model.latent.value_complete assignment

private theorem factorizationAssignments_nodup (model : FiniteLatentSCM S) :
    (factorizationAssignments model).Nodup := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  exact deduplicate_nodup _

private def assignmentEvents (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    (root : Fin model.latent.count) -> model.latent.Value root -> Bool :=
  fun root value => decide (value = assignment root)

private theorem rectangular_assignmentEvents (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    model.latent.rectangularEvent (assignmentEvents model assignment) =
      FiniteProbRecord.singletonEvent assignment := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  funext candidate
  apply Bool.eq_iff_iff.mpr
  change
    FiniteProduct.rectangularEvent model.latent.count model.latent.Value
        (assignmentEvents model assignment) candidate = true <->
      FiniteProbRecord.singletonEvent assignment candidate = true
  rw [FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro equal
    have same : candidate = assignment := by
      funext root
      exact of_decide_eq_true (equal root)
    simp [FiniteProbRecord.singletonEvent, same]
  · intro equal root
    have same : candidate = assignment := by
      simpa [FiniteProbRecord.singletonEvent] using equal
    subst candidate
    simp [assignmentEvents]

/--
The rectangular-event product law determines the complete latent prior, not
only its rectangular marginals.  Consequently all subsequent finite
factorization arguments may work with the canonical dependent product record.
-/
theorem prior_probVal_productRecord (model : FiniteLatentSCM S)
    (event : model.latent.Assignment -> Bool) :
    QProb.Equiv (model.prior.probVal event)
      ((FiniteProduct.record model.latent.count model.latent.Value
        model.factor).probVal event) := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  apply FiniteProbRecord.probVal_extensional_of_singletons
    model.prior
    (FiniteProduct.record model.latent.count model.latent.Value model.factor)
    (factorizationAssignments model)
    (factorizationAssignments_nodup model)
    (factorizationAssignments_complete model)
  intro assignment
  let events := assignmentEvents model assignment
  have supplied := model.product_law events
  have canonical := FiniteProduct.record_rectangular_probVal
    model.latent.count model.latent.Value model.factor events
  have eventEq : FiniteProduct.rectangularEvent model.latent.count
      model.latent.Value events =
        FiniteProbRecord.singletonEvent assignment := by
    simpa [events, LatentExtension.rectangularEvent] using
      rectangular_assignmentEvents model assignment
  change QProb.Equiv
    (model.prior.probVal
      (FiniteProduct.rectangularEvent model.latent.count
        model.latent.Value events)) _ at supplied
  rw [eventEq] at supplied canonical
  exact QProb.equiv_trans supplied (QProb.equiv_symm canonical)

theorem interventionalValue_productRecord (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (event : S.Assignment -> Bool) :
    QProb.Equiv (model.interventionalValue intervention event)
      ((FiniteProduct.record model.latent.count model.latent.Value
        model.factor).probVal
          (fun roots => event (model.evalUnder intervention roots))) :=
  QProb.equiv_trans (model.interventionalValue_eq intervention event)
    (model.prior_probVal_productRecord
      (fun roots => event (model.evalUnder intervention roots)))

theorem observationalValue_productRecord (model : FiniteLatentSCM S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (model.observationalValue event)
      ((FiniteProduct.record model.latent.count model.latent.Value
        model.factor).probVal (fun roots => event (model.eval roots))) :=
  QProb.equiv_trans (model.observationalValue_eq event)
    (model.prior_probVal_productRecord
      (fun roots => event (model.eval roots)))

/-- A latent root is relevant to a node set under an intervention when it is
incident to at least one non-intervened node in that set. -/
def latentRelevantUnder (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S)
    (root : Fin model.latent.count) : Bool :=
  finAny S.count (fun child =>
    nodes child && (intervention child).isNone &&
      model.latent.incident root child)

theorem latentRelevantUnder_eq_true_iff (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (root : Fin model.latent.count) :
    model.latentRelevantUnder intervention nodes root = true <->
      Exists fun child : Fin S.count =>
        nodes child = true /\ intervention child = none /\
          model.latent.incident root child = true := by
  rw [latentRelevantUnder, finAny_eq_true_iff]
  constructor
  · rintro ⟨child, holds⟩
    rcases Bool.and_eq_true_iff.mp holds with ⟨selectedAndFree, incident⟩
    rcases Bool.and_eq_true_iff.mp selectedAndFree with
      ⟨selected, notIntervened⟩
    exact ⟨child, selected, Option.isNone_iff_eq_none.mp notIntervened,
      incident⟩
  · rintro ⟨child, selected, notIntervened, incident⟩
    refine ⟨child, Bool.and_eq_true_iff.mpr ⟨?_, incident⟩⟩
    exact Bool.and_eq_true_iff.mpr
      ⟨selected, Option.isNone_iff_eq_none.mpr notIntervened⟩

theorem latentRelevantUnder_of_incident (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (root : Fin model.latent.count)
    (child : Fin S.count) (selected : nodes child = true)
    (notIntervened : intervention child = none)
    (incident : model.latent.incident root child = true) :
    model.latentRelevantUnder intervention nodes root = true := by
  apply finAny_eq_true_of _ child
  simp [selected, notIntervened, incident]

/-- A set contains every non-intervened directed parent of each of its
members. -/
def BackwardClosedUnder (_model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) : Prop :=
  forall parent child,
    nodes child = true -> intervention child = none ->
      S.directed parent child = true -> nodes parent = true

/-- Evaluation on a backward-closed node set observes only latent roots
incident to that set. -/
theorem evalNodeUnder_eq_of_rootAgreement (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (closed : model.BackwardClosedUnder intervention nodes)
    (left right : model.latent.Assignment)
    (rootsAgree : forall root,
      model.latentRelevantUnder intervention nodes root = true ->
      left root = right root)
    (child : Fin S.count) (selected : nodes child = true) :
    model.evalNodeUnder intervention left child =
      model.evalNodeUnder intervention right child := by
  rw [evalNodeUnder, evalNodeUnder]
  unfold equationUnder
  cases intervened : intervention child with
  | some value => rfl
  | none =>
      change model.mechanism child _ _ = model.mechanism child _ _
      congr 1
      · funext parent edge
        exact model.evalNodeUnder_eq_of_rootAgreement intervention nodes closed
          left right rootsAgree parent (closed parent child selected intervened edge)
      · funext root incident
        exact rootsAgree root
          (model.latentRelevantUnder_of_incident intervention nodes root child
            selected intervened incident)
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

theorem evalUnder_eq_on_of_rootAgreement (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (nodes : NodeSet S) (closed : model.BackwardClosedUnder intervention nodes)
    (left right : model.latent.Assignment)
    (rootsAgree : forall root,
      model.latentRelevantUnder intervention nodes root = true ->
      left root = right root) :
    forall child, nodes child = true ->
      model.evalUnder intervention left child =
        model.evalUnder intervention right child := by
  intro child selected
  exact model.evalNodeUnder_eq_of_rootAgreement intervention nodes closed
    left right rootsAgree child selected

/-- No latent root is relevant to both node sets. -/
def LatentSeparatedUnder (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (left right : NodeSet S) : Prop :=
  forall root, model.latentRelevantUnder intervention left root = true ->
    model.latentRelevantUnder intervention right root = false

/-- A shared latent parent of two distinct observed nodes is visible as a
bidirected edge in every graph compatible with the model. -/
theorem bidirected_eq_true_of_shared_latent
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (root : Fin model.latent.count) (left right : Fin S.count)
    (different : left ≠ right)
    (leftIncident : model.latent.incident root left = true)
    (rightIncident : model.latent.incident root right = true) :
    G.bidirected left right = true := by
  rw [← projected left right]
  change model.latent.projectedBidirected left right = true
  apply Bool.and_eq_true_iff.mpr
  constructor
  · have valueDifferent : left.val ≠ right.val := by
      intro equal
      exact different (Fin.ext equal)
    cases hbeq : Nat.beq left.val right.val with
    | true =>
        exact (valueDifferent (Nat.eq_of_beq_eq_true hbeq)).elim
    | false =>
        rfl
  · apply finAny_eq_true_of _ root
    exact Bool.and_eq_true_iff.mpr ⟨leftIncident, rightIncident⟩

/-- If two disjoint observed regions have no projected bidirected edge
between them, no non-intervened latent root can be relevant to both. -/
theorem latentSeparatedUnder_of_no_bidirected_across
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (projected : HasProjectedGraph model G)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (left right : NodeSet S) (disjoint : NodeSet.Disjoint left right)
    (noBidirected : forall leftNode rightNode,
      left leftNode = true -> right rightNode = true ->
        G.bidirected leftNode rightNode = false) :
    model.LatentSeparatedUnder intervention left right := by
  intro root leftRelevant
  cases rightRelevant : model.latentRelevantUnder intervention right root with
  | false => rfl
  | true =>
      rcases (model.latentRelevantUnder_eq_true_iff intervention left root).mp
          leftRelevant with
        ⟨leftNode, leftSelected, _leftFree, leftIncident⟩
      rcases (model.latentRelevantUnder_eq_true_iff intervention right root).mp
          rightRelevant with
        ⟨rightNode, rightSelected, _rightFree, rightIncident⟩
      have different : leftNode ≠ rightNode := by
        intro same
        subst rightNode
        have excluded := disjoint leftNode leftSelected
        rw [rightSelected] at excluded
        contradiction
      have edgeTrue := bidirected_eq_true_of_shared_latent model G projected
        root leftNode rightNode different leftIncident rightIncident
      have edgeFalse := noBidirected leftNode rightNode
        leftSelected rightSelected
      rw [edgeTrue] at edgeFalse
      contradiction

end FiniteLatentSCM

namespace CanonicalFactorization

open Probability.FiniteProduct

/-- Splice two dependent assignments along a decidable coordinate set. -/
def spliceAssignment (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (left right : Assignment n Value) :
    Assignment n Value :=
  fun coordinate => if selected coordinate then left coordinate
    else right coordinate

@[simp] theorem spliceAssignment_selected (n : Nat)
    (Value : Fin n -> Type u) (selected : Fin n -> Bool)
    (left right : Assignment n Value) (coordinate : Fin n)
    (isSelected : selected coordinate = true) :
    spliceAssignment n Value selected left right coordinate =
      left coordinate := by
  simp [spliceAssignment, isSelected]

@[simp] theorem spliceAssignment_unselected (n : Nat)
    (Value : Fin n -> Type u) (selected : Fin n -> Bool)
    (left right : Assignment n Value) (coordinate : Fin n)
    (isUnselected : selected coordinate = false) :
    spliceAssignment n Value selected left right coordinate =
      right coordinate := by
  simp [spliceAssignment, isUnselected]

theorem spliceAssignment_exchange (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (left right : Assignment n Value) :
    spliceAssignment n Value selected
        (spliceAssignment n Value selected left right)
        (spliceAssignment n Value selected right left) = left := by
  funext coordinate
  cases chosen : selected coordinate <;>
    simp [spliceAssignment, chosen]

/-- Swapping any selected family of independent coordinates between two
assignments preserves the product of their point masses. -/
theorem qProduct_splice_mul (n : Nat) (Value : Fin n -> Type u)
    (weight : (coordinate : Fin n) -> Value coordinate -> QProb)
    (selected : Fin n -> Bool) (left right : Assignment n Value) :
    QProb.Equiv
      (QProb.mul
        (qProduct n (fun coordinate => weight coordinate (left coordinate)))
        (qProduct n (fun coordinate => weight coordinate (right coordinate))))
      (QProb.mul
        (qProduct n (fun coordinate => weight coordinate
          (spliceAssignment n Value selected left right coordinate)))
        (qProduct n (fun coordinate => weight coordinate
          (spliceAssignment n Value selected right left coordinate)))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let prefixValue := fun coordinate : Fin n => Value coordinate.castSucc
      let prefixWeight := fun (coordinate : Fin n) => weight coordinate.castSucc
      let prefixSelected := fun coordinate : Fin n => selected coordinate.castSucc
      let leftPrefix : Assignment n prefixValue :=
        fun coordinate => left coordinate.castSucc
      let rightPrefix : Assignment n prefixValue :=
        fun coordinate => right coordinate.castSucc
      have prefixSwap := ih prefixValue prefixWeight prefixSelected
        leftPrefix rightPrefix
      let lastLeft := weight (Fin.last n) (left (Fin.last n))
      let lastRight := weight (Fin.last n) (right (Fin.last n))
      let leftProduct := qProduct n
        (fun coordinate => prefixWeight coordinate (leftPrefix coordinate))
      let rightProduct := qProduct n
        (fun coordinate => prefixWeight coordinate (rightPrefix coordinate))
      let firstSplice := qProduct n (fun coordinate =>
        prefixWeight coordinate
          (spliceAssignment n prefixValue prefixSelected
            leftPrefix rightPrefix coordinate))
      let secondSplice := qProduct n (fun coordinate =>
        prefixWeight coordinate
          (spliceAssignment n prefixValue prefixSelected
            rightPrefix leftPrefix coordinate))
      have groupedLeft : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft leftProduct)
            (QProb.mul lastRight rightProduct))
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul leftProduct rightProduct)) := by
        simp [QProb.Equiv, QProb.mul]
        ac_rfl
      have groupedMiddle : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul leftProduct rightProduct))
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul firstSplice secondSplice)) :=
        QProb.mul_congr (QProb.equiv_refl _)
          (by simpa [leftProduct, rightProduct, firstSplice,
            secondSplice] using prefixSwap)
      have groupedRightFalse : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul firstSplice secondSplice))
          (QProb.mul (QProb.mul lastRight firstSplice)
            (QProb.mul lastLeft secondSplice)) := by
        simp [QProb.Equiv, QProb.mul]
        ac_rfl
      have groupedRightTrue : QProb.Equiv
          (QProb.mul (QProb.mul lastLeft lastRight)
            (QProb.mul firstSplice secondSplice))
          (QProb.mul (QProb.mul lastLeft firstSplice)
            (QProb.mul lastRight secondSplice)) := by
        simp [QProb.Equiv, QProb.mul]
        ac_rfl
      cases lastSelected : selected (Fin.last n) with
      | false =>
          simpa [qProduct, spliceAssignment, lastSelected, lastLeft,
            lastRight, leftProduct, rightProduct, firstSplice,
            secondSplice, prefixValue, prefixWeight, prefixSelected,
            leftPrefix, rightPrefix] using
            QProb.equiv_trans groupedLeft
              (QProb.equiv_trans groupedMiddle groupedRightFalse)
      | true =>
          simpa [qProduct, spliceAssignment, lastSelected, lastLeft,
            lastRight, leftProduct, rightProduct, firstSplice,
            secondSplice, prefixValue, prefixWeight, prefixSelected,
            leftPrefix, rightPrefix] using
            QProb.equiv_trans groupedLeft
              (QProb.equiv_trans groupedMiddle groupedRightTrue)

/-- An event observes only the coordinates marked by `selected`. -/
def DependsOnSelected (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool) : Prop :=
  forall left right,
    (forall coordinate, selected coordinate = true ->
      left coordinate = right coordinate) ->
    event left = event right

/-- An event observes only the coordinates not marked by `selected`. -/
def DependsOnUnselected (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool) : Prop :=
  forall left right,
    (forall coordinate, selected coordinate = false ->
      left coordinate = right coordinate) ->
    event left = event right

theorem DependsOnSelected.inter (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (leftEvent rightEvent : Assignment n Value -> Bool)
    (leftDepends : DependsOnSelected n Value selected leftEvent)
    (rightDepends : DependsOnSelected n Value selected rightEvent) :
    DependsOnSelected n Value selected
      (Probability.inter leftEvent rightEvent) := by
  intro left right agree
  simp [Probability.inter, leftDepends left right agree,
    rightDepends left right agree]

theorem DependsOnUnselected.inter (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (leftEvent rightEvent : Assignment n Value -> Bool)
    (leftDepends : DependsOnUnselected n Value selected leftEvent)
    (rightDepends : DependsOnUnselected n Value selected rightEvent) :
    DependsOnUnselected n Value selected
      (Probability.inter leftEvent rightEvent) := by
  intro left right agree
  simp [Probability.inter, leftDepends left right agree,
    rightDepends left right agree]

theorem dependsOnSelected_splice (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool)
    (depends : DependsOnSelected n Value selected event)
    (left right : Assignment n Value) :
    event (spliceAssignment n Value selected left right) = event left := by
  apply depends
  intro coordinate chosen
  exact spliceAssignment_selected n Value selected left right coordinate chosen

theorem dependsOnUnselected_splice (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool) (event : Assignment n Value -> Bool)
    (depends : DependsOnUnselected n Value selected event)
    (left right : Assignment n Value) :
    event (spliceAssignment n Value selected left right) = event right := by
  apply depends
  intro coordinate chosen
  exact spliceAssignment_unselected n Value selected left right coordinate chosen

/-- Swap the selected coordinates of a pair of assignments. -/
def swapPair (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool)
    (pair : Assignment n Value × Assignment n Value) :
    Assignment n Value × Assignment n Value :=
  (spliceAssignment n Value selected pair.1 pair.2,
    spliceAssignment n Value selected pair.2 pair.1)

theorem swapPair_involutive (n : Nat) (Value : Fin n -> Type u)
    (selected : Fin n -> Bool)
    (pair : Assignment n Value × Assignment n Value) :
    swapPair n Value selected (swapPair n Value selected pair) = pair := by
  apply Prod.ext
  · exact spliceAssignment_exchange n Value selected pair.1 pair.2
  · exact spliceAssignment_exchange n Value selected pair.2 pair.1

/-- A map with an explicit left inverse preserves duplicate-freeness. -/
theorem nodup_map_of_leftInverse {A : Type u} {B : Type v} (forward : A -> B)
    (backward : B -> A) (leftInverse : forall value,
      backward (forward value) = value) (values : List A)
    (nodup : values.Nodup) : (values.map forward).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons value values ih =>
      rw [List.map_cons, List.nodup_cons]
      have parts := List.nodup_cons.mp nodup
      constructor
      · intro occurs
        obtain ⟨other, otherMem, same⟩ := List.mem_map.mp occurs
        apply parts.1
        have sameValue : other = value := by
          rw [← leftInverse other, ← leftInverse value, same]
        simpa [sameValue] using otherMem
      · exact ih parts.2

/-- Cartesian-product enumeration, with the right coordinate varying fastest. -/
def pairList {A : Type u} {B : Type v} (left : List A) (right : List B) :
    List (A × B) :=
  left.flatMap (fun first => right.map (fun second => (first, second)))

@[simp] theorem mem_pairList {A : Type u} {B : Type v}
    [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (first : A) (second : B)
    (left : List A) (right : List B) :
    (first, second) ∈ pairList left right <->
      first ∈ left ∧ second ∈ right := by
  simp [pairList]

theorem pairList_nodup {A : Type u} {B : Type v}
    [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (left : List A) (right : List B)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (pairList left right).Nodup := by
  induction left with
  | nil => exact List.nodup_nil
  | cons first left ih =>
      have parts := List.nodup_cons.mp leftNodup
      rw [pairList, List.flatMap_cons, List.nodup_append]
      constructor
      · exact nodup_map_of_leftInverse (fun second => (first, second))
          Prod.snd (fun _ => rfl) right rightNodup
      · constructor
        · exact ih parts.2
        · intro rowPair rowMem tailPair tailMem same
          apply parts.1
          have rowFirst : rowPair.1 = first := by
            obtain ⟨second, _, rowEq⟩ := List.mem_map.mp rowMem
            rw [← rowEq]
          have tailFirst : tailPair.1 ∈ left :=
            (mem_pairList tailPair.1 tailPair.2 left right).mp tailMem |>.1
          rw [← rowFirst, same]
          exact tailFirst

/-- Duplicate-free finite enumerations with the same members differ only by a
permutation. -/
theorem perm_of_nodup_mem_iff {A : Type u} [BEq A] [LawfulBEq A]
    (left right : List A) (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : forall value, value ∈ left <-> value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Perm.refl []
      | cons head tail =>
          have impossible : head ∈ ([] : List A) :=
            (sameMembers head).mpr (by simp)
          simp at impossible
  | cons head tail ih =>
      have leftParts := List.nodup_cons.mp leftNodup
      have headMemRight := (sameMembers head).mp (by simp)
      obtain ⟨before, suffix, rightEq⟩ := List.append_of_mem headMemRight
      subst right
      have rightParts := List.nodup_append.mp rightNodup
      have suffixParts := List.nodup_cons.mp rightParts.2.1
      have removedNodup : (before ++ suffix).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨rightParts.1, suffixParts.2, ?_⟩
        intro first firstMem second secondMem same
        exact rightParts.2.2 first firstMem second (by simp [secondMem]) same
      have headNotRemoved : head ∉ before ++ suffix := by
        intro occurs
        simp only [List.mem_append] at occurs
        rcases occurs with inPrefix | inSuffix
        · exact rightParts.2.2 head inPrefix head (by simp) rfl
        · exact suffixParts.1 inSuffix
      have tailMembers : forall value,
          value ∈ tail <-> value ∈ before ++ suffix := by
        intro value
        constructor
        · intro tailMem
          have different : value ≠ head := by
            intro same
            subst value
            exact leftParts.1 tailMem
          have rightMem := (sameMembers value).mp (by simp [tailMem])
          simp only [List.mem_append, List.mem_cons] at rightMem ⊢
          rcases rightMem with inPrefix | same | inSuffix
          · exact Or.inl inPrefix
          · exact (different same).elim
          · exact Or.inr inSuffix
        · intro removedMem
          have rightMem : value ∈ before ++ head :: suffix := by
            simp only [List.mem_append, List.mem_cons] at removedMem ⊢
            rcases removedMem with inPrefix | inSuffix
            · exact Or.inl inPrefix
            · exact Or.inr (Or.inr inSuffix)
          have leftMem := (sameMembers value).mpr rightMem
          simp only [List.mem_cons] at leftMem
          rcases leftMem with same | inTail
          · subst value
            exact (headNotRemoved removedMem).elim
          · exact inTail
      have tailPerm := ih (before ++ suffix) leftParts.2 removedNodup
        tailMembers
      exact (tailPerm.cons head).trans List.perm_middle.symm

/-- Splicing is a constructive bijection between pairs satisfying separate
selected/unselected events and pairs whose first component satisfies their
intersection.  The second component is unrestricted. -/
theorem swapPair_eventPairs_perm (n : Nat) (Value : Fin n -> Type u)
    [DecidableEq (Assignment n Value)]
    (selected : Fin n -> Bool) (values : List (Assignment n Value))
    (valuesNodup : values.Nodup)
    (valuesComplete : forall value, value ∈ values)
    (selectedEvent unselectedEvent : Assignment n Value -> Bool)
    (selectedDepends : DependsOnSelected n Value selected selectedEvent)
    (unselectedDepends : DependsOnUnselected n Value selected
      unselectedEvent) :
    (pairList (values.filter selectedEvent)
      (values.filter unselectedEvent)).map (swapPair n Value selected) |>.Perm
        (pairList (values.filter
          (Probability.inter selectedEvent unselectedEvent)) values) := by
  let source := pairList (values.filter selectedEvent)
    (values.filter unselectedEvent)
  let target := pairList (values.filter
    (Probability.inter selectedEvent unselectedEvent)) values
  have sourceNodup : source.Nodup := by
    exact pairList_nodup _ _
      (List.Sublist.nodup List.filter_sublist valuesNodup)
      (List.Sublist.nodup List.filter_sublist valuesNodup)
  have targetNodup : target.Nodup := by
    exact pairList_nodup _ _
      (List.Sublist.nodup List.filter_sublist valuesNodup) valuesNodup
  have mappedNodup :
      (source.map (swapPair n Value selected)).Nodup :=
    nodup_map_of_leftInverse (swapPair n Value selected)
      (swapPair n Value selected)
      (swapPair_involutive n Value selected) source sourceNodup
  apply perm_of_nodup_mem_iff _ _ mappedNodup targetNodup
  intro targetPair
  constructor
  · intro occurs
    obtain ⟨sourcePair, sourceMem, swapped⟩ := List.mem_map.mp occurs
    have sourceParts :=
      (mem_pairList sourcePair.1 sourcePair.2
        (values.filter selectedEvent)
        (values.filter unselectedEvent)).mp sourceMem
    have firstParts := List.mem_filter.mp sourceParts.1
    have secondParts := List.mem_filter.mp sourceParts.2
    rw [← swapped]
    apply (mem_pairList _ _
      (values.filter (Probability.inter selectedEvent unselectedEvent))
      values).mpr
    constructor
    · apply List.mem_filter.mpr
      constructor
      · exact valuesComplete _
      · have selectedPreserved := dependsOnSelected_splice n Value selected
          selectedEvent selectedDepends sourcePair.1 sourcePair.2
        have unselectedPreserved := dependsOnUnselected_splice n Value selected
          unselectedEvent unselectedDepends sourcePair.1 sourcePair.2
        simp [Probability.inter, selectedPreserved, unselectedPreserved,
          firstParts.2, secondParts.2]
    · exact valuesComplete _
  · intro occurs
    have targetParts :=
      (mem_pairList targetPair.1 targetPair.2
        (values.filter (Probability.inter selectedEvent unselectedEvent))
        values).mp occurs
    have firstParts := List.mem_filter.mp targetParts.1
    have eventParts : selectedEvent targetPair.1 = true ∧
        unselectedEvent targetPair.1 = true := by
      simpa [Probability.inter] using firstParts.2
    apply List.mem_map.mpr
    refine ⟨swapPair n Value selected targetPair, ?_,
      swapPair_involutive n Value selected targetPair⟩
    apply (mem_pairList _ _ (values.filter selectedEvent)
      (values.filter unselectedEvent)).mpr
    constructor
    · apply List.mem_filter.mpr
      constructor
      · exact valuesComplete _
      · have preserved := dependsOnSelected_splice n Value selected
          selectedEvent selectedDepends targetPair.1 targetPair.2
        simpa [swapPair, preserved] using eventParts.1
    · apply List.mem_filter.mpr
      constructor
      · exact valuesComplete _
      · have preserved := dependsOnUnselected_splice n Value selected
          unselectedEvent unselectedDepends targetPair.2 targetPair.1
        simpa [swapPair, preserved] using eventParts.2

end CanonicalFactorization

namespace ProbabilityTerm

private theorem unionList_event_true_of_mem
    {events : List (Probability.Event X)} {event : Probability.Event X}
    (member : event ∈ events) (value : X) (holds : event value = true) :
    Probability.unionList events value = true := by
  induction events with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst event
        simp [Probability.unionList, Probability.union, holds]
      · simp [Probability.unionList, Probability.union, ih later]

private theorem exists_event_of_unionList_true
    (events : List (Probability.Event X)) (value : X)
    (holds : Probability.unionList events value = true) :
    ∃ event, event ∈ events ∧ event value = true := by
  induction events with
  | nil => simp [Probability.unionList, Probability.bottomEvent] at holds
  | cons head tail ih =>
      simp only [Probability.unionList, Probability.union,
        Bool.or_eq_true] at holds
      rcases holds with headHolds | tailHolds
      · exact ⟨head, by simp, headHolds⟩
      · rcases ih tailHolds with ⟨event, member, eventHolds⟩
        exact ⟨event, by simp [member], eventHolds⟩

theorem marginal_numerator_events_pairwise
    (y z action w : NodeSet S) (reference : S.Assignment) :
    ((marginalAssignments S z reference).map (fun variant =>
      (Kernel.mk (NodeSet.union y z) action w).numeratorEvent variant)).Pairwise
      Probability.disjoint := by
  apply (List.pairwise_map).mpr
  apply List.Pairwise.imp_of_mem
    (p := marginalAssignments_nodup S z reference)
  intro first second firstMember secondMember different
  intro sample firstHolds secondHolds
  apply different
  have firstZ : Kernel.agreesOn z first sample = true := by
    have parts : Kernel.agreesOn y first sample = true ∧
        Kernel.agreesOn z first sample = true ∧
          Kernel.agreesOn w first sample = true := by
      simpa [Kernel.numeratorEvent, Kernel.agreesOn_union, Bool.and_assoc] using
        firstHolds
    exact parts.2.1
  have secondZ : Kernel.agreesOn z second sample = true := by
    have parts : Kernel.agreesOn y second sample = true ∧
        Kernel.agreesOn z second sample = true ∧
          Kernel.agreesOn w second sample = true := by
      simpa [Kernel.numeratorEvent, Kernel.agreesOn_union, Bool.and_assoc] using
        secondHolds
    exact parts.2.1
  have firstProjected := (Kernel.agreesOn_iff_project_eq z first sample).mp firstZ
  have secondProjected := (Kernel.agreesOn_iff_project_eq z second sample).mp secondZ
  funext i
  cases selected : z i with
  | false =>
      exact (marginal_member_agrees_outside firstMember selected).trans
        (marginal_member_agrees_outside secondMember selected).symm
  | true =>
      have projected : S.project z first i = S.project z second i := by
        rw [← firstProjected, ← secondProjected]
      simpa [ObservedSignature.project, selected] using projected

theorem marginal_numerator_union
    (y z action w : NodeSet S) (reference : S.Assignment)
    (yz : NodeSet.Disjoint y z) (wz : NodeSet.Disjoint w z) :
    Probability.unionList
        ((marginalAssignments S z reference).map (fun variant =>
          (Kernel.mk (NodeSet.union y z) action w).numeratorEvent variant)) =
      (Kernel.mk y action w).numeratorEvent reference := by
  funext sample
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro unionHolds
    rcases exists_event_of_unionList_true _ sample unionHolds with
      ⟨event, eventMember, eventHolds⟩
    simp only [List.mem_map] at eventMember
    rcases eventMember with ⟨variant, variantMember, eventEq⟩
    subst event
    have variantY : ∀ i, y i = true -> variant i = reference i := by
      intro i selected
      exact marginal_member_agrees_outside variantMember (yz i selected)
    have variantW : ∀ i, w i = true -> variant i = reference i := by
      intro i selected
      exact marginal_member_agrees_outside variantMember (wz i selected)
    have yAgreement := Kernel.agreesOn_reference_congr y variant reference sample variantY
    have wAgreement := Kernel.agreesOn_reference_congr w variant reference sample variantW
    have parts : Kernel.agreesOn y reference sample = true ∧
        Kernel.agreesOn z variant sample = true ∧
          Kernel.agreesOn w reference sample = true := by
      simpa [Kernel.numeratorEvent, Kernel.agreesOn_union, Bool.and_assoc,
        yAgreement, wAgreement] using eventHolds
    simpa [Kernel.numeratorEvent] using And.intro parts.1 parts.2.2
  · intro targetHolds
    let variant := marginalVariant S z reference sample
    have variantMember := marginalVariant_mem S z reference sample
    apply unionList_event_true_of_mem
      (List.mem_map.mpr ⟨variant, variantMember, rfl⟩) sample
    have variantY : ∀ i, y i = true -> variant i = reference i := by
      intro i selected
      have notZ := yz i selected
      simp [variant, marginalVariant, notZ]
    have variantW : ∀ i, w i = true -> variant i = reference i := by
      intro i selected
      have notZ := wz i selected
      simp [variant, marginalVariant, notZ]
    have variantZ : ∀ i, z i = true -> variant i = sample i := by
      intro i selected
      simp [variant, marginalVariant, selected]
    have yAgreement := Kernel.agreesOn_reference_congr y variant reference sample variantY
    have wAgreement := Kernel.agreesOn_reference_congr w variant reference sample variantW
    have zAgreement := Kernel.agreesOn_reference_congr z variant sample sample variantZ
    have targetParts : Kernel.agreesOn y reference sample = true ∧
        Kernel.agreesOn w reference sample = true := by
      simpa [Kernel.numeratorEvent] using targetHolds
    have yTrue : Kernel.agreesOn y variant sample = true := by
      rw [yAgreement]
      exact targetParts.1
    have wTrue : Kernel.agreesOn w variant sample = true := by
      rw [wAgreement]
      exact targetParts.2
    have zTrue : Kernel.agreesOn z variant sample = true := by
      rw [zAgreement]
      apply (finAll_eq_true_iff _).mpr
      intro i
      cases z i <;> simp
    simp [Kernel.numeratorEvent, Kernel.agreesOn_union, yTrue, zTrue, wTrue]

/-- Finite marginalization partitions a joint cylinder over its marginalized values. -/
noncomputable def marginalization_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment) (disjoint : FourWayDisjoint x y z w)
    (leftSupported : SupportedAt model (.kernel ⟨y, x, w⟩) assignment)
    (_rightSupported : SupportedAt model
      (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment) :
    EquivalentAt model
      (.kernel ⟨y, x, w⟩)
      (.marginalize z (.kernel ⟨NodeSet.union y z, x, w⟩)) assignment := by
  let variants := marginalAssignments S z assignment
  let leftKernel : Kernel S := ⟨y, x, w⟩
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let distribution := leftKernel.distribution model assignment
  let denominator := distribution.probVal (leftKernel.conditionEvent assignment)
  let total := distribution.probVal (leftKernel.numeratorEvent assignment)
  let numerator : S.Assignment -> QProb := fun variant =>
    distribution.probVal (jointKernel.numeratorEvent variant)
  have pairwise :
      (variants.map (fun variant => jointKernel.numeratorEvent variant)).Pairwise
        Probability.disjoint := by
    simpa only [variants, jointKernel] using
      marginal_numerator_events_pairwise y z x w assignment
  have union : Probability.unionList
      (variants.map (fun variant => jointKernel.numeratorEvent variant)) =
        leftKernel.numeratorEvent assignment := by
    simpa only [variants, jointKernel, leftKernel] using
      marginal_numerator_union y z x w assignment disjoint.yz
        disjoint.zw.symm
  have numeratorSum : QProb.Equiv total
      (QProb.listSum (variants.map numerator)) := by
    have additive := distribution.finite_additivity_family
      (variants.map (fun variant => jointKernel.numeratorEvent variant)) pairwise
    rw [union] at additive
    simpa only [total, numerator, List.map_map, Function.comp_apply] using additive
  have leftCanonical : ProbabilityResult.Equivalent
      (leftKernel.denote model assignment)
      (ProbabilityResult.divide (some total) (some denominator)) := by
    exact ProbabilityResult.divide_congr
      (.value (QProb.equiv_refl _)) (.value (QProb.equiv_refl _))
  have variantCanonical : ∀ variant, variant ∈ variants ->
      ProbabilityResult.Equivalent
        (jointKernel.denote model variant)
        (ProbabilityResult.divide (some (numerator variant)) (some denominator)) := by
    intro variant member
    have outside := (mem_marginalAssignments_iff S z assignment variant).mp
      (by simpa only [variants] using member)
    have actionAgreement : ∀ i, x i = true -> variant i = assignment i := by
      intro i selected
      exact outside i (disjoint.xz i selected)
    have conditionAgreement : ∀ i, w i = true -> variant i = assignment i := by
      intro i selected
      exact outside i (disjoint.zw.symm i selected)
    have distributionEq : jointKernel.distribution model variant = distribution := by
      simpa only [jointKernel, leftKernel, distribution] using
        Kernel.distribution_eq_of_action_reference model
          (NodeSet.union y z) y x w w variant assignment actionAgreement
    have denominatorEq : QProb.Equiv
        ((jointKernel.distribution model variant).probVal
          (jointKernel.conditionEvent variant)) denominator := by
      rw [distributionEq]
      apply FiniteProbRecord.probVal_congr
      intro sample
      exact Kernel.agreesOn_reference_congr w variant assignment sample
        conditionAgreement
    have numeratorEq : QProb.Equiv
        ((jointKernel.distribution model variant).probVal
          (jointKernel.numeratorEvent variant)) (numerator variant) := by
      rw [distributionEq]
      exact QProb.equiv_refl _
    simpa only [Kernel.denote] using
      ProbabilityResult.divide_congr (.value numeratorEq) (.value denominatorEq)
  have rightCanonical : ProbabilityResult.Equivalent
      ((ProbabilityTerm.marginalize z (.kernel jointKernel)).denote model assignment)
      (ProbabilityResult.sum (variants.map (fun variant =>
        ProbabilityResult.divide (some (numerator variant)) (some denominator)))) := by
    simpa only [ProbabilityTerm.denote, variants] using
      ProbabilityResult.sum_map_congr_mem variants
        (fun variant => jointKernel.denote model variant)
        (fun variant =>
          ProbabilityResult.divide (some (numerator variant)) (some denominator))
        variantCanonical
  let leftListCanonical : ProbabilityResult.Equivalent
      (leftKernel.denote model assignment)
      (ProbabilityResult.divide
        (some (QProb.listSum (variants.map numerator))) (some denominator)) :=
    ProbabilityResult.trans leftCanonical
      (ProbabilityResult.divide_congr (.value numeratorSum)
        (.value (QProb.equiv_refl _)))
  have listSupported : ProbabilityResult.Supported
      (ProbabilityResult.divide
        (some (QProb.listSum (variants.map numerator))) (some denominator)) :=
    ProbabilityResult.Supported.transport leftListCanonical (by
      simpa only [leftKernel, SupportedAt, denote] using leftSupported)
  exact ProbabilityResult.trans leftListCanonical
    (ProbabilityResult.trans
      (ProbabilityResult.divide_listSum_same_denominator
        (variants.map numerator) denominator listSupported)
      (by
        simpa only [List.map_map, Function.comp_apply] using
          ProbabilityResult.symm rightCanonical))

/-- Conditioning is the quotient of a joint kernel by its conditioning kernel. -/
noncomputable def conditioning_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment)
    (leftSupported : SupportedAt model
      (.kernel ⟨y, x, NodeSet.union z w⟩) assignment)
    (rightSupported : SupportedAt model
      (.divide
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.kernel ⟨z, x, w⟩)) assignment) :
    EquivalentAt model
      (.kernel ⟨y, x, NodeSet.union z w⟩)
      (.divide
        (.kernel ⟨NodeSet.union y z, x, w⟩)
        (.kernel ⟨z, x, w⟩)) assignment := by
  let leftKernel : Kernel S := ⟨y, x, NodeSet.union z w⟩
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let conditionKernel : Kernel S := ⟨z, x, w⟩
  let distribution := leftKernel.distribution model assignment
  let jointEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn y assignment sample &&
      Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let conditionEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let baseEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn w assignment sample
  let numerator := distribution.probVal jointEvent
  let middle := distribution.probVal conditionEvent
  let denominator := distribution.probVal baseEvent
  have jointDistribution :
      jointKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      (NodeSet.union y z) y x w (NodeSet.union z w) assignment
  have conditionDistribution :
      conditionKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      z y x w (NodeSet.union z w) assignment
  have leftNumerator : QProb.Equiv
      ((leftKernel.distribution model assignment).probVal
        (leftKernel.numeratorEvent assignment)) numerator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [leftKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have leftDenominator : QProb.Equiv
      ((leftKernel.distribution model assignment).probVal
        (leftKernel.conditionEvent assignment)) middle := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [leftKernel, conditionEvent, Kernel.conditionEvent,
      Kernel.agreesOn_union]
  have jointNumerator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.numeratorEvent assignment)) numerator := by
    rw [jointDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [jointKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have jointDenominator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.conditionEvent assignment)) denominator := by
    rw [jointDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionNumerator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.numeratorEvent assignment)) middle := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionDenominator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.conditionEvent assignment)) denominator := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  let leftCanonical : ProbabilityResult.Equivalent
      (leftKernel.denote model assignment)
      (ProbabilityResult.divide (some numerator) (some middle)) := by
    simpa only [Kernel.denote] using ProbabilityResult.divide_congr
      (.value leftNumerator) (.value leftDenominator)
  let rightCanonical : ProbabilityResult.Equivalent
      (ProbabilityResult.divide
        (jointKernel.denote model assignment)
        (conditionKernel.denote model assignment))
      (ProbabilityResult.divide
        (ProbabilityResult.divide (some numerator) (some denominator))
        (ProbabilityResult.divide (some middle) (some denominator))) := by
    apply ProbabilityResult.divide_congr
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value jointNumerator) (.value jointDenominator)
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value conditionNumerator) (.value conditionDenominator)
  have leftSupported' : ProbabilityResult.Supported
      (ProbabilityResult.divide (some numerator) (some middle)) :=
    ProbabilityResult.Supported.transport leftCanonical (by
      simpa only [leftKernel, SupportedAt, denote] using leftSupported)
  have rightSupported' : ProbabilityResult.Supported
      (ProbabilityResult.divide
        (ProbabilityResult.divide (some numerator) (some denominator))
        (ProbabilityResult.divide (some middle) (some denominator))) :=
    ProbabilityResult.Supported.transport rightCanonical (by
      simpa only [jointKernel, conditionKernel, SupportedAt, denote] using
        rightSupported)
  exact ProbabilityResult.trans leftCanonical
    (ProbabilityResult.trans
      (ProbabilityResult.divide_divide_cancel numerator middle denominator
        leftSupported' rightSupported')
      (ProbabilityResult.symm rightCanonical))

/-- The product of adjacent conditional kernels is their joint kernel. -/
noncomputable def chain_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (assignment : S.Assignment)
    (leftSupported : SupportedAt model
      (.kernel ⟨NodeSet.union y z, x, w⟩) assignment)
    (rightSupported : SupportedAt model
      (.multiply
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.kernel ⟨z, x, w⟩)) assignment) :
    EquivalentAt model
      (.kernel ⟨NodeSet.union y z, x, w⟩)
      (.multiply
        (.kernel ⟨y, x, NodeSet.union z w⟩)
        (.kernel ⟨z, x, w⟩)) assignment := by
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let conditionalKernel : Kernel S := ⟨y, x, NodeSet.union z w⟩
  let conditionKernel : Kernel S := ⟨z, x, w⟩
  let distribution := jointKernel.distribution model assignment
  let jointEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn y assignment sample &&
      Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let middleEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn z assignment sample &&
      Kernel.agreesOn w assignment sample
  let baseEvent : S.Assignment -> Bool := fun sample =>
    Kernel.agreesOn w assignment sample
  let numerator := distribution.probVal jointEvent
  let middle := distribution.probVal middleEvent
  let denominator := distribution.probVal baseEvent
  have conditionalDistribution :
      conditionalKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      y (NodeSet.union y z) x (NodeSet.union z w) w assignment
  have conditionDistribution :
      conditionKernel.distribution model assignment = distribution := by
    exact Kernel.distribution_eq_of_action model
      z (NodeSet.union y z) x w w assignment
  have jointNumerator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.numeratorEvent assignment)) numerator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [jointKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have jointDenominator : QProb.Equiv
      ((jointKernel.distribution model assignment).probVal
        (jointKernel.conditionEvent assignment)) denominator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionalNumerator : QProb.Equiv
      ((conditionalKernel.distribution model assignment).probVal
        (conditionalKernel.numeratorEvent assignment)) numerator := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have conditionalDenominator : QProb.Equiv
      ((conditionalKernel.distribution model assignment).probVal
        (conditionalKernel.conditionEvent assignment)) middle := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, middleEvent, Kernel.conditionEvent,
      Kernel.agreesOn_union]
  have conditionNumerator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.numeratorEvent assignment)) middle := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  have conditionDenominator : QProb.Equiv
      ((conditionKernel.distribution model assignment).probVal
        (conditionKernel.conditionEvent assignment)) denominator := by
    rw [conditionDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    rfl
  let leftCanonical : ProbabilityResult.Equivalent
      (jointKernel.denote model assignment)
      (ProbabilityResult.divide (some numerator) (some denominator)) := by
    simpa only [Kernel.denote] using ProbabilityResult.divide_congr
      (.value jointNumerator) (.value jointDenominator)
  let rightCanonical : ProbabilityResult.Equivalent
      (ProbabilityResult.multiply
        (conditionalKernel.denote model assignment)
        (conditionKernel.denote model assignment))
      (ProbabilityResult.multiply
        (ProbabilityResult.divide (some numerator) (some middle))
        (ProbabilityResult.divide (some middle) (some denominator))) := by
    apply ProbabilityResult.multiply_congr
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value conditionalNumerator) (.value conditionalDenominator)
    · simpa only [Kernel.denote] using ProbabilityResult.divide_congr
        (.value conditionNumerator) (.value conditionDenominator)
  have leftSupported' : ProbabilityResult.Supported
      (ProbabilityResult.divide (some numerator) (some denominator)) :=
    ProbabilityResult.Supported.transport leftCanonical (by
      simpa only [jointKernel, SupportedAt, denote] using leftSupported)
  have rightSupported' : ProbabilityResult.Supported
      (ProbabilityResult.multiply
        (ProbabilityResult.divide (some numerator) (some middle))
        (ProbabilityResult.divide (some middle) (some denominator))) :=
    ProbabilityResult.Supported.transport rightCanonical (by
      simpa only [conditionalKernel, conditionKernel, SupportedAt, denote] using
        rightSupported)
  exact ProbabilityResult.trans leftCanonical
    (ProbabilityResult.trans
      (ProbabilityResult.divide_multiply_chain numerator middle denominator
        leftSupported' rightSupported')
      (ProbabilityResult.symm rightCanonical))

end ProbabilityTerm

namespace Kernel

def productRecord (model : FiniteLatentSCM S) :
    FiniteProbRecord model.latent.Assignment :=
  FiniteProduct.record model.latent.count model.latent.Value model.factor

def productMass (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) : QProb :=
  (productRecord model).probVal
    (fun roots => event
      (model.evalUnder (kernel.intervention reference) roots))

/-- The latent event whose canonical-product mass is `productMass`. -/
def productPreimage (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    model.latent.Assignment -> Bool :=
  fun roots => event
    (model.evalUnder (kernel.intervention reference) roots)

/-- Agreement cylinders are unchanged when the latent assignments agree on
all roots relevant to a backward-closed node set containing the cylinder. -/
theorem agreesOn_evalUnder_congr_of_rootAgreement
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (relevant observed : NodeSet S) (reference : S.Assignment)
    (closed : model.BackwardClosedUnder intervention relevant)
    (contained : NodeSet.Subset observed relevant)
    (left right : model.latent.Assignment)
    (rootsAgree : forall root,
      model.latentRelevantUnder intervention relevant root = true ->
      left root = right root) :
    Kernel.agreesOn observed reference (model.evalUnder intervention left) =
      Kernel.agreesOn observed reference
        (model.evalUnder intervention right) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro child
  cases selected : observed child with
  | false => rfl
  | true =>
      have relevantChild := contained child selected
      have evaluated := model.evalUnder_eq_on_of_rootAgreement intervention
        relevant closed left right rootsAgree child relevantChild
      simp only [↓reduceIte]
      rw [evaluated]

theorem agreesOn_evalUnder_dependsOnSelected
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (relevant observed : NodeSet S) (reference : S.Assignment)
    (closed : model.BackwardClosedUnder intervention relevant)
    (contained : NodeSet.Subset observed relevant) :
    CanonicalFactorization.DependsOnSelected model.latent.count
      model.latent.Value (model.latentRelevantUnder intervention relevant)
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder intervention roots)) := by
  intro left right rootsAgree
  exact agreesOn_evalUnder_congr_of_rootAgreement model intervention
    relevant observed reference closed contained left right rootsAgree

/-- If two backward-closed regions share no latent root, a cylinder over the
right region depends only on coordinates unselected by the left region. -/
theorem agreesOn_evalUnder_dependsOnUnselected
    (model : FiniteLatentSCM S)
    (intervention : (i : Fin S.count) -> Option (S.Value i))
    (leftRelevant rightRelevant observed : NodeSet S)
    (reference : S.Assignment)
    (rightClosed : model.BackwardClosedUnder intervention rightRelevant)
    (contained : NodeSet.Subset observed rightRelevant)
    (separated : model.LatentSeparatedUnder intervention
      leftRelevant rightRelevant) :
    CanonicalFactorization.DependsOnUnselected model.latent.count
      model.latent.Value
        (model.latentRelevantUnder intervention leftRelevant)
      (fun roots => Kernel.agreesOn observed reference
        (model.evalUnder intervention roots)) := by
  intro left right rootsAgree
  apply agreesOn_evalUnder_congr_of_rootAgreement model intervention
    rightRelevant observed reference rightClosed contained
  intro root rightRelevantRoot
  apply rootsAgree root
  cases leftRelevantRoot :
      model.latentRelevantUnder intervention leftRelevant root with
  | false => rfl
  | true =>
      have impossible := separated root leftRelevantRoot
      rw [rightRelevantRoot] at impossible
      contradiction

/-- Adding hard interventions at nodes that already have their requested
values under a base intervention does not change the evaluated assignment. -/
theorem evalUnder_union_intervention_eq_of_agreesOn
    (model : FiniteLatentSCM S) (baseAction addedAction : NodeSet S)
    (reference : S.Assignment) (roots : model.latent.Assignment)
    (agreement : Kernel.agreesOn addedAction reference
      (model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) roots) = true) :
    model.evalUnder
        ((Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
          NodeSet.empty).intervention reference) roots =
      model.evalUnder
        ((Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
          reference) roots := by
  let base := (Kernel.mk NodeSet.empty baseAction NodeSet.empty).intervention
    reference
  let extension :=
    (Kernel.mk NodeSet.empty (NodeSet.union baseAction addedAction)
      NodeSet.empty).intervention reference
  have addedAgrees : forall node, addedAction node = true ->
      model.evalUnder base roots node = reference node := by
    intro node selected
    have components := (finAll_eq_true_iff _).mp agreement node
    simpa [Kernel.agreesOn, base, selected] using components
  apply model.evalUnder_composition base extension roots
  · intro node extensionNone
    cases baseSelected : baseAction node with
    | false => simp [base, Kernel.intervention, baseSelected]
    | true =>
        simp [extension, Kernel.intervention, NodeSet.union,
          baseSelected] at extensionNone
  · intro node value extensionValue
    cases baseSelected : baseAction node with
    | true =>
        have referenceEq : reference node = value := by
          simpa [extension, Kernel.intervention, NodeSet.union,
            baseSelected] using extensionValue
        subst value
        apply model.evalUnder_effectiveness
        simp [base, Kernel.intervention, baseSelected]
    | false =>
        cases addedSelected : addedAction node with
        | false =>
            simp [extension, Kernel.intervention, NodeSet.union,
              baseSelected, addedSelected] at extensionValue
        | true =>
            have referenceEq : reference node = value := by
              simpa [extension, Kernel.intervention, NodeSet.union,
                baseSelected, addedSelected] using extensionValue
            subst value
            exact addedAgrees node addedSelected

theorem productRecord_singleton_qProduct (model : FiniteLatentSCM S)
    (assignment : model.latent.Assignment) :
    QProb.Equiv
      ((productRecord model).probVal
        (FiniteProbRecord.singletonEvent assignment))
      (FiniteProduct.qProduct model.latent.count (fun root =>
        (model.factor root).probVal
          (FiniteProbRecord.singletonEvent (assignment root)))) := by
  let events := FiniteLatentSCM.assignmentEvents model assignment
  have rectangular := FiniteProduct.record_rectangular_probVal
    model.latent.count model.latent.Value model.factor events
  have eventEq : FiniteProduct.rectangularEvent model.latent.count
      model.latent.Value events =
        FiniteProbRecord.singletonEvent assignment := by
    simpa [events, LatentExtension.rectangularEvent] using
      FiniteLatentSCM.rectangular_assignmentEvents model assignment
  rw [eventEq] at rectangular
  simpa [productRecord, events, FiniteLatentSCM.assignmentEvents] using
    rectangular

/-- Point-mass products in the canonical latent record are invariant under
coordinate splicing. -/
theorem productRecord_singleton_splice_mul (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (left right : model.latent.Assignment) :
    QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal
          (FiniteProbRecord.singletonEvent left))
        ((productRecord model).probVal
          (FiniteProbRecord.singletonEvent right)))
      (QProb.mul
        ((productRecord model).probVal (FiniteProbRecord.singletonEvent
          (CanonicalFactorization.spliceAssignment model.latent.count
            model.latent.Value selected left right)))
        ((productRecord model).probVal (FiniteProbRecord.singletonEvent
          (CanonicalFactorization.spliceAssignment model.latent.count
            model.latent.Value selected right left)))) := by
  let weight := fun (root : Fin model.latent.count)
      (value : model.latent.Value root) =>
    (model.factor root).probVal (FiniteProbRecord.singletonEvent value)
  have leftPoint := productRecord_singleton_qProduct model left
  have rightPoint := productRecord_singleton_qProduct model right
  have firstSplicePoint := productRecord_singleton_qProduct model
    (CanonicalFactorization.spliceAssignment model.latent.count
      model.latent.Value selected left right)
  have secondSplicePoint := productRecord_singleton_qProduct model
    (CanonicalFactorization.spliceAssignment model.latent.count
      model.latent.Value selected right left)
  have swap := CanonicalFactorization.qProduct_splice_mul
    model.latent.count model.latent.Value weight selected left right
  exact QProb.equiv_trans (QProb.mul_congr leftPoint rightPoint)
    (QProb.equiv_trans (by simpa [weight] using swap)
      (QProb.equiv_symm
        (QProb.mul_congr firstSplicePoint secondSplicePoint)))

/-- Events depending on complementary families of independent latent roots
satisfy the denominator-free independence identity.  The factor
`P(topEvent)` is retained so the statement is valid for the unreduced
rational presentations used by `QProb`. -/
theorem productRecord_complementary_independence
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedEvent unselectedEvent : model.latent.Assignment -> Bool)
    (selectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedEvent)
    (unselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedEvent) :
    QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal selectedEvent)
        ((productRecord model).probVal unselectedEvent))
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter selectedEvent unselectedEvent))
        ((productRecord model).probVal Probability.topEvent)) := by
  letI : DecidableEq model.latent.Assignment :=
    FiniteProduct.assignmentDecidableEq model.latent.count
      model.latent.Value model.latent.valueDecidableEq
  let values := FiniteLatentSCM.factorizationAssignments model
  let pointMass := fun assignment : model.latent.Assignment =>
    (productRecord model).probVal
      (FiniteProbRecord.singletonEvent assignment)
  let pairMass := fun pair :
      model.latent.Assignment × model.latent.Assignment =>
    QProb.mul (pointMass pair.1) (pointMass pair.2)
  let source := CanonicalFactorization.pairList
    (values.filter selectedEvent) (values.filter unselectedEvent)
  let target := CanonicalFactorization.pairList
    (values.filter (Probability.inter selectedEvent unselectedEvent)) values
  have valuesNodup : values.Nodup := by
    exact FiniteLatentSCM.factorizationAssignments_nodup model
  have valuesComplete : forall value, value ∈ values := by
    exact FiniteLatentSCM.factorizationAssignments_complete model
  have expand (event : model.latent.Assignment -> Bool) :=
    FiniteProbRecord.probVal_equiv_listSum_singletons
      (productRecord model) values valuesNodup valuesComplete event
  have sourceExpansion : QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal selectedEvent)
        ((productRecord model).probVal unselectedEvent))
      (QProb.listSum (source.map pairMass)) := by
    have multiplyExpanded := QProb.listSum_mul_listSum
      ((values.filter selectedEvent).map pointMass)
      ((values.filter unselectedEvent).map pointMass)
    have flattenExpanded := QProb.listSum_flatMap
      (values.filter selectedEvent) (fun first =>
        (values.filter unselectedEvent).map (fun second =>
          pairMass (first, second)))
    exact QProb.equiv_trans
      (QProb.mul_congr (expand selectedEvent) (expand unselectedEvent))
      (QProb.equiv_trans multiplyExpanded (by
        simpa [source, CanonicalFactorization.pairList, pairMass,
          pointMass, List.map_map, List.map_flatMap,
          Function.comp_apply] using QProb.equiv_symm flattenExpanded))
  have targetExpansion : QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter selectedEvent unselectedEvent))
        ((productRecord model).probVal Probability.topEvent))
      (QProb.listSum (target.map pairMass)) := by
    have topFilter : values.filter Probability.topEvent = values := by
      induction values with
      | nil => rfl
      | cons value values ih =>
          simp [Probability.topEvent, ih]
    have expandTop : QProb.Equiv
        ((productRecord model).probVal Probability.topEvent)
        (QProb.listSum (values.map pointMass)) := by
      have expanded := expand Probability.topEvent
      rw [topFilter] at expanded
      exact expanded
    have multiplyExpanded := QProb.listSum_mul_listSum
      ((values.filter
        (Probability.inter selectedEvent unselectedEvent)).map pointMass)
      (values.map pointMass)
    have flattenExpanded := QProb.listSum_flatMap
      (values.filter (Probability.inter selectedEvent unselectedEvent))
      (fun first => values.map (fun second => pairMass (first, second)))
    exact QProb.equiv_trans
      (QProb.mul_congr
        (expand (Probability.inter selectedEvent unselectedEvent))
        expandTop)
      (QProb.equiv_trans multiplyExpanded (by
        simpa [target, CanonicalFactorization.pairList, pairMass,
          pointMass, Probability.topEvent, List.map_map, List.map_flatMap,
          Function.comp_apply, Function.comp_def] using
            QProb.equiv_symm flattenExpanded))
  have pairPermutation := CanonicalFactorization.swapPair_eventPairs_perm
    model.latent.count model.latent.Value selected values valuesNodup
    valuesComplete selectedEvent unselectedEvent selectedDepends
    unselectedDepends
  have pointwise : forall pair :
      model.latent.Assignment × model.latent.Assignment,
      QProb.Equiv (pairMass pair)
        (pairMass (CanonicalFactorization.swapPair model.latent.count
          model.latent.Value selected pair)) := by
    intro pair
    simpa [pairMass, pointMass, CanonicalFactorization.swapPair] using
      productRecord_singleton_splice_mul model selected pair.1 pair.2
  have reindexed : QProb.Equiv
      (QProb.listSum (source.map pairMass))
      (QProb.listSum (target.map pairMass)) := by
    exact QProb.equiv_trans
      (QProb.listSum_map_congr source pairMass
        (fun pair => pairMass
          (CanonicalFactorization.swapPair model.latent.count
            model.latent.Value selected pair)) pointwise)
      (by
        have mappedPermutation := pairPermutation.map pairMass
        simpa [source, target, List.map_map] using
          QProb.listSum_perm mappedPermutation)
  exact QProb.equiv_trans sourceExpansion
    (QProb.equiv_trans reindexed (QProb.equiv_symm targetExpansion))

/-- Normalization removes the explicit `P(topEvent)` factor from the
denominator-free product identity. -/
theorem productRecord_inter_equiv_mul
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedEvent unselectedEvent : model.latent.Assignment -> Bool)
    (selectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedEvent)
    (unselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedEvent) :
    QProb.Equiv
      ((productRecord model).probVal
        (Probability.inter selectedEvent unselectedEvent))
      (QProb.mul
        ((productRecord model).probVal selectedEvent)
        ((productRecord model).probVal unselectedEvent)) := by
  let intersection := (productRecord model).probVal
    (Probability.inter selectedEvent unselectedEvent)
  let whole := (productRecord model).probVal Probability.topEvent
  have independent := productRecord_complementary_independence model selected
    selectedEvent unselectedEvent selectedDepends unselectedDepends
  have normalized : QProb.Equiv whole QProb.one :=
    (productRecord model).normalization
  exact QProb.equiv_trans (QProb.equiv_symm (QProb.mul_one intersection))
    (QProb.equiv_trans
      (QProb.mul_congr (QProb.equiv_refl intersection)
        (QProb.equiv_symm normalized))
      (by simpa [intersection, whole] using QProb.equiv_symm independent))

/-- Conditional independence in cross-product form.  A common conditioning
event may have one component on each side of the latent-root partition. -/
theorem productRecord_conditional_independence_cross
    (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (selectedOutcome selectedCondition unselectedOutcome
      unselectedCondition : model.latent.Assignment -> Bool)
    (selectedOutcomeDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedOutcome)
    (selectedConditionDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected selectedCondition)
    (unselectedOutcomeDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedOutcome)
    (unselectedConditionDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected unselectedCondition) :
    QProb.Equiv
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter
            (Probability.inter selectedOutcome selectedCondition)
            unselectedCondition))
        ((productRecord model).probVal
          (Probability.inter selectedCondition
            (Probability.inter unselectedOutcome unselectedCondition))))
      (QProb.mul
        ((productRecord model).probVal
          (Probability.inter
            (Probability.inter selectedOutcome selectedCondition)
            (Probability.inter unselectedOutcome unselectedCondition)))
        ((productRecord model).probVal
          (Probability.inter selectedCondition unselectedCondition))) := by
  let selectedJoint := Probability.inter selectedOutcome selectedCondition
  let unselectedJoint := Probability.inter unselectedOutcome unselectedCondition
  have selectedJointDepends := CanonicalFactorization.DependsOnSelected.inter
    model.latent.count model.latent.Value selected
      selectedOutcome selectedCondition selectedOutcomeDepends
      selectedConditionDepends
  have unselectedJointDepends :=
    CanonicalFactorization.DependsOnUnselected.inter model.latent.count
      model.latent.Value selected unselectedOutcome unselectedCondition
      unselectedOutcomeDepends unselectedConditionDepends
  have leftFactor := productRecord_inter_equiv_mul model selected
    selectedJoint unselectedCondition selectedJointDepends
    unselectedConditionDepends
  have rightFactor := productRecord_inter_equiv_mul model selected
    selectedCondition unselectedJoint selectedConditionDepends
    unselectedJointDepends
  have jointFactor := productRecord_inter_equiv_mul model selected
    selectedJoint unselectedJoint selectedJointDepends unselectedJointDepends
  have conditionFactor := productRecord_inter_equiv_mul model selected
    selectedCondition unselectedCondition selectedConditionDepends
    unselectedConditionDepends
  exact QProb.equiv_trans (QProb.mul_congr leftFactor rightFactor)
    (QProb.equiv_trans (by
      simp only [QProb.Equiv, QProb.mul]
      ac_rfl)
      (QProb.equiv_symm (QProb.mul_congr jointFactor conditionFactor)))

/-- Every kernel distribution is a pushforward of the canonical independent
latent product, including the action-free branch. -/
theorem distribution_probVal_productRecord
    (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (event : S.Assignment -> Bool) :
    QProb.Equiv ((kernel.distribution model reference).probVal event)
      (productMass model kernel reference event) := by
  unfold productMass productRecord
  cases actionValue : kernel.hasAction with
  | true =>
      simpa [Kernel.distribution, actionValue,
        FiniteLatentSCM.interventionalValue] using
        model.interventionalValue_productRecord
          (kernel.intervention reference) event
  | false =>
      have noAction : forall node, kernel.action node = false :=
        (finAny_eq_false_iff kernel.action).mp (by
          simpa [Kernel.hasAction] using actionValue)
      have noIntervention : kernel.intervention reference =
          FiniteLatentSCM.noIntervention S := by
        funext node
        simp [Kernel.intervention, FiniteLatentSCM.noIntervention,
          noAction node]
      rw [noIntervention]
      simpa [Kernel.distribution, actionValue,
        FiniteLatentSCM.observationalValue,
        FiniteLatentSCM.evalUnder_noIntervention, productMass,
        productRecord] using
        model.observationalValue_productRecord event

/-- The denominator-free cross-product obligation for two conditional kernels. -/
structure CrossProductEquivalentAt (model : FiniteLatentSCM S)
    (left right : Kernel S) (assignment : S.Assignment) : Prop where
  cross : QProb.Equiv
    (QProb.mul
      ((left.distribution model assignment).probVal
        (left.numeratorEvent assignment))
      ((right.distribution model assignment).probVal
        (right.conditionEvent assignment)))
    (QProb.mul
      ((right.distribution model assignment).probVal
        (right.numeratorEvent assignment))
      ((left.distribution model assignment).probVal
        (left.conditionEvent assignment)))

/-- The same cross-product obligation after replacing the supplied latent
prior by its canonical independent product record. -/
structure ProductCrossProductEquivalentAt (model : FiniteLatentSCM S)
    (left right : Kernel S) (assignment : S.Assignment) : Prop where
  cross : QProb.Equiv
    (QProb.mul
      (productMass model left assignment (left.numeratorEvent assignment))
      (productMass model right assignment (right.conditionEvent assignment)))
    (QProb.mul
      (productMass model right assignment (right.numeratorEvent assignment))
      (productMass model left assignment (left.conditionEvent assignment)))

theorem ProductCrossProductEquivalentAt.symm
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : ProductCrossProductEquivalentAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model right left assignment :=
  ⟨QProb.equiv_symm equivalent.cross⟩

/-- A concrete latent partition witnessing the conditional-independence
identity required by a pair of kernels.  The four equalities isolate the
intervention/structural-equation work; the four dependence fields isolate the
graph-separation work. -/
structure ProductConditionalIndependenceWitnessAt
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  selectedOutcome : model.latent.Assignment -> Bool
  selectedCondition : model.latent.Assignment -> Bool
  unselectedOutcome : model.latent.Assignment -> Bool
  unselectedCondition : model.latent.Assignment -> Bool
  selectedOutcomeDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedOutcome
  selectedConditionDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedCondition
  unselectedOutcomeDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedOutcome
  unselectedConditionDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedCondition
  leftNumerator :
    productPreimage model left assignment (left.numeratorEvent assignment) =
      Probability.inter
        (Probability.inter selectedOutcome selectedCondition)
        (Probability.inter unselectedOutcome unselectedCondition)
  rightCondition :
    productPreimage model right assignment (right.conditionEvent assignment) =
      Probability.inter selectedCondition unselectedCondition
  rightNumerator :
    productPreimage model right assignment (right.numeratorEvent assignment) =
      Probability.inter selectedCondition
        (Probability.inter unselectedOutcome unselectedCondition)
  leftCondition :
    productPreimage model left assignment (left.conditionEvent assignment) =
      Probability.inter
        (Probability.inter selectedOutcome selectedCondition)
        unselectedCondition

/-- Build the latent conditional-independence witness for rule 1 from two
backward-closed, latent-separated regions and a partition of the common
conditioning nodes. -/
def rule1PartitionWitness (model : FiniteLatentSCM S)
    (x y z w wSelected wUnselected leftRelevant rightRelevant : NodeSet S)
    (assignment : S.Assignment)
    (wSplit : w = NodeSet.union wSelected wUnselected)
    (leftClosed : model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment) leftRelevant)
    (rightClosed : model.BackwardClosedUnder
      ((rule1Right x y z w).intervention assignment) rightRelevant)
    (zContained : NodeSet.Subset z leftRelevant)
    (wSelectedContained : NodeSet.Subset wSelected leftRelevant)
    (yContained : NodeSet.Subset y rightRelevant)
    (wUnselectedContained : NodeSet.Subset wUnselected rightRelevant)
    (separated : model.LatentSeparatedUnder
      ((rule1Right x y z w).intervention assignment)
      leftRelevant rightRelevant) :
    ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment := by
  let intervention := (rule1Right x y z w).intervention assignment
  let evaluated := fun roots : model.latent.Assignment =>
    model.evalUnder intervention roots
  let cylinder := fun nodes : NodeSet S => fun roots : model.latent.Assignment =>
    Kernel.agreesOn nodes assignment (evaluated roots)
  refine
    { selected := model.latentRelevantUnder intervention leftRelevant
      selectedOutcome := cylinder z
      selectedCondition := cylinder wSelected
      unselectedOutcome := cylinder y
      unselectedCondition := cylinder wUnselected
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnSelected model intervention leftRelevant z
        assignment leftClosed zContained
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnSelected model intervention leftRelevant
        wSelected assignment leftClosed wSelectedContained
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnUnselected model intervention leftRelevant
        rightRelevant y assignment rightClosed yContained separated
  · simpa [cylinder, evaluated, intervention] using
      agreesOn_evalUnder_dependsOnUnselected model intervention leftRelevant
        rightRelevant wUnselected assignment rightClosed
        wUnselectedContained separated
  · funext roots
    simp only [productPreimage, rule1Left, Kernel.numeratorEvent,
      cylinder, evaluated]
    change
      (Kernel.agreesOn y assignment (model.evalUnder intervention roots) &&
        Kernel.agreesOn (NodeSet.union z w) assignment
          (model.evalUnder intervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union z,
      Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule1Right, Kernel.conditionEvent,
      cylinder, evaluated]
    change Kernel.agreesOn w assignment
      (model.evalUnder intervention roots) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
  · funext roots
    simp only [productPreimage, rule1Right, Kernel.numeratorEvent,
      cylinder, evaluated]
    change
      (Kernel.agreesOn y assignment (model.evalUnder intervention roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder intervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule1Left, Kernel.conditionEvent,
      cylinder, evaluated]
    change Kernel.agreesOn (NodeSet.union z w) assignment
      (model.evalUnder intervention roots) = _
    rw [wSplit, Kernel.agreesOn_union z,
      Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl

/-- Build the rule-2 witness once the four cylinders have been assigned to a
common latent partition.  The cross-world event equalities are discharged by
SCM composition; only the dependence proofs remain graph-specific. -/
def rule2PartitionWitness (model : FiniteLatentSCM S)
    (x y z w wSelected wUnselected : NodeSet S)
    (assignment : S.Assignment)
    (selected : Fin model.latent.count -> Bool)
    (wSplit : w = NodeSet.union wSelected wUnselected)
    (zDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn z assignment
        (model.evalUnder
          ((rule2Right x y z w).intervention assignment) roots)))
    (wSelectedDepends : CanonicalFactorization.DependsOnSelected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn wSelected assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)))
    (yDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn y assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots)))
    (wUnselectedDepends : CanonicalFactorization.DependsOnUnselected
      model.latent.count model.latent.Value selected
      (fun roots => Kernel.agreesOn wUnselected assignment
        (model.evalUnder
          ((rule2Left x y z w).intervention assignment) roots))) :
    ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment := by
  let baseIntervention := (rule2Right x y z w).intervention assignment
  let extendedIntervention := (rule2Left x y z w).intervention assignment
  let baseCylinder := fun nodes : NodeSet S =>
    fun roots : model.latent.Assignment => Kernel.agreesOn nodes assignment
      (model.evalUnder baseIntervention roots)
  let extendedCylinder := fun nodes : NodeSet S =>
    fun roots : model.latent.Assignment => Kernel.agreesOn nodes assignment
      (model.evalUnder extendedIntervention roots)
  refine
    { selected := selected
      selectedOutcome := baseCylinder z
      selectedCondition := extendedCylinder wSelected
      unselectedOutcome := extendedCylinder y
      unselectedCondition := extendedCylinder wUnselected
      selectedOutcomeDepends := ?_
      selectedConditionDepends := ?_
      unselectedOutcomeDepends := ?_
      unselectedConditionDepends := ?_
      leftNumerator := ?_
      rightCondition := ?_
      rightNumerator := ?_
      leftCondition := ?_ }
  · simpa [baseCylinder, baseIntervention] using zDepends
  · simpa [extendedCylinder, extendedIntervention] using wSelectedDepends
  · simpa [extendedCylinder, extendedIntervention] using yDepends
  · simpa [extendedCylinder, extendedIntervention] using wUnselectedDepends
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.numeratorEvent,
      baseCylinder, extendedCylinder]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder baseIntervention roots) &&
        Kernel.agreesOn (NodeSet.union z w) assignment
          (model.evalUnder baseIntervention roots)) = _
    rw [Kernel.agreesOn_union z w]
    cases zHolds : Kernel.agreesOn z assignment
        (model.evalUnder baseIntervention roots) with
    | false => simp [Probability.inter, zHolds]
    | true =>
        have evaluationsEqual :
            model.evalUnder extendedIntervention roots =
              model.evalUnder baseIntervention roots := by
          simpa [baseIntervention, extendedIntervention, rule2Left,
            rule2Right] using
            evalUnder_union_intervention_eq_of_agreesOn model x z assignment
              roots zHolds
        simp only [Probability.inter]
        rw [evaluationsEqual]
        rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
        simp [zHolds]
        ac_rfl
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.conditionEvent,
      extendedCylinder]
    change Kernel.agreesOn w assignment
      (model.evalUnder extendedIntervention roots) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
  · funext roots
    simp only [productPreimage, rule2Left, Kernel.numeratorEvent,
      extendedCylinder]
    change
      (Kernel.agreesOn y assignment
          (model.evalUnder extendedIntervention roots) &&
        Kernel.agreesOn w assignment
          (model.evalUnder extendedIntervention roots)) = _
    rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
    simp only [Probability.inter]
    ac_rfl
  · funext roots
    simp only [productPreimage, rule2Right, Kernel.conditionEvent,
      baseCylinder, extendedCylinder]
    change Kernel.agreesOn (NodeSet.union z w) assignment
      (model.evalUnder baseIntervention roots) = _
    rw [Kernel.agreesOn_union z w]
    cases zHolds : Kernel.agreesOn z assignment
        (model.evalUnder baseIntervention roots) with
    | false => simp [Probability.inter, zHolds]
    | true =>
        have evaluationsEqual :
            model.evalUnder extendedIntervention roots =
              model.evalUnder baseIntervention roots := by
          simpa [baseIntervention, extendedIntervention, rule2Left,
            rule2Right] using
            evalUnder_union_intervention_eq_of_agreesOn model x z assignment
              roots zHolds
        simp only [Probability.inter]
        rw [evaluationsEqual]
        rw [wSplit, Kernel.agreesOn_union wSelected wUnselected]
        simp [zHolds]

/-- A checked latent partition discharges the canonical-product cross-product
obligation. -/
theorem ProductConditionalIndependenceWitnessAt.toCrossProduct
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (witness : ProductConditionalIndependenceWitnessAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model left right assignment := by
  have conditional := productRecord_conditional_independence_cross model
    witness.selected witness.selectedOutcome witness.selectedCondition
    witness.unselectedOutcome witness.unselectedCondition
    witness.selectedOutcomeDepends witness.selectedConditionDepends
    witness.unselectedOutcomeDepends witness.unselectedConditionDepends
  constructor
  unfold productMass
  change QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.conditionEvent assignment))))
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.conditionEvent assignment))))
  rw [witness.leftNumerator, witness.rightCondition,
    witness.rightNumerator, witness.leftCondition]
  exact QProb.equiv_trans (QProb.equiv_symm conditional)
    (QProb.mul_comm _ _)

/-- A latent event factored across a selected/unselected partition of the
independent roots.  Unlike `ProductConditionalIndependenceWitnessAt`, this
does not require the four kernel events to share any of their two factors. -/
structure ProductEventRectangle (model : FiniteLatentSCM S)
    (selected : Fin model.latent.count -> Bool)
    (event : model.latent.Assignment -> Bool) where
  selectedPart : model.latent.Assignment -> Bool
  unselectedPart : model.latent.Assignment -> Bool
  selectedDepends : CanonicalFactorization.DependsOnSelected
    model.latent.count model.latent.Value selected selectedPart
  unselectedDepends : CanonicalFactorization.DependsOnUnselected
    model.latent.count model.latent.Value selected unselectedPart
  factorization : event = Probability.inter selectedPart unselectedPart

theorem ProductEventRectangle.probVal
    {model : FiniteLatentSCM S}
    {selected : Fin model.latent.count -> Bool}
    {event : model.latent.Assignment -> Bool}
    (rectangle : ProductEventRectangle model selected event) :
    QProb.Equiv ((productRecord model).probVal event)
      (QProb.mul
        ((productRecord model).probVal rectangle.selectedPart)
        ((productRecord model).probVal rectangle.unselectedPart)) := by
  cases rectangle with
  | mk selectedPart unselectedPart selectedDepends unselectedDepends
      factorization =>
      subst event
      exact productRecord_inter_equiv_mul model selected
        selectedPart unselectedPart selectedDepends unselectedDepends

/-- A general rectangular factorization of a kernel cross product.

The selected and unselected factors may differ in all four kernel events.
The two component cross identities are therefore expressive enough for
cross-world intervention arguments such as do-calculus Rule 3, without
imposing a pointwise inclusion between the two conditioning events. -/
structure ProductRectangularCrossProductWitnessAt
    (model : FiniteLatentSCM S) (left right : Kernel S)
    (assignment : S.Assignment) where
  selected : Fin model.latent.count -> Bool
  leftNumerator : ProductEventRectangle model selected
    (productPreimage model left assignment (left.numeratorEvent assignment))
  rightCondition : ProductEventRectangle model selected
    (productPreimage model right assignment (right.conditionEvent assignment))
  rightNumerator : ProductEventRectangle model selected
    (productPreimage model right assignment (right.numeratorEvent assignment))
  leftCondition : ProductEventRectangle model selected
    (productPreimage model left assignment (left.conditionEvent assignment))
  selectedCross : QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal leftNumerator.selectedPart)
      ((productRecord model).probVal rightCondition.selectedPart))
    (QProb.mul
      ((productRecord model).probVal rightNumerator.selectedPart)
      ((productRecord model).probVal leftCondition.selectedPart))
  unselectedCross : QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal leftNumerator.unselectedPart)
      ((productRecord model).probVal rightCondition.unselectedPart))
    (QProb.mul
      ((productRecord model).probVal rightNumerator.unselectedPart)
      ((productRecord model).probVal leftCondition.unselectedPart))

/-- Componentwise rectangular cross identities imply the kernel-level
canonical-product cross identity. -/
theorem ProductRectangularCrossProductWitnessAt.toCrossProduct
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (witness : ProductRectangularCrossProductWitnessAt
      model left right assignment) :
    ProductCrossProductEquivalentAt model left right assignment := by
  have leftNumeratorFactor := witness.leftNumerator.probVal
  have rightConditionFactor := witness.rightCondition.probVal
  have rightNumeratorFactor := witness.rightNumerator.probVal
  have leftConditionFactor := witness.leftCondition.probVal
  constructor
  unfold productMass
  change QProb.Equiv
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.conditionEvent assignment))))
    (QProb.mul
      ((productRecord model).probVal
        (productPreimage model right assignment
          (right.numeratorEvent assignment)))
      ((productRecord model).probVal
        (productPreimage model left assignment
          (left.conditionEvent assignment))))
  exact QProb.equiv_trans
    (QProb.mul_congr leftNumeratorFactor rightConditionFactor)
    (QProb.equiv_trans (by
      simp only [QProb.Equiv, QProb.mul]
      ac_rfl)
      (QProb.equiv_trans
        (QProb.mul_congr witness.selectedCross witness.unselectedCross)
        (QProb.equiv_trans (by
          simp only [QProb.Equiv, QProb.mul]
          ac_rfl)
          (QProb.equiv_symm
            (QProb.mul_congr rightNumeratorFactor
              leftConditionFactor)))))

theorem ProductCrossProductEquivalentAt.toDistribution
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : ProductCrossProductEquivalentAt
      model left right assignment) :
    CrossProductEquivalentAt model left right assignment := by
  let leftNumerator := left.distribution_probVal_productRecord model assignment
    (left.numeratorEvent assignment)
  let leftDenominator := left.distribution_probVal_productRecord model assignment
    (left.conditionEvent assignment)
  let rightNumerator := right.distribution_probVal_productRecord model assignment
    (right.numeratorEvent assignment)
  let rightDenominator := right.distribution_probVal_productRecord model assignment
    (right.conditionEvent assignment)
  refine ⟨QProb.equiv_trans
    (QProb.mul_congr leftNumerator rightDenominator)
    (QProb.equiv_trans equivalent.cross
      (QProb.equiv_symm
        (QProb.mul_congr rightNumerator leftDenominator)))⟩

/-- A cross-product identity yields equality of both supported partial ratios. -/
noncomputable def CrossProductEquivalentAt.denote
    {model : FiniteLatentSCM S} {left right : Kernel S}
    {assignment : S.Assignment}
    (equivalent : CrossProductEquivalentAt model left right assignment)
    (leftSupported : ProbabilityTerm.SupportedAt model (.kernel left) assignment)
    (rightSupported : ProbabilityTerm.SupportedAt model (.kernel right) assignment) :
    ProbabilityResult.Equivalent
      (left.denote model assignment) (right.denote model assignment) := by
  let leftNumerator := (left.distribution model assignment).probVal
    (left.numeratorEvent assignment)
  let leftDenominator := (left.distribution model assignment).probVal
    (left.conditionEvent assignment)
  let rightNumerator := (right.distribution model assignment).probVal
    (right.numeratorEvent assignment)
  let rightDenominator := (right.distribution model assignment).probVal
    (right.conditionEvent assignment)
  have leftPositive : 0 < leftDenominator.num := by
    by_cases positive : 0 < leftDenominator.num
    · exact positive
    · change ProbabilityResult.Supported (left.denote model assignment)
        at leftSupported
      simp only [Kernel.denote, leftDenominator,
        ProbabilityResult.divide, dif_neg positive] at leftSupported
      rcases leftSupported with ⟨_, impossible⟩
      cases impossible
  have rightPositive : 0 < rightDenominator.num := by
    by_cases positive : 0 < rightDenominator.num
    · exact positive
    · change ProbabilityResult.Supported (right.denote model assignment)
        at rightSupported
      simp only [Kernel.denote, rightDenominator,
        ProbabilityResult.divide, dif_neg positive] at rightSupported
      rcases rightSupported with ⟨_, impossible⟩
      cases impossible
  simp only [Kernel.denote, leftDenominator, rightDenominator,
    ProbabilityResult.divide,
    dif_pos leftPositive, dif_pos rightPositive]
  exact .value (QProb.div_equiv_of_cross leftPositive rightPositive
    equivalent.cross)

end Kernel

/--
All graph-dependent work for primitive soundness, stated before ratio algebra.
This is the target of the finite global-Markov/do-calculus proof.
-/
structure PathDoRuleCrossProductSoundness (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  crossProduct : forall {left right} (assignment : S.Assignment),
    PathDoRuleApplication G left right ->
      Kernel.CrossProductEquivalentAt model left right assignment

/-- Separate cross-product obligations for the three do-calculus rules. -/
structure PathDoRuleCrossProductLaws (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.CrossProductEquivalentAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.CrossProductEquivalentAt model
      (rule2Left x y z w) (rule2Right x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.CrossProductEquivalentAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment

/-- The three graph-dependent laws reduced to the canonical independent
latent product.  This is the input expected from the finite factor-graph
separation proof. -/
structure PathDoRuleProductCrossProductLaws (G : ObservedGraph S)
    (model : FiniteLatentSCM S) : Prop where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule2Left x y z w) (rule2Right x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.ProductCrossProductEquivalentAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment

/-- The remaining graph layer may provide explicit latent partitions rather
than opaque kernel-level mass equalities.  Rules 1 and 2 use the stronger
conditional-independence shape.  Rule 3 uses general rectangular factors,
because its two conditioning cylinders live under different interventions
and need not be pointwise nested.  Rule 2 is oriented in reverse because its
composition proof naturally identifies the observational-action kernel as
the joint side of conditional independence. -/
structure PathDoRulePartitionWitnesses (G : ObservedGraph S)
    (model : FiniteLatentSCM S) where
  rule1 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.bar x) y z (NodeSet.union x w) ->
    Kernel.ProductConditionalIndependenceWitnessAt model
      (rule1Left x y z w) (rule1Right x y z w) assignment
  rule2 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    PathSpecification.PathDSeparated
      G (.barUnderline x z) y z (NodeSet.union x w) ->
    Kernel.ProductConditionalIndependenceWitnessAt model
      (rule2Right x y z w) (rule2Left x y z w) assignment
  rule3 : forall (x y z w : NodeSet S) (assignment : S.Assignment),
    FourWayDisjoint x y z w ->
    (let base := GraphMutilation.bar x
     let removable := G.nonAncestorsOf base z w
     PathSpecification.PathDSeparated G
       { removeIncoming := NodeSet.union x removable,
         removeOutgoing := NodeSet.empty }
       y z (NodeSet.union x w)) ->
    Kernel.ProductRectangularCrossProductWitnessAt model
      (rule3Left x y z w) (rule3Right x y z w) assignment

def PathDoRulePartitionWitnesses.toProductCrossProductLaws
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (witnesses : PathDoRulePartitionWitnesses G model) :
    PathDoRuleProductCrossProductLaws G model where
  rule1 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule1 x y z w assignment disjoint separated).toCrossProduct
  rule2 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule2 x y z w assignment disjoint separated).toCrossProduct.symm
  rule3 := by
    intro x y z w assignment disjoint separated
    exact (witnesses.rule3 x y z w assignment disjoint separated).toCrossProduct

def PathDoRuleProductCrossProductLaws.toDistributionLaws
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (laws : PathDoRuleProductCrossProductLaws G model) :
    PathDoRuleCrossProductLaws G model where
  rule1 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule1 x y z w assignment disjoint separated).toDistribution
  rule2 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule2 x y z w assignment disjoint separated).toDistribution
  rule3 := by
    intro x y z w assignment disjoint separated
    exact (laws.rule3 x y z w assignment disjoint separated).toDistribution

/-- Package the three independently checkable laws as application soundness. -/
def PathDoRuleCrossProductLaws.toCrossProductSoundness
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (laws : PathDoRuleCrossProductLaws G model) :
    PathDoRuleCrossProductSoundness G model where
  crossProduct := by
    intro left right assignment application
    cases application with
    | rule1 x y z w disjoint sideCondition =>
        exact laws.rule1 x y z w assignment disjoint sideCondition
    | rule2 x y z w disjoint sideCondition =>
        exact laws.rule2 x y z w assignment disjoint sideCondition
    | rule3 x y z w disjoint sideCondition =>
        exact laws.rule3 x y z w assignment disjoint sideCondition

/-- Cross-product do-rule laws supply the semantic do-rule leaf. -/
noncomputable def PathDoRuleCrossProductSoundness.toDoRule
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (sound : PathDoRuleCrossProductSoundness G model)
    {left right : Kernel S} (assignment : S.Assignment)
    (application : PathDoRuleApplication G left right)
    (_leftSupported : ProbabilityTerm.SupportedAt model (.kernel left) assignment)
    (_rightSupported : ProbabilityTerm.SupportedAt model (.kernel right) assignment) :
    ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
      assignment := by
  simpa only [ProbabilityTerm.denote] using
    (sound.crossProduct assignment application).denote
      _leftSupported _rightSupported

/-- Assemble all primitive laws once the graph-dependent do-rule leaf is supplied. -/
noncomputable def PathPrimitiveSoundness.ofDoRule
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (doRuleSound : ∀ {left right} (assignment : S.Assignment),
      PathDoRuleApplication G left right ->
        ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
        ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
        ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
          assignment) :
    PathPrimitiveSoundness G model where
  doRule := doRuleSound
  marginalization := by
    intro x y z w assignment disjoint leftSupported rightSupported
    exact ProbabilityTerm.marginalization_soundAt model x y z w assignment
      disjoint leftSupported rightSupported
  conditioning := by
    intro x y z w assignment _ leftSupported rightSupported
    exact ProbabilityTerm.conditioning_soundAt model x y z w assignment
      leftSupported rightSupported
  chain := by
    intro x y z w assignment _ leftSupported rightSupported
    exact ProbabilityTerm.chain_soundAt model x y z w assignment
      leftSupported rightSupported

/-- Compile path-based primitive semantics to executable rule syntax using the
proved algorithm-to-path implication.  The converse (path to algorithm) is
inhabited as `ObservedGraph.dSeparationCorrectness` and is used by
`PublishedSoundness`, not by semantic soundness of an executable derivation.
-/
def PathPrimitiveSoundness.compileChecked
    {G : ObservedGraph S} {model : FiniteLatentSCM S}
    (semantics : PathPrimitiveSoundness G model) :
    LocalPrimitiveSoundness G model where
  doRule := by
    intro left right assignment application leftSupported rightSupported
    exact semantics.doRule assignment application.toPathChecked
      leftSupported rightSupported
  marginalization := semantics.marginalization
  conditioning := semantics.conditioning
  chain := semantics.chain

/-- Assemble executable primitive soundness directly from the three path
cross-product laws, without assuming full d-separation completeness. -/
noncomputable def LocalPrimitiveSoundness.ofPathCrossProductLaws
    (model : FiniteLatentSCM S) (G : ObservedGraph S)
    (laws : PathDoRuleCrossProductLaws G model) :
    LocalPrimitiveSoundness G model :=
  (PathPrimitiveSoundness.ofDoRule model G
    laws.toCrossProductSoundness.toDoRule).compileChecked

/--
Soundness package for executable derivations.  Unlike `PublishedSoundness`,
this needs only the proved algorithm-to-path implication; the reverse
direction remains relevant to compiling published path certificates, not to
semantic soundness of an executable derivation.
-/
structure CheckedSoundness (S : ObservedSignature)
    (G : ObservedGraph S) where
  pathPrimitive : forall model : ExactModel S,
    Compatible model G -> PathPrimitiveSoundness G model

def CheckedSoundness.primitive (sound : CheckedSoundness S G)
    (model : ExactModel S) (compatible : Compatible model G) :
    LocalPrimitiveSoundness G model :=
  (sound.pathPrimitive model compatible).compileChecked

/-- Construct the executable package from the remaining global-Markov
cross-product laws. -/
noncomputable def CheckedSoundness.ofCrossProductLaws
    (G : ObservedGraph S)
    (laws : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductLaws G model) :
    CheckedSoundness S G where
  pathPrimitive := by
    intro model compatible
    exact PathPrimitiveSoundness.ofDoRule model G
      (laws model compatible).toCrossProductSoundness.toDoRule

/-- Assemble executable soundness from explicit graph-derived latent
partition witnesses. -/
noncomputable def CheckedSoundness.ofPartitionWitnesses
    (G : ObservedGraph S)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    CheckedSoundness S G :=
  CheckedSoundness.ofCrossProductLaws G (fun model compatible =>
    (witnesses model compatible).toProductCrossProductLaws.toDistributionLaws)

/-- Transport target primitive soundness back to the finite source semantics. -/
noncomputable def PathPrimitiveSoundness.toFiniteSource
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    {model : FiniteTableSCM T}
    (semantics : PathPrimitiveSoundness G.interpret model.interpret) :
    FiniteSourcePathPrimitiveSoundness G model where
  doRule := by
    intro left right assignment application leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.doRule assignment application
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  marginalization := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.marginalization x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  conditioning := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.conditioning x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)
  chain := by
    intro x y z w assignment disjoint leftSupported rightSupported
    apply model.termEquivalentAt_of_target
    exact semantics.chain x y z w assignment disjoint
      (model.termSupportedAt_to_target _ _ leftSupported)
      (model.termSupportedAt_to_target _ _ rightSupported)

/--
The checked constructor isolates the two remaining graph-dependent obligations:
correctness of executable d-separation and semantic validity of a path do-rule.
-/
noncomputable def PublishedSoundness.ofDSeparationDoRule
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (doRuleSound : ∀ (model : ExactModel S), Compatible model G ->
      ∀ {left right} (assignment : S.Assignment),
        PathDoRuleApplication G left right ->
          ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
          ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
          ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
            assignment) :
    PublishedSoundness S G where
  dseparation := correct
  pathPrimitive := by
    intro model compatible
    exact PathPrimitiveSoundness.ofDoRule model G
      (doRuleSound model compatible)

/-- Assemble published soundness from raw global-Markov cylinder equalities. -/
noncomputable def PublishedSoundness.ofDSeparationCrossProduct
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (crossProductSound : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductSoundness G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationDoRule G correct (by
    intro model compatible left right assignment application
      leftSupported rightSupported
    exact (crossProductSound model compatible).toDoRule assignment application
      leftSupported rightSupported)

/-- Published soundness assembled from three separately proved cross-product laws. -/
noncomputable def PublishedSoundness.ofDSeparationCrossProductLaws
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (laws : forall (model : ExactModel S), Compatible model G ->
      PathDoRuleCrossProductLaws G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationCrossProduct G correct
    (fun model compatible =>
      (laws model compatible).toCrossProductSoundness)

/-- Assemble published soundness from explicit graph-derived latent
partitions plus the complete d-separation correctness theorem. -/
noncomputable def PublishedSoundness.ofDSeparationPartitionWitnesses
    (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationCrossProductLaws G correct
    (fun model compatible =>
      (witnesses model compatible).toProductCrossProductLaws.toDistributionLaws)

/--
Published soundness from a path do-rule, using the inhabited d-separation
correctness theorem.  The remaining obligation is global-Markov soundness
of the three rules on compatible models.
-/
noncomputable def PublishedSoundness.ofDoRule
    (G : ObservedGraph S)
    (doRuleSound : ∀ (model : ExactModel S), Compatible model G ->
      ∀ {left right} (assignment : S.Assignment),
        PathDoRuleApplication G left right ->
          ProbabilityTerm.SupportedAt model (.kernel left) assignment ->
          ProbabilityTerm.SupportedAt model (.kernel right) assignment ->
          ProbabilityTerm.EquivalentAt model (.kernel left) (.kernel right)
            assignment) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationDoRule G G.dSeparationCorrectness doRuleSound

/--
Published soundness from graph-derived latent partitions, using the
inhabited d-separation correctness theorem.  The remaining obligation is
the three do-rule partition witnesses on compatible models.
-/
noncomputable def PublishedSoundness.ofPartitionWitnesses
    (G : ObservedGraph S)
    (witnesses : forall (model : ExactModel S), Compatible model G ->
      PathDoRulePartitionWitnesses G model) :
    PublishedSoundness S G :=
  PublishedSoundness.ofDSeparationPartitionWitnesses G
    G.dSeparationCorrectness witnesses

/-- A generic soundness package specializes constructively to finite source tables. -/
noncomputable def PublishedSoundness.toFiniteSource
    {T : FiniteTableSignature} {G : FiniteTableGraph T}
    (sound : PublishedSoundness T.toObserved G.interpret) :
    PublishedFiniteSourceSoundness T G where
  dseparation := sound.dseparation
  pathPrimitive := by
    intro model compatible
    apply PathPrimitiveSoundness.toFiniteSource
    exact sound.pathPrimitive model.interpret
      ((finiteSourceCompatible_iff model G).mp compatible)

/-- Finite-source package assembled from the three target mass laws. -/
noncomputable def PublishedFiniteSourceSoundness.ofDSeparationCrossProductLaws
    {T : FiniteTableSignature} (G : FiniteTableGraph T)
    (correct : DSeparationCorrectness G.interpret)
    (laws : forall (model : ExactModel T.toObserved),
      Compatible model G.interpret ->
        PathDoRuleCrossProductLaws G.interpret model) :
    PublishedFiniteSourceSoundness T G :=
  (PublishedSoundness.ofDSeparationCrossProductLaws
    G.interpret correct laws).toFiniteSource

end Causality
end Thesis
