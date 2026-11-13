import Thesis.Causality.Structural
import Thesis.Causality.Multiworld

namespace Thesis
namespace Causality

open Probability

/-!
Creation primitives for executable occurrence-indexed multiworld models.

The opening definitions select a fresh factual record and provide the
dependent coordinate-transport lemmas used throughout the construction. The
subsequent sections append isolated terminal nodes, assemble occurrence-world
copies, and retain genuine edit paths to every resulting epistemic endpoint.
The direct occurrence model remains an independent semantic reference.
-/

/--
The factual starting mode used by occurrence-world execution: it keeps the
source structural model, uses its product prior as belief, and has no active
compact intervention.
-/
def counterfactualBaseMode (mode : CausalMode S) : CausalMode S :=
  ⟨"counterfactual-factual", CausalEpistemicRecord.initial mode.record.model⟩

theorem counterfactualBaseMode_noActiveIntervention (mode : CausalMode S) :
    AtomicIntervention.NoActiveIntervention (counterfactualBaseMode mode) := by
  intro child
  rfl

namespace AtomicIntervention.SameRoots

theorem transportAssignment_toFun
    {S T : ObservedSignature} {source : CausalMode S}
    {targetMode : CausalMode T}
    (roots : AtomicIntervention.SameRoots source targetMode)
    (assignment : source.record.model.latent.Assignment)
    (root : Fin source.record.model.latent.count) :
    cast (roots.value_eq root).symm
        (roots.transportAssignment assignment (roots.rootEquiv.toFun root)) =
      assignment root := by
  unfold transportAssignment
  apply eq_of_heq
  exact HEq.trans (cast_heq _ _)
    (HEq.trans (cast_heq _ _)
      (dependentApplyHEq assignment (roots.rootEquiv.left_inv root)))

end AtomicIntervention.SameRoots

namespace AtomicIntervention.SameCoordinates

theorem transportObserved_untransportObserved
    (coordinates : AtomicIntervention.SameCoordinates S T)
    (assignment : T.Assignment) :
    coordinates.transportObserved
        (coordinates.untransportObserved assignment) = assignment := by
  funext node
  unfold transportObserved untransportObserved
  apply eq_of_heq
  exact HEq.trans (cast_heq _ _)
    (HEq.trans (cast_heq _ _)
      (by
        rw [coordinates.nodeEquiv.right_inv]))

end AtomicIntervention.SameCoordinates

/-! ## Repeated terminal creation -/

/-- Finite data needed to create isolated terminal nodes of a fixed family. -/
structure IsolatedNodeFamily (α : Type) where
  Value : α -> Type
  valueEnumeration : (item : α) -> List (Value item)
  value_complete : forall item value, value ∈ valueEnumeration item
  value_nodup : forall item, (valueEnumeration item).Nodup
  defaultValue : (item : α) -> Value item
  valueDecidableEq : (item : α) -> DecidableEq (Value item)

namespace IsolatedNodeFamily

def spec (family : IsolatedNodeFamily α) (item : α)
    {S : ObservedSignature} (record : CausalEpistemicRecord S) :
    EndogenousVariableSpec record where
  Value := family.Value item
  valueEnumeration := family.valueEnumeration item
  value_complete := family.value_complete item
  value_nodup := family.value_nodup item
  defaultValue := family.defaultValue item
  valueDecidableEq := family.valueDecidableEq item
  parents := (NodeSet.empty : NodeSet S)
  latentInputs := fun _ => false
  mechanism := fun _ _ => family.defaultValue item

end IsolatedNodeFamily

/--
The result of appending one isolated terminal node for every list occurrence.
It records both the genuine causal-edit path and the coordinates of old and new
nodes in the resulting dependent signature.
-/
structure TerminalListConstruction
    {α : Type} (family : IsolatedNodeFamily α)
    {S : ObservedSignature} (source : CausalMode S)
    (items : List α) where
  signature : ObservedSignature
  target : CausalMode signature
  path : CausalEditPath source target
  roots : AtomicIntervention.SameRoots source target
  count_eq : signature.count = S.count + items.length
  oldNode : Fin S.count -> Fin signature.count
  oldNode_val : forall node, (oldNode node).val = node.val
  oldValue_eq : forall node,
    signature.Value (oldNode node) = S.Value node
  oldDirected : forall parent child,
    S.directed parent child = true ->
      signature.directed (oldNode parent) (oldNode child) = true
  directedReflects : forall parent child,
    signature.directed parent child = true ->
      Exists fun sourceParent : Fin S.count =>
        Exists fun sourceChild : Fin S.count =>
          parent = oldNode sourceParent ∧ child = oldNode sourceChild ∧
            S.directed sourceParent sourceChild = true
  oldIncident : forall sourceRoot child,
    source.record.model.latent.incident sourceRoot child = true ->
      target.record.model.latent.incident
        (roots.rootEquiv.toFun sourceRoot) (oldNode child) = true
  incidentReflects : forall sourceRoot child,
    target.record.model.latent.incident
        (roots.rootEquiv.toFun sourceRoot) child = true ->
      Exists fun sourceChild : Fin S.count =>
        child = oldNode sourceChild ∧
          source.record.model.latent.incident sourceRoot sourceChild = true
  itemNode : Fin items.length -> Fin signature.count
  itemNode_val : forall index,
    (itemNode index).val = S.count + index.val
  itemValue_eq : forall index,
    signature.Value (itemNode index) = family.Value (items.get index)

namespace TerminalListConstruction

def build {α : Type} (family : IsolatedNodeFamily α)
    {S : ObservedSignature} (source : CausalMode S) :
    (items : List α) -> TerminalListConstruction family source items
  | [] =>
      { signature := S
        target := source
        path := .nil source
        roots := AtomicIntervention.SameRoots.refl source
        count_eq := by simp
        oldNode := fun node => node
        oldNode_val := fun _ => rfl
        oldValue_eq := fun _ => rfl
        oldDirected := fun _ _ edge => edge
        directedReflects := fun parent child edge =>
          ⟨parent, child, rfl, rfl, edge⟩
        oldIncident := fun _ _ incident => incident
        incidentReflects := fun _ child incident =>
          ⟨child, rfl, incident⟩
        itemNode := fun index => Fin.elim0 index
        itemNode_val := fun index => Fin.elim0 index
        itemValue_eq := fun index => Fin.elim0 index }
  | item :: rest =>
      let spec := family.spec item source.record
      let transition := spec.learnTransition source "create-endogenous"
      let tail := build family transition.target rest
      let stepRoots : AtomicIntervention.SameRoots source transition.target :=
        { rootEquiv :=
            AtomicIntervention.FinIndexEquiv.refl
              source.record.model.latent.count
          value_eq := fun _ => rfl }
      { signature := tail.signature
        target := tail.target
        path := (CausalEditPath.single transition).append tail.path
        roots := stepRoots.trans tail.roots
        count_eq := by
          rw [tail.count_eq]
          simp [spec, EndogenousVariableSpec.extendSignature,
            TerminalVariableSpec.extendSignature]
          omega
        oldNode := fun node => tail.oldNode (spec.oldNode node)
        oldNode_val := fun node => by
          rw [tail.oldNode_val]
          rfl
        oldValue_eq := fun node =>
          Eq.trans (tail.oldValue_eq (spec.oldNode node))
            (spec.terminalSpec.value_oldNode node)
        oldDirected := fun parent child edge => by
          exact tail.oldDirected (spec.oldNode parent) (spec.oldNode child)
            (by
              change spec.extendSignature.directed
                (spec.oldNode parent) (spec.oldNode child) = true
              simpa [EndogenousVariableSpec.extendSignature,
                EndogenousVariableSpec.oldNode] using edge)
        directedReflects := fun parent child edge => by
          rcases tail.directedReflects parent child edge with
            ⟨stepParent, stepChild, parentEq, childEq, stepEdge⟩
          change spec.terminalSpec.extendedDirected stepParent stepChild = true
            at stepEdge
          have reflected :
              Exists fun sourceParent : Fin S.count =>
                Exists fun sourceChild : Fin S.count =>
                  stepParent = sourceParent.castSucc ∧
                    stepChild = sourceChild.castSucc ∧
                      S.directed sourceParent sourceChild = true := by
            refine TerminalVariableSpec.terminalCases
              (motive := fun candidateChild =>
                spec.terminalSpec.extendedDirected stepParent
                    candidateChild = true ->
                  Exists fun sourceParent : Fin S.count =>
                    Exists fun sourceChild : Fin S.count =>
                      stepParent = sourceParent.castSucc ∧
                        candidateChild = sourceChild.castSucc ∧
                          S.directed sourceParent sourceChild = true)
              ?_ (fun sourceChild sourceEdge => ?_) stepChild stepEdge
            · refine TerminalVariableSpec.terminalCases
                (motive := fun candidateParent =>
                  spec.terminalSpec.extendedDirected candidateParent
                      (Fin.last S.count) = true ->
                    Exists fun sourceParent : Fin S.count =>
                      Exists fun sourceChild : Fin S.count =>
                        candidateParent = sourceParent.castSucc ∧
                          Fin.last S.count = sourceChild.castSucc ∧
                            S.directed sourceParent sourceChild = true)
                ?_ (fun sourceParent impossible => ?_) stepParent
              · simp [TerminalVariableSpec.extendedDirected]
              · simp [TerminalVariableSpec.extendedDirected, spec,
                  EndogenousVariableSpec.terminalSpec,
                  IsolatedNodeFamily.spec, NodeSet.empty] at impossible
            · refine TerminalVariableSpec.terminalCases
                (motive := fun candidateParent =>
                  spec.terminalSpec.extendedDirected candidateParent
                      sourceChild.castSucc = true ->
                    Exists fun sourceParent : Fin S.count =>
                      Exists fun oldChild : Fin S.count =>
                        candidateParent = sourceParent.castSucc ∧
                          sourceChild.castSucc = oldChild.castSucc ∧
                            S.directed sourceParent oldChild = true)
                ?_ (fun sourceParent oldEdge => ?_) stepParent sourceEdge
              · simp [TerminalVariableSpec.extendedDirected]
              · exact ⟨sourceParent, sourceChild, rfl, rfl,
                  by simpa [TerminalVariableSpec.extendedDirected] using oldEdge⟩
          rcases reflected with
            ⟨sourceParent, sourceChild, stepParentEq, stepChildEq, sourceEdge⟩
          exact ⟨sourceParent, sourceChild,
            parentEq.trans (congrArg tail.oldNode stepParentEq),
            childEq.trans (congrArg tail.oldNode stepChildEq), sourceEdge⟩
        oldIncident := fun sourceRoot child incident => by
          have firstIncident :
              transition.target.record.model.latent.incident sourceRoot
                (spec.oldNode child) = true := by
            change spec.extendLatent.incident sourceRoot
              (spec.oldNode child) = true
            simpa using incident
          simpa [stepRoots, AtomicIntervention.SameRoots.trans,
            AtomicIntervention.FinIndexEquiv.trans] using
            tail.oldIncident sourceRoot (spec.oldNode child) firstIncident
        incidentReflects := fun sourceRoot child incident => by
          have tailIncident :
              tail.target.record.model.latent.incident
                  (tail.roots.rootEquiv.toFun sourceRoot) child = true := by
            simpa [stepRoots, AtomicIntervention.SameRoots.trans,
              AtomicIntervention.FinIndexEquiv.trans] using incident
          rcases tail.incidentReflects sourceRoot child tailIncident with
            ⟨stepChild, childEq, stepIncident⟩
          change (spec.terminalSpec.extendLatent
            source.record.model.latent).incident sourceRoot stepChild = true
              at stepIncident
          rcases spec.terminalSpec.extendLatent_incident_true_is_old
              source.record.model.latent sourceRoot stepChild stepIncident with
            ⟨sourceChild, stepChildEq, sourceIncident⟩
          exact ⟨sourceChild,
            childEq.trans (congrArg tail.oldNode stepChildEq), sourceIncident⟩
        itemNode := fun index =>
          Fin.cases (tail.oldNode spec.newNode)
            (fun restIndex => tail.itemNode restIndex) index
        itemNode_val := fun index => by
          refine Fin.cases ?_ (fun restIndex => ?_) index
          · simp only [Fin.cases_zero]
            rw [tail.oldNode_val]
            rfl
          · simp only [Fin.cases_succ]
            rw [tail.itemNode_val]
            simp [spec, EndogenousVariableSpec.extendSignature,
              TerminalVariableSpec.extendSignature]
            omega
        itemValue_eq := fun index => by
          refine Fin.cases ?_ (fun restIndex => ?_) index
          · exact Eq.trans (tail.oldValue_eq spec.newNode)
              spec.terminalSpec.value_newNode
          · exact tail.itemValue_eq restIndex }

/--
The canonical terminal-node builder preserves absence of a compact
intervention at every recursive learning step.
-/
theorem build_noActiveIntervention {α : Type}
    (family : IsolatedNodeFamily α)
    {S : ObservedSignature} (source : CausalMode S)
    (empty : AtomicIntervention.NoActiveIntervention source) :
    (items : List α) ->
      AtomicIntervention.NoActiveIntervention
        (build family source items).target
  | [] => by
      simpa [build] using empty
  | item :: rest => by
      let spec := family.spec item source.record
      let transition := spec.learnTransition source "create-endogenous"
      have stepEmpty :
          AtomicIntervention.NoActiveIntervention transition.target :=
        AtomicIntervention.endogenousLearning_noActiveIntervention
          source spec "create-endogenous" empty
      simpa [build, spec, transition] using
        build_noActiveIntervention family transition.target stepEmpty rest

end TerminalListConstruction

/-! ## Isolated copies of an observed world -/

def ObservedSignature.isolatedNodeFamily (S : ObservedSignature) :
    IsolatedNodeFamily (Fin S.count) where
  Value := S.Value
  valueEnumeration := S.valueEnumeration
  value_complete := S.value_complete
  value_nodup := S.value_nodup
  defaultValue := S.defaultValue
  valueDecidableEq := S.valueDecidableEq

def finRangePosition {count : Nat} (node : Fin count) :
    Fin (List.finRange count).length :=
  ⟨node.val, by
    rw [List.length_finRange]
    exact node.isLt⟩

@[simp] theorem finRange_get_position {count : Nat} (node : Fin count) :
    (List.finRange count).get (finRangePosition node) = node := by
  simp [finRangePosition]

/-- One genuinely appended, initially isolated copy of an observed signature. -/
structure IsolatedWorldConstruction (template : ObservedSignature)
    {S : ObservedSignature} (source : CausalMode S) where
  construction : TerminalListConstruction template.isolatedNodeFamily source
    (List.finRange template.count)

namespace IsolatedWorldConstruction

def build (template : ObservedSignature) (source : CausalMode S) :
    IsolatedWorldConstruction template source where
  construction := TerminalListConstruction.build
    template.isolatedNodeFamily source (List.finRange template.count)

theorem build_noActiveIntervention
    (template : ObservedSignature) (source : CausalMode S)
    (empty : AtomicIntervention.NoActiveIntervention source) :
    AtomicIntervention.NoActiveIntervention
      (build template source).construction.target :=
  TerminalListConstruction.build_noActiveIntervention
    template.isolatedNodeFamily source empty (List.finRange template.count)

abbrev signature {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source) :
    ObservedSignature :=
  built.construction.signature

abbrev target {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source) :
    CausalMode built.signature :=
  built.construction.target

abbrev path {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source) :
    CausalEditPath source built.target :=
  built.construction.path

theorem count_eq {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source) :
    built.signature.count = S.count + template.count := by
  simpa using built.construction.count_eq

def oldNode {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (node : Fin S.count) : Fin built.signature.count :=
  built.construction.oldNode node

def copiedNode {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (node : Fin template.count) : Fin built.signature.count :=
  built.construction.itemNode (finRangePosition node)

theorem oldNode_val {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (node : Fin S.count) :
    (built.oldNode node).val = node.val :=
  built.construction.oldNode_val node

theorem copiedNode_val {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (node : Fin template.count) :
    (built.copiedNode node).val = S.count + node.val := by
  exact built.construction.itemNode_val (finRangePosition node)

theorem oldValue_eq {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (node : Fin S.count) :
    built.signature.Value (built.oldNode node) = S.Value node :=
  built.construction.oldValue_eq node

theorem oldDirected {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (parent child : Fin S.count) (edge : S.directed parent child = true) :
    built.signature.directed (built.oldNode parent) (built.oldNode child) =
      true :=
  built.construction.oldDirected parent child edge

theorem oldIncident {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (sourceRoot : Fin source.record.model.latent.count)
    (child : Fin S.count)
    (incident : source.record.model.latent.incident sourceRoot child = true) :
    built.target.record.model.latent.incident
        (built.construction.roots.rootEquiv.toFun sourceRoot)
        (built.oldNode child) = true :=
  built.construction.oldIncident sourceRoot child incident

theorem copiedValue_eq {S : ObservedSignature} {source : CausalMode S}
    (built : IsolatedWorldConstruction template source)
    (node : Fin template.count) :
    built.signature.Value (built.copiedNode node) = template.Value node := by
  exact Eq.trans
    (built.construction.itemValue_eq (finRangePosition node))
    (congrArg template.Value (finRange_get_position node))

end IsolatedWorldConstruction

/--
Append one isolated observed copy for every atom occurrence.  Equal actions
remain different occurrences because the recursion follows the atom list rather
than quotienting it.
-/
structure OccurrenceCopiesConstruction (template : ObservedSignature)
    {S : ObservedSignature} (source : CausalMode S)
    (atoms : List (CounterfactualAtom template)) where
  signature : ObservedSignature
  target : CausalMode signature
  path : CausalEditPath source target
  roots : AtomicIntervention.SameRoots source target
  count_eq : signature.count = S.count + atoms.length * template.count
  oldNode : Fin S.count -> Fin signature.count
  oldNode_val : forall node, (oldNode node).val = node.val
  oldValue_eq : forall node,
    signature.Value (oldNode node) = S.Value node
  oldDirected : forall parent child,
    S.directed parent child = true ->
      signature.directed (oldNode parent) (oldNode child) = true
  oldIncident : forall sourceRoot child,
    source.record.model.latent.incident sourceRoot child = true ->
      target.record.model.latent.incident
        (roots.rootEquiv.toFun sourceRoot) (oldNode child) = true
  copiedNode : Fin atoms.length -> Fin template.count -> Fin signature.count
  copiedNode_val : forall occurrence node,
    (copiedNode occurrence node).val =
      S.count + occurrence.val * template.count + node.val
  copiedValue_eq : forall occurrence node,
    signature.Value (copiedNode occurrence node) = template.Value node

namespace OccurrenceCopiesConstruction

def build (template : ObservedSignature) (source : CausalMode S) :
    (atoms : List (CounterfactualAtom template)) ->
      OccurrenceCopiesConstruction template source atoms
  | [] =>
      { signature := S
        target := source
        path := .nil source
        roots := AtomicIntervention.SameRoots.refl source
        count_eq := by simp
        oldNode := fun node => node
        oldNode_val := fun _ => rfl
        oldValue_eq := fun _ => rfl
        oldDirected := fun _ _ edge => edge
        oldIncident := fun _ _ incident => incident
        copiedNode := fun occurrence => Fin.elim0 occurrence
        copiedNode_val := fun occurrence => Fin.elim0 occurrence
        copiedValue_eq := fun occurrence => Fin.elim0 occurrence }
  | _atom :: rest =>
      let head := IsolatedWorldConstruction.build template source
      let tail := build template head.target rest
      { signature := tail.signature
        target := tail.target
        path := head.path.append tail.path
        roots := head.construction.roots.trans tail.roots
        count_eq := by
          rw [tail.count_eq, head.count_eq]
          simp [Nat.add_mul]
          omega
        oldNode := fun node => tail.oldNode (head.oldNode node)
        oldNode_val := fun node => by
          rw [tail.oldNode_val, head.oldNode_val]
        oldValue_eq := fun node =>
          Eq.trans (tail.oldValue_eq (head.oldNode node))
            (head.oldValue_eq node)
        oldDirected := fun parent child edge =>
          tail.oldDirected (head.oldNode parent) (head.oldNode child)
            (head.oldDirected parent child edge)
        oldIncident := fun sourceRoot child incident => by
          simpa [AtomicIntervention.SameRoots.trans,
            AtomicIntervention.FinIndexEquiv.trans] using
            tail.oldIncident
              (head.construction.roots.rootEquiv.toFun sourceRoot)
              (head.oldNode child)
              (head.oldIncident sourceRoot child incident)
        copiedNode := fun occurrence node =>
          Fin.cases
            (tail.oldNode (head.copiedNode node))
            (fun restOccurrence => tail.copiedNode restOccurrence node)
            occurrence
        copiedNode_val := fun occurrence node => by
          refine Fin.cases ?_ (fun restOccurrence => ?_) occurrence
          · simp only [Fin.cases_zero]
            rw [tail.oldNode_val, head.copiedNode_val]
            simp
          · simp only [Fin.cases_succ]
            rw [tail.copiedNode_val, head.count_eq]
            simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        copiedValue_eq := fun occurrence node => by
          refine Fin.cases ?_ (fun restOccurrence => ?_) occurrence
          · exact Eq.trans
              (tail.oldValue_eq (head.copiedNode node))
              (head.copiedValue_eq node)
          · exact tail.copiedValue_eq restOccurrence node }

/-- Every canonical occurrence-copy creation preserves intervention emptiness. -/
theorem build_noActiveIntervention
    (template : ObservedSignature) (source : CausalMode S)
    (empty : AtomicIntervention.NoActiveIntervention source) :
    (atoms : List (CounterfactualAtom template)) ->
      AtomicIntervention.NoActiveIntervention
        (build template source atoms).target
  | [] => by
      simpa [build] using empty
  | _atom :: rest => by
      let head := IsolatedWorldConstruction.build template source
      have headEmpty : AtomicIntervention.NoActiveIntervention head.target :=
        IsolatedWorldConstruction.build_noActiveIntervention template source empty
      simpa [build, head] using
        build_noActiveIntervention template head.target headEmpty rest

end OccurrenceCopiesConstruction

end Causality
end Thesis
