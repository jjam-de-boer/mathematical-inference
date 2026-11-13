import Thesis.CausalTransport.HedgeChannelEnvironmentAbsorption
import Thesis.CausalTransport.HedgeChannelEnvironmentMaskPhase

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability PathSpecification HedgeChannelInstallation FiniteBooleanInteraction

/-!
# Fuse a real forest with an interaction at arbitrary overlaps

The absorbing-forest theorem assumes that the forest stops at the original
interaction.  Collider activation does the opposite: a collider already on
the path sends its bit along an outgoing activation trace.  The same legal
`absorbSuccessor` installation still combines its incoming masks correctly,
but its whole-phase formula must retain the overlap's own-bit correction.

For arbitrary well-formed forest data the union phase is the original
interaction phase XOR the whole forest phase XOR the observed bits of their
intersection.  At an overlap the installed row has one own bit, not two;
the correction belongs only to the proof-level accounting.  This allows
merging activation traces without duplicating shared rows or reserved inputs.

If every actual forest-domain coordinate is zero in a supplied direction,
the forest's incoming reads are zero.  Original row parities are then
preserved and new forest rows are even, whether or not a forest seed lies
in the interaction or has an outgoing successor there.  The graph-facing
application must prove those coordinate zeros from its actual direction.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

namespace LinearSignal

private theorem routingIncoming_zero_of_domain_zero (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (bits : Fin S.count -> Bool)
    (zero : forall parent, domain parent = true -> bits parent = false) (child : Fin S.count) :
    hedgeRoutingIncomingBits successor bits child = false := by
  unfold hedgeRoutingIncomingBits hedgeRoutingParentEntry
  apply foldl_unchanged
  intro total parent
  by_cases next : successor parent = some child
  · rw [if_pos next, zero parent (childWellFormed_edge domain successor wellFormed next).1, Bool.xor_false]
  · rw [if_neg next, Bool.xor_false]

/-- A forest row with no domain member in the supplied direction has no
nonzero incoming read.  Its own bit remains present even outside the domain. -/
theorem ofSuccessor_rowPhase_of_domain_zero (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (point : Cube G)
    (zero : forall parent, domain parent = true -> cubeSample G point parent = false) (child : Fin S.count) :
    ((ofSuccessor (G := G) successor).rowPhase child).value point = cubeSample G point child := by
  rw [ofSuccessor_rowPhase domain successor wellFormed]
  unfold hedgeRoutingLocalSource
  rw [routingIncoming_zero_of_domain_zero domain successor wellFormed _ zero, Bool.xor_false]

private theorem ofSuccessor_rowPhase_outside_domain (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (child : Fin S.count)
    (outside : domain child = false) (point : Cube G) :
    ((ofSuccessor (G := G) successor).rowPhase child).value point = cubeSample G point child := by
  rw [ofSuccessor_rowPhase domain successor wellFormed]
  unfold hedgeRoutingLocalSource
  have noIncoming : hedgeRoutingIncomingBits successor (cubeSample G point) child = false := by
    unfold hedgeRoutingIncomingBits hedgeRoutingParentEntry
    apply foldl_unchanged
    intro total parent
    by_cases next : successor parent = some child
    · have inside := (childWellFormed_edge domain successor wellFormed next).2.1
      exact False.elim (Bool.false_ne_true (outside.symm.trans inside))
    · rw [if_neg next, Bool.xor_false]
  rw [noIncoming, Bool.xor_false]

private theorem forestPhase_full_fold (data : LinearSignal G) (nodes : NodeSet S) (point : Cube G) :
    (data.forestPhase nodes).value point =
      (List.finRange S.count).foldl (fun total child => Bool.xor total
        (if nodes child then (data.rowPhase child).value point else false)) false := by
  rw [← selectedPhase_value_eq_forestPhase, selectedPhase_value_eq_foldl]

/-- General whole-union accounting for the actual fused installation.
The forest need not stop at interaction rows.  The explicit intersection
term corrects the own-bit duplication in the two separate proof-level
phase sums; the installed mechanism itself always keeps one own bit. -/
theorem absorbSuccessor_forestPhase_with_overlap (data : LinearSignal G)
    (interaction domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (point : Cube G) :
    ((data.absorbSuccessor interaction successor).forestPhase (NodeSet.union interaction domain)).value point =
      Bool.xor ((data.forestPhase interaction).value point)
        (Bool.xor (((ofSuccessor (G := G) successor).forestPhase domain).value point)
          (hedgeNodeXor (NodeSet.inter interaction domain) (cubeSample G point))) := by
  rw [forestPhase_full_fold, forestPhase_full_fold, forestPhase_full_fold, nodeXor_value_eq_full_fold]
  have entries : forall child,
      (if NodeSet.union interaction domain child then
        ((data.absorbSuccessor interaction successor).rowPhase child).value point else false) =
        Bool.xor (if interaction child then (data.rowPhase child).value point else false)
          (Bool.xor (if domain child then ((ofSuccessor (G := G) successor).rowPhase child).value point else false)
            (if NodeSet.inter interaction domain child then cubeSample G point child else false)) := by
    intro child
    cases core : interaction child with
    | false =>
        simp only [NodeSet.union, NodeSet.inter, core, Bool.false_or, Bool.false_and, Bool.false_eq_true,
          if_false, Bool.false_xor, Bool.xor_false]
        cases forest : domain child with
        | false => rfl
        | true =>
            change ((data.absorbSuccessor interaction successor).rowPhase child).value point = _
            exact data.absorbSuccessor_rowPhase_outside interaction successor child core point
    | true =>
        simp only [NodeSet.union, NodeSet.inter, core, Bool.true_or, Bool.true_and, if_true]
        cases forest : domain child with
        | false =>
            simp only [Bool.false_eq_true, if_false, Bool.xor_false]
            rw [data.absorbSuccessor_rowPhase_inside interaction successor child core,
              ofSuccessor_rowPhase_outside_domain domain successor wellFormed child forest,
              Bool.xor_self, Bool.xor_false]
        | true =>
            simp only [if_true]
            exact data.absorbSuccessor_rowPhase_inside interaction successor child core point
  calc
    _ = (List.finRange S.count).foldl (fun total child => Bool.xor total
        (Bool.xor (if interaction child then (data.rowPhase child).value point else false)
          (Bool.xor (if domain child then ((ofSuccessor (G := G) successor).rowPhase child).value point else false)
            (if NodeSet.inter interaction domain child then cubeSample G point child else false)))) false := by
      apply foldl_congr
      intro total child
      exact congrArg (Bool.xor total) (entries child)
    _ = _ := by rw [foldl_xor_pointwise, foldl_xor_pointwise]

/-- A zero-valued forest domain preserves each original interaction-row
phase in the actual fused signal, even when the forest transmits from that
row.  This does not need the absorber's stronger stopped-at-core premise. -/
theorem absorbSuccessor_rowPhase_inside_of_domain_zero (data : LinearSignal G)
    (interaction domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (point : Cube G)
    (zero : forall parent, domain parent = true -> cubeSample G point parent = false)
    (child : Fin S.count) (inside : interaction child = true) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value point = (data.rowPhase child).value point := by
  rw [data.absorbSuccessor_rowPhase_inside interaction successor child inside,
    ofSuccessor_rowPhase_of_domain_zero domain successor wellFormed point zero,
    Bool.xor_self, Bool.xor_false]

/-- A newly added forest row is even when all real forest coordinates are
zero.  A repeated activation occurrence has no separate own row here: the
domain is one Boolean selection under one common successor policy. -/
theorem absorbSuccessor_rowPhase_new_of_domain_zero (data : LinearSignal G)
    (interaction domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (point : Cube G)
    (zero : forall parent, domain parent = true -> cubeSample G point parent = false)
    (child : Fin S.count) (outside : interaction child = false) (inside : domain child = true) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value point = false := by
  rw [data.absorbSuccessor_rowPhase_outside interaction successor child outside,
    ofSuccessor_rowPhase_of_domain_zero domain successor wellFormed point zero, zero child inside]

/-- A row outside the actual fused union has only its own observed bit.
The well-formed forest has no incoming arrow into an unselected child,
and fusion retains no original core reads at an outside row.  This permits
retaining additional conditioned rows without inventing routes or latent reads. -/
theorem absorbSuccessor_rowPhase_outside_union (data : LinearSignal G)
    (interaction domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (child : Fin S.count)
    (outside : NodeSet.union interaction domain child = false) (point : Cube G) :
    ((data.absorbSuccessor interaction successor).rowPhase child).value point = cubeSample G point child := by
  have entries : interaction child = false ∧ domain child = false := Bool.or_eq_false_iff.mp outside
  rw [data.absorbSuccessor_rowPhase_outside interaction successor child entries.1,
    ofSuccessor_rowPhase_outside_domain domain successor wellFormed child entries.2]

end LinearSignal
end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
