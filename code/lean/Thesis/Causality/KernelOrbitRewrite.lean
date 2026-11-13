import Thesis.Causality.KernelTableSCM
import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.Causality.Semantics

/-!
# Orbit rewrite of identified queries

A supplied partition of a child's alphabet, or kernel constancy on a supplied
parent orbit, licenses equating labels and dropping a conditioner that the
kernel does not distinguish. The rewrite calls the existing identification
engine; it does not infer partitions from data, does not put family names
into ID, and does not claim that a rewritten query is identified when the
original failed.
-/

namespace Thesis
namespace Causality

open Probability Probability.Distros
open ParentIndexedRecipe

/-- Drop the conditioner, producing `P(outcome | do(action))`. Licensed only
when a same-kernel or independence fact equates the two source terms. -/
def dropConditioner (q : ConditionalKernelQuery S) : JointKernelQuery S :=
  q.unconditionalJoint

theorem dropConditioner_sourceTerm (q : ConditionalKernelQuery S) :
    (dropConditioner q).sourceTerm =
      .kernel ⟨q.outcome, q.action, NodeSet.empty⟩ :=
  ConditionalKernelQuery.unconditionalJoint_sourceTerm q

/-- Existing joint engine on the dropped-conditioner query. Not a new ID
algorithm. -/
def identifyDroppedConditioner (G : ObservedGraph S) (q : ConditionalKernelQuery S) :
    IdentificationOutcome S :=
  identifyJointKernel G (dropConditioner q)

/-- Both engines, or `none`. Failure of the original is not rewritten into
an identified pair. -/
def identifiedAfterDrop? (G : ObservedGraph S) (q : ConditionalKernelQuery S) :
    Option (ProbabilityTerm S × ProbabilityTerm S) :=
  match identifyConditionalKernel G q with
  | .identified original =>
      match identifyDroppedConditioner G q with
      | .identified rewritten => some (original, rewritten)
      | .failed _ => none
      | .unfinished => none
  | .failed _ => none
  | .unfinished => none

theorem identifiedAfterDrop?_none_of_original_failed {S : ObservedSignature}
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    {fail : IdentificationFail S}
    (h : identifyConditionalKernel G q = .failed fail) :
    identifiedAfterDrop? G q = none := by
  simp [identifiedAfterDrop?, h]

theorem identifiedAfterDrop?_none_of_original_unfinished {S : ObservedSignature}
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    (h : identifyConditionalKernel G q = .unfinished) :
    identifiedAfterDrop? G q = none := by
  simp [identifiedAfterDrop?, h]

theorem identifiedAfterDrop?_eq_some {S : ObservedSignature}
    {G : ObservedGraph S} {q : ConditionalKernelQuery S}
    {original rewritten : ProbabilityTerm S}
    (h : identifiedAfterDrop? G q = some (original, rewritten)) :
    identifyConditionalKernel G q = .identified original ∧
      identifyDroppedConditioner G q = .identified rewritten := by
  revert h
  simp only [identifiedAfterDrop?]
  cases hOrig : identifyConditionalKernel G q with
  | identified t1 =>
      cases hRew : identifyDroppedConditioner G q with
      | identified t2 =>
          intro h
          cases h
          exact ⟨rfl, rfl⟩
      | failed _ => intro h; cases h
      | unfinished => intro h; cases h
  | failed _ => intro h; cases h
  | unfinished => intro h; cases h

/-- If both engines succeed, identified values agree exactly when the
original and rewritten source terms already agree on this model. Soundness
certificates are hypotheses; the pair is `none` when the original failed. -/
def dropConditioner_identified_equiv {S : ObservedSignature}
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    (model : FiniteLatentSCM S) (reference : S.Assignment)
    {original rewritten : ProbabilityTerm S}
    (_hpair : identifiedAfterDrop? G q = some (original, rewritten))
    (license :
      ProbabilityTerm.EquivalentAt model q.sourceTerm
        (dropConditioner q).sourceTerm reference)
    (soundOriginal :
      ProbabilityTerm.EquivalentAt model q.sourceTerm original reference)
    (soundRewritten :
      ProbabilityTerm.EquivalentAt model (dropConditioner q).sourceTerm
        rewritten reference) :
    ProbabilityTerm.EquivalentAt model original rewritten reference :=
  ProbabilityResult.trans (ProbabilityResult.symm soundOriginal)
    (ProbabilityResult.trans license soundRewritten)

/-- Two joint queries that differ only by orbit-equivalent outcome labels
are compared the same way: identification is reused, not reimplemented. -/
def identified_values_equiv {S : ObservedSignature}
    (G : ObservedGraph S) (first second : JointKernelQuery S)
    (model : FiniteLatentSCM S) (reference : S.Assignment)
    {tFirst tSecond : ProbabilityTerm S}
    (_hFirst : identifyJointKernel G first = .identified tFirst)
    (_hSecond : identifyJointKernel G second = .identified tSecond)
    (license :
      ProbabilityTerm.EquivalentAt model first.sourceTerm second.sourceTerm
        reference)
    (soundFirst :
      ProbabilityTerm.EquivalentAt model first.sourceTerm tFirst reference)
    (soundSecond :
      ProbabilityTerm.EquivalentAt model second.sourceTerm tSecond reference) :
    ProbabilityTerm.EquivalentAt model tFirst tSecond reference :=
  ProbabilityResult.trans (ProbabilityResult.symm soundFirst)
    (ProbabilityResult.trans license soundSecond)

/-- Identified supported values agree by `QProb.Equiv`. Undefined stays
undefined; this does not complete a missing denominator to zero. -/
def qprobEquivOfSupported {p r : QProb} {left right : ProbabilityResult.Result}
    (agree : ProbabilityResult.Equivalent left right)
    (hl : ProbabilityResult.Equivalent left (some p))
    (hr : ProbabilityResult.Equivalent right (some r)) :
    QProb.Equiv p r := by
  cases hl with
  | value hp =>
      cases hr with
      | value hq =>
          cases agree with
          | value heq =>
              exact QProb.equiv_trans (QProb.equiv_symm hp)
                (QProb.equiv_trans heq hq)

def dropConditioner_identified_qprob {S : ObservedSignature}
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    (model : FiniteLatentSCM S) (reference : S.Assignment)
    {original rewritten : ProbabilityTerm S} {p r : QProb}
    (hpair : identifiedAfterDrop? G q = some (original, rewritten))
    (license :
      ProbabilityTerm.EquivalentAt model q.sourceTerm
        (dropConditioner q).sourceTerm reference)
    (soundOriginal :
      ProbabilityTerm.EquivalentAt model q.sourceTerm original reference)
    (soundRewritten :
      ProbabilityTerm.EquivalentAt model (dropConditioner q).sourceTerm
        rewritten reference)
    (hp :
      ProbabilityResult.Equivalent (original.denote model reference) (some p))
    (hr :
      ProbabilityResult.Equivalent (rewritten.denote model reference) (some r)) :
    QProb.Equiv p r :=
  qprobEquivOfSupported
    (dropConditioner_identified_equiv G q model reference hpair license
      soundOriginal soundRewritten)
    hp hr

/-- Parent-orbit constancy of compiled rows: the kernel ignores labels in the
same supplied class. Occupancy rank is not a rewrite rule. -/
def kernelConstantOn {Parent Child : Type u} [DecidableEq Child]
    {spec : ParentIndexedRecipe Parent Child} (kernel : KernelTable spec)
    (label : Parent → Nat) : Prop :=
  ∀ p1, ∀ hp1 : p1 ∈ spec.parents, ∀ p2, ∀ hp2 : p2 ∈ spec.parents,
    label p1 = label p2 →
      ∀ event : Event Child,
        QProb.Equiv ((kernel.row p1 hp1).probVal event)
          ((kernel.row p2 hp2).probVal event)

theorem kernelConstantOn_prob {Parent Child : Type u} [DecidableEq Child]
    {spec : ParentIndexedRecipe Parent Child} (kernel : KernelTable spec)
    (label : Parent → Nat) (hconst : kernelConstantOn kernel label)
    (p1 : Parent) (hp1 : p1 ∈ spec.parents)
    (p2 : Parent) (hp2 : p2 ∈ spec.parents)
    (same : label p1 = label p2) (child : Child) :
    QProb.Equiv (kernel.prob p1 hp1 child) (kernel.prob p2 hp2 child) :=
  hconst p1 hp1 p2 hp2 same (FiniteProbRecord.singletonEvent child)

/-- A conditioner orbit the compiled kernel does not distinguish yields the
same installed child law. Occupancy rank is not used. -/
theorem mechanism_kernelConstantOn {S : ObservedSignature}
    (kernels : (child : Fin S.count) → InstalledChildKernel S child)
    (child : Fin S.count) (label : S.ParentValues child → Nat)
    (hconst : kernelConstantOn (kernels child).kernel label)
    (p1 p2 : S.ParentValues child) (same : label p1 = label p2)
    (event : S.Value child → Bool) :
    QProb.Equiv
      (((ofInstalled kernels).factor child).probVal
        (fun seed =>
          event ((ofInstalled kernels).mechanism child p1 seed)))
      (((ofInstalled kernels).factor child).probVal
        (fun seed =>
          event ((ofInstalled kernels).mechanism child p2 seed))) :=
  QProb.equiv_trans
    (mechanism_realizes_row kernels child p1 event)
    (QProb.equiv_trans
      (hconst p1 ((kernels child).cover p1) p2 ((kernels child).cover p2)
        same event)
      (QProb.equiv_symm (mechanism_realizes_row kernels child p2 event)))

end Causality
end Thesis
