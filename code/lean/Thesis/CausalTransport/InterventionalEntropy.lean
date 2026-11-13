import Thesis.CausalTransport.HiddenDAGSourceCompression
import Thesis.Causality.SelectedEntropy

namespace Thesis
namespace Causality

open Probability Probability.Distros

variable {S : ObservedSignature} {projection : FiniteLatentProjection S}

/-!
# Observational and interventional entropy of original hidden-DAG models

The existing evaluator already supplies the observational and interventional
assignment records as finite rational laws.  Entropy is then the Shannon
functional already proved on `Distro`.  Identification of an entire
interventional law therefore identifies its entropy; identification of one
event probability does not, except on a binary alphabet where the complement
is determined.

Hidden vertices remain in the original DAG.  Selected entropy below is
computed after the observed projection of an evaluation, never by pretending
that observed parents still factorise the hidden joint.
-/

namespace FiniteHiddenDAGSCM

/-- Push the native observational record into the entropy-facing law wrapper. -/
def observationalLaw (M : FiniteHiddenDAGSCM S projection) : Distro S.Assignment :=
  ⟨M.observationalDist⟩

/-- Push a native interventional record into the entropy-facing law wrapper. -/
def interventionalLaw (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) : Distro S.Assignment :=
  ⟨M.interventionalDist intervention⟩

def observationalEntropy (M : FiniteHiddenDAGSCM S projection) : ExactLog :=
  jointEntropy M.observationalLaw

def interventionalEntropy (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) : ExactLog :=
  jointEntropy (M.interventionalLaw intervention)

def selectedObservationalEntropy (M : FiniteHiddenDAGSCM S projection)
    (nodes : NodeSet S) : ExactLog :=
  selectedEntropy M.observationalLaw nodes

def selectedInterventionalEntropy (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (nodes : NodeSet S) : ExactLog :=
  selectedEntropy (M.interventionalLaw intervention) nodes

/-- Eventwise observational agreement is law agreement of the wrapped records. -/
theorem observationalLaw_sameLaw {left right : FiniteHiddenDAGSCM S projection}
    (agreement : ∀ event, QProb.Equiv (left.observationalValue event)
      (right.observationalValue event)) :
    left.observationalLaw.SameLaw right.observationalLaw :=
  agreement

theorem interventionalLaw_sameLaw {left right : FiniteHiddenDAGSCM S projection}
    (intervention : HardIntervention S)
    (agreement : ∀ event, QProb.Equiv (left.interventionalValue intervention event)
      (right.interventionalValue intervention event)) :
    (left.interventionalLaw intervention).SameLaw (right.interventionalLaw intervention) :=
  agreement

/-- The identification bridge: agreement of an entire observational law
identifies its entropy, jointly and on every selected coordinate set. -/
theorem observationalEntropy_of_agreement {left right : FiniteHiddenDAGSCM S projection}
    (agreement : ∀ event, QProb.Equiv (left.observationalValue event)
      (right.observationalValue event)) :
    ExactLog.Equiv left.observationalEntropy right.observationalEntropy :=
  jointEntropy_sameLaw (observationalLaw_sameLaw agreement)

theorem selectedObservationalEntropy_of_agreement
    {left right : FiniteHiddenDAGSCM S projection}
    (agreement : ∀ event, QProb.Equiv (left.observationalValue event)
      (right.observationalValue event))
    (nodes : NodeSet S) :
    ExactLog.Equiv (left.selectedObservationalEntropy nodes)
      (right.selectedObservationalEntropy nodes) :=
  selectedEntropy_sameLaw (observationalLaw_sameLaw agreement) nodes

/-- The same bridge for an interventional law.  The hypothesis is agreement
of every interventional event, i.e. identification of the whole pushed-forward
record, not of a single atom. -/
theorem interventionalEntropy_of_agreement {left right : FiniteHiddenDAGSCM S projection}
    (intervention : HardIntervention S)
    (agreement : ∀ event, QProb.Equiv (left.interventionalValue intervention event)
      (right.interventionalValue intervention event)) :
    ExactLog.Equiv (left.interventionalEntropy intervention)
      (right.interventionalEntropy intervention) :=
  jointEntropy_sameLaw (interventionalLaw_sameLaw intervention agreement)

theorem selectedInterventionalEntropy_of_agreement
    {left right : FiniteHiddenDAGSCM S projection}
    (intervention : HardIntervention S)
    (agreement : ∀ event, QProb.Equiv (left.interventionalValue intervention event)
      (right.interventionalValue intervention event))
    (nodes : NodeSet S) :
    ExactLog.Equiv (left.selectedInterventionalEntropy intervention nodes)
      (right.selectedInterventionalEntropy intervention nodes) :=
  selectedEntropy_sameLaw (interventionalLaw_sameLaw intervention agreement) nodes

/-- Probability-preserving source recoding preserves observational entropy,
because it preserves every observational event. -/
theorem observationalEntropy_of_record_eq {left right : FiniteHiddenDAGSCM S projection}
    (same : left.observationalDist = right.observationalDist) :
    ExactLog.Equiv left.observationalEntropy right.observationalEntropy :=
  observationalEntropy_of_agreement (by
    intro event
    change QProb.Equiv (left.observationalDist.probVal event)
      (right.observationalDist.probVal event)
    rw [same]
    exact QProb.equiv_refl _)

/-- Probability-preserving source recoding preserves observational entropy
exactly when it preserves every observational event. -/
theorem observationalEntropy_withSourceLaw (M : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw M.Noise)
    (preserved : ∀ event, QProb.Equiv
      ((M.withSourceLaw law).observationalValue event)
      (M.observationalValue event)) :
    ExactLog.Equiv (M.withSourceLaw law).observationalEntropy M.observationalEntropy :=
  observationalEntropy_of_agreement preserved

/-- The same transport for a hard intervention whose events are all retained. -/
theorem interventionalEntropy_withSourceLaw (M : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw M.Noise) (intervention : HardIntervention S)
    (preserved : ∀ event, QProb.Equiv
      ((M.withSourceLaw law).interventionalValue intervention event)
      (M.interventionalValue intervention event)) :
    ExactLog.Equiv ((M.withSourceLaw law).interventionalEntropy intervention)
      (M.interventionalEntropy intervention) :=
  interventionalEntropy_of_agreement intervention preserved

/-- Mechanism rewrite preserves observational entropy iff it preserves the
observational law.  Cutting an arrow can change the law; that change is the
Janzing disruption, not a recoding. -/
theorem observationalEntropy_withMechanism (M : FiniteHiddenDAGSCM S projection)
    (child : Fin projection.hiddenDAG.count)
    (newMechanism :
      projection.hiddenDAG.ParentValues M.NodeValue child →
        M.Noise child → M.NodeValue child)
    (preserved : ∀ event, QProb.Equiv
      ((M.withMechanism child newMechanism).observationalValue event)
      (M.observationalValue event)) :
    ExactLog.Equiv (M.withMechanism child newMechanism).observationalEntropy
      M.observationalEntropy :=
  observationalEntropy_of_agreement preserved

end FiniteHiddenDAGSCM

end Causality
end Thesis
