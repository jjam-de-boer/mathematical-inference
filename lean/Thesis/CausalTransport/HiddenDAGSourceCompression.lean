import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.FiniteProductSourceCompression

namespace Thesis
namespace Causality

open Probability

/-!
# Bounded independent sources on the unchanged native hidden DAG

A query specifies an actual observed event and hard intervention; the empty
intervention includes observational probabilities.  For any finite family of
these queries, every native private-noise source can be compressed to at most
`count + 1` positive atom occurrences while all requested values are retained.

The construction changes only noise probability records and their joint
prior.  It keeps the original hidden DAG, all node/noise value types, observed
embeddings and structural mechanisms.  A separate evaluator theorem proves
that every supplied noise assignment gives exactly the same structural
readout after changing the source law.  Thus event preservation is about the
actual new native model, not an assumed correspondence with another model.

No positivity of observed cells or selected interventions is needed.  These
are unconditional event probabilities under hard interventions.  A desired
conditional value can be preserved by including both its joint event and
conditioner probabilities and retaining the required positive denominator;
undefined conditionals are not assigned arbitrary values by this theorem.

The bounds concern positive occurrences in each source's finite record, not
the cardinality of the unchanged ambient noise type or of hidden endogenous
node alphabets.  Complete general optimization is not a consequence here.
-/

structure NativeProbabilityQuery (S : ObservedSignature) where
  intervention : HardIntervention S
  event : Event S.Assignment

namespace FiniteHiddenDAGSCM

variable {count : Nat}

def sourceLaw (model : FiniteHiddenDAGSCM S projection) : FiniteProduct.IndependentLaw model.Noise :=
  ⟨model.factor, model.prior, model.product_law⟩

/-- Retain every structural field verbatim.  The supplied replacement law
has the very same dependent noise types and its own proved product law. -/
def withSourceLaw (model : FiniteHiddenDAGSCM S projection) (law : FiniteProduct.IndependentLaw model.Noise) :
    FiniteHiddenDAGSCM S projection :=
  { model with factor := law.factor, prior := law.prior, product_law := law.product_law }

theorem withSourceLaw_evalNode (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (intervention : HardIntervention S)
    (noise : model.NoiseAssignment) (node : Fin projection.hiddenDAG.count) :
    (model.withSourceLaw law).evalNode intervention noise node = model.evalNode intervention noise node := by
  apply (model.withSourceLaw law).evalNode_eq_of_solution intervention noise (model.evalFull intervention noise)
  intro current
  change model.evalNode intervention noise current =
    match model.interventionValueAt intervention current with
    | some value => value
    | none => model.mechanism current (fun parent _edge => model.evalNode intervention noise parent) (noise current)
  rw [evalNode]

theorem withSourceLaw_evalObserved (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (intervention : HardIntervention S) (noise : model.NoiseAssignment) :
    (model.withSourceLaw law).evalObserved intervention noise = model.evalObserved intervention noise := by
  funext index
  change (model.observedEquiv index).forward
      ((model.withSourceLaw law).evalNode intervention noise (projection.hiddenDAG.observedNode index)) = _
  rw [withSourceLaw_evalNode]

theorem withSourceLaw_interventionalValue (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (query : NativeProbabilityQuery S) :
    QProb.Equiv ((model.withSourceLaw law).interventionalValue query.intervention query.event)
      (law.prior.probVal (fun noise => query.event (model.evalObserved query.intervention noise))) := by
  exact QProb.equiv_trans
    (law.prior.map_probVal ((model.withSourceLaw law).evalObserved query.intervention) query.event)
    (law.prior.probVal_congr _ _ (fun noise => congrArg query.event (withSourceLaw_evalObserved model law query.intervention noise)))

structure SourceCompression (original : FiniteHiddenDAGSCM S projection) (queries : Fin count → NativeProbabilityQuery S) where
  law : FiniteProduct.IndependentLaw original.Noise
  bounded : forall node, (law.factor node).atoms.length ≤ count + 1
  positive : forall node atom, atom ∈ (law.factor node).atoms → 0 < atom.2
  preserved : forall index, QProb.Equiv
    ((original.withSourceLaw law).interventionalValue (queries index).intervention (queries index).event)
    (original.interventionalValue (queries index).intervention (queries index).event)

def SourceCompression.model {original : FiniteHiddenDAGSCM S projection} {queries : Fin count → NativeProbabilityQuery S}
    (compressed : SourceCompression original queries) : FiniteHiddenDAGSCM S projection :=
  original.withSourceLaw compressed.law

/-- Compress all private sources successively, using the unchanged native
readout as the finite family of noise events.  Every intermediate independent
law and support bound is constructed by the generic product theorem. -/
def compressSources (model : FiniteHiddenDAGSCM S projection) (queries : Fin count → NativeProbabilityQuery S) :
    SourceCompression model queries := by
  let events := fun index noise => (queries index).event (model.evalObserved (queries index).intervention noise)
  let solved := FiniteProductSourceCompression.compress model.sourceLaw model.noiseEnumeration
    model.noise_complete model.noiseDecidableEq events
  refine ⟨solved.law, solved.bounded, solved.positive, ?_⟩
  intro index
  have pushed := model.prior.map_probVal (model.evalObserved (queries index).intervention) (queries index).event
  exact QProb.equiv_trans (withSourceLaw_interventionalValue model solved.law (queries index))
    (QProb.equiv_trans (solved.preserved index) (QProb.equiv_symm pushed))

end FiniteHiddenDAGSCM
end Causality
end Thesis
