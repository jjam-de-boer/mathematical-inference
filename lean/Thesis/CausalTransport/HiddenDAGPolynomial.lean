import Thesis.CausalTransport.HiddenDAGSourceCompression
import Thesis.Probability.FiniteProbabilityPolynomialCertificates

namespace Thesis
namespace Causality
namespace FiniteHiddenDAGSCM

open Probability

/-!
# Exact polynomial compilation and supplied bounds for native causal queries

The primitive query is evaluated by the unchanged native structural equations
under its hard intervention.  Its noise event is then compiled from the actual
independent source law, with source variables, binding and normalization all
constructed internally.  The producer supplies only a bound certificate, not
a polynomial-likelihood correspondence or source-positivity assumption.

The compiler's polynomial and basic constraints depend on the finite source
presentation and structural readout, not the source probabilities.  The final
source-law theorems therefore reuse a checked bound for every independent law
on this same finite structural template, including zero-containing laws.

This does not quantify over different mechanisms, hidden endogenous alphabets
or arbitrary alternate templates on the same graph.  Additional observed-law
constraints and supported conditional ratios require their own assembly;
neither graph-wide completeness nor a general optimizer is asserted here.
-/

def probabilityProgram (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S) :
    FiniteProbabilityPolynomial.Compiled model.sourceLaw (fun noise => query.event (model.evalObserved query.intervention noise)) :=
  FiniteProbabilityPolynomial.compileEncoded model.sourceLaw model.noiseEnumeration model.noise_complete model.noiseDecidableEq _

abbrev ProbabilityBoundCertificate (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S) :=
  PolynomialBoundCertificate.Certificate (model.probabilityProgram query).variableCount
    (model.probabilityProgram query).variableCount projection.hiddenDAG.count

theorem probabilityProgram_sound (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S) :
    SignedRatio.Equiv (RationalPolynomial.evaluate (model.probabilityProgram query).polynomial (model.probabilityProgram query).parameters)
      (model.interventionalValue query.intervention query.event).toSignedRatio :=
  SignedRatio.equiv_trans (model.probabilityProgram query).correct
    (QProb.toSignedRatio_congr (QProb.equiv_symm (model.prior.map_probVal (model.evalObserved query.intervention) query.event)))

def checkProbabilityLower (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S) (bound : SignedRatio)
    (certificate : model.ProbabilityBoundCertificate query) : Bool := (model.probabilityProgram query).checkLower bound certificate

def checkProbabilityUpper (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S) (bound : SignedRatio)
    (certificate : model.ProbabilityBoundCertificate query) : Bool := (model.probabilityProgram query).checkUpper bound certificate

theorem checkProbabilityLower_sound (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S) (bound : SignedRatio)
    (certificate : model.ProbabilityBoundCertificate query) (accepted : model.checkProbabilityLower query bound certificate = true) :
    SignedRatio.LE bound (model.interventionalValue query.intervention query.event).toSignedRatio := by
  have sourceBound := (model.probabilityProgram query).checkLower_sound bound certificate accepted
  have pushed := QProb.toSignedRatio_congr (model.prior.map_probVal (model.evalObserved query.intervention) query.event)
  exact (SignedRatio.le_congr (SignedRatio.equiv_refl bound) (SignedRatio.equiv_symm pushed)).mp sourceBound

theorem checkProbabilityUpper_sound (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S) (bound : SignedRatio)
    (certificate : model.ProbabilityBoundCertificate query) (accepted : model.checkProbabilityUpper query bound certificate = true) :
    SignedRatio.LE (model.interventionalValue query.intervention query.event).toSignedRatio bound := by
  have sourceBound := (model.probabilityProgram query).checkUpper_sound bound certificate accepted
  have pushed := QProb.toSignedRatio_congr (model.prior.map_probVal (model.evalObserved query.intervention) query.event)
  exact (SignedRatio.le_congr (SignedRatio.equiv_symm pushed) (SignedRatio.equiv_refl bound)).mp sourceBound

/-- The structural template's polynomial is unchanged when only its source
law changes.  The source probabilities are parameters, not frozen coefficients
silently baked into this compiled causal formula. -/
theorem probabilityProgram_polynomial_withSourceLaw (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (query : NativeProbabilityQuery S) :
    ((model.withSourceLaw law).probabilityProgram query).polynomial = (model.probabilityProgram query).polynomial := by
  have readout : (fun noise => query.event ((model.withSourceLaw law).evalObserved query.intervention noise)) =
      (fun noise => query.event (model.evalObserved query.intervention noise)) :=
    funext (fun noise => congrArg query.event (model.withSourceLaw_evalObserved law query.intervention noise))
  exact congrArg (FiniteProbabilityPolynomial.compile model.noiseEnumeration model.noiseDecidableEq
    (FiniteProbabilityPolynomial.sourceCode (FiniteProbabilityPolynomial.encoding model.noiseEnumeration model.noise_complete model.noiseDecidableEq))) readout

theorem checkProbabilityLower_withSourceLaw (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (query : NativeProbabilityQuery S) (bound : SignedRatio)
    (certificate : model.ProbabilityBoundCertificate query) :
    (model.withSourceLaw law).checkProbabilityLower query bound certificate = model.checkProbabilityLower query bound certificate := by
  unfold checkProbabilityLower FiniteProbabilityPolynomial.Compiled.checkLower FiniteProbabilityPolynomial.Compiled.checkNonnegative
  rw [probabilityProgram_polynomial_withSourceLaw]
  -- Normalization is built solely from the unchanged finite noise types and
  -- enumerations. After rewriting the readout, these constraint fields agree
  -- by computation; no equivalence of arbitrary source laws is assumed.
  rfl

theorem checkProbabilityUpper_withSourceLaw (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (query : NativeProbabilityQuery S) (bound : SignedRatio)
    (certificate : model.ProbabilityBoundCertificate query) :
    (model.withSourceLaw law).checkProbabilityUpper query bound certificate = model.checkProbabilityUpper query bound certificate := by
  unfold checkProbabilityUpper FiniteProbabilityPolynomial.Compiled.checkUpper FiniteProbabilityPolynomial.Compiled.checkNonnegative
  rw [probabilityProgram_polynomial_withSourceLaw]
  rfl

theorem checkProbabilityLower_sound_forSourceLaw (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S)
    (bound : SignedRatio) (certificate : model.ProbabilityBoundCertificate query) (accepted : model.checkProbabilityLower query bound certificate = true)
    (law : FiniteProduct.IndependentLaw model.Noise) : SignedRatio.LE bound ((model.withSourceLaw law).interventionalValue query.intervention query.event).toSignedRatio := by
  apply checkProbabilityLower_sound (model.withSourceLaw law) query bound certificate
  rw [checkProbabilityLower_withSourceLaw]
  exact accepted

theorem checkProbabilityUpper_sound_forSourceLaw (model : FiniteHiddenDAGSCM S projection) (query : NativeProbabilityQuery S)
    (bound : SignedRatio) (certificate : model.ProbabilityBoundCertificate query) (accepted : model.checkProbabilityUpper query bound certificate = true)
    (law : FiniteProduct.IndependentLaw model.Noise) : SignedRatio.LE ((model.withSourceLaw law).interventionalValue query.intervention query.event).toSignedRatio bound := by
  apply checkProbabilityUpper_sound (model.withSourceLaw law) query bound certificate
  rw [checkProbabilityUpper_withSourceLaw]
  exact accepted

end FiniteHiddenDAGSCM
end Causality
end Thesis
