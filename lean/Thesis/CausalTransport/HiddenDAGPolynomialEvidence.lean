import Thesis.CausalTransport.HiddenDAGPolynomialExpressions

namespace Thesis
namespace Causality

open Probability

/-!
# Supplied causal bound certificates constrained by observed probabilities

A probability equation records a native query and a rational reference value.
The checker compiles that query itself and subtracts the reference constant;
the caller supplies only evidence that the candidate model fits the stated
data. Source nonnegativity and normalization remain internally proved facts.

Observational data are obtained by empty intervention. A finite catalogue can
contain selected observed events, or `observationalEquations` can construct
the complete observed table. Its satisfaction theorem shows that the latter
is exactly equality of all observed event probabilities, including zeros.

The final theorem quantifies over every independent source law on the same
structural template that fits the catalogue. It does not silently reuse the
original model's fitted data for a new, incompatible law. Additional catalogue
queries under hard interventions are allowed, with the corresponding explicit
data-fit premise. No constraint is trusted merely because a producer lists it.
-/

structure NativeProbabilityEquation (S : ObservedSignature) where
  query : NativeProbabilityQuery S
  reference : QProb

namespace FiniteHiddenDAGSCM

variable {equationCount : Nat}

def SatisfiesProbabilityEquations (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) : Prop :=
  forall index, QProb.Equiv (model.interventionalValue (equations index).query.intervention (equations index).query.event)
    (equations index).reference

/-- Source normalization occupies the first block of indices. The second
block is built from the stated data queries. The split is a natural-number
decision, not a choice of proof or a decision for arbitrary propositions. -/
def polynomialEvidenceEquations (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S)
    (index : Fin (projection.hiddenDAG.count + equationCount)) : RationalPolynomial.Polynomial model.polynomialEncoding.card :=
  if isSource : index.val < projection.hiddenDAG.count then model.polynomialSourceEquations ⟨index.val, isSource⟩
  else
    let selected : Fin equationCount := ⟨index.val - projection.hiddenDAG.count, by have bounded := index.isLt; omega⟩
    RationalPolynomial.sub (model.expressionPolynomial (.probability (equations selected).query))
      (RationalPolynomial.constant (equations selected).reference.toSignedRatio)

theorem polynomialEvidenceEquations_vanish (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (fits : model.SatisfiesProbabilityEquations equations)
    (index : Fin (projection.hiddenDAG.count + equationCount)) :
    SignedRatio.Equiv (RationalPolynomial.evaluate (model.polynomialEvidenceEquations equations index) model.polynomialParameters) SignedRatio.zero := by
  unfold polynomialEvidenceEquations
  split
  · exact model.polynomialSourceEquations_vanish _
  · rename_i isData
    let selected : Fin equationCount := ⟨index.val - projection.hiddenDAG.count, by have bounded := index.isLt; omega⟩
    have querySound := model.expressionPolynomial_sound (.probability (equations selected).query)
    have fitted := SignedRatio.equiv_trans querySound (QProb.toSignedRatio_congr (fits selected))
    exact SignedRatio.equiv_trans (RationalPolynomial.evaluate_sub _ _ model.polynomialParameters)
      ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_trans fitted
        (SignedRatio.equiv_symm (RationalPolynomial.evaluate_constant _ model.polynomialParameters))))

abbrev ExpressionBoundCertificate (model : FiniteHiddenDAGSCM S projection) (equationCount : Nat) :=
  PolynomialBoundCertificate.Certificate model.polynomialEncoding.card model.polynomialEncoding.card (projection.hiddenDAG.count + equationCount)

/-- Check nonnegativity of a signed causal expression. A successful Boolean
result proves a bound only for candidates satisfying the displayed data, as
made explicit by `checkExpressionNonnegative_sound` below. -/
def checkExpressionNonnegative (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (expression : NativePolynomialExpression S)
    (certificate : model.ExpressionBoundCertificate equationCount) : Bool :=
  PolynomialBoundCertificate.check RationalPolynomial.coordinate (model.polynomialEvidenceEquations equations)
    (model.expressionPolynomial expression) certificate

theorem checkExpressionNonnegative_sound (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (expression : NativePolynomialExpression S)
    (certificate : model.ExpressionBoundCertificate equationCount) (accepted : model.checkExpressionNonnegative equations expression certificate = true)
    (fits : model.SatisfiesProbabilityEquations equations) : SignedRatio.Nonnegative (model.expressionValue expression) := by
  have checked := PolynomialBoundCertificate.check_sound RationalPolynomial.coordinate (model.polynomialEvidenceEquations equations)
    (model.expressionPolynomial expression) certificate accepted model.polynomialParameters
    (fun index => (SignedRatio.nonnegative_congr (RationalPolynomial.evaluate_coordinate index model.polynomialParameters)).mpr
      (model.polynomialParameters_nonnegative index)) (model.polynomialEvidenceEquations_vanish equations fits)
  exact (SignedRatio.nonnegative_congr (model.expressionPolynomial_sound expression)).mp checked

def checkExpressionLower (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (expression : NativePolynomialExpression S) (bound : SignedRatio)
    (certificate : model.ExpressionBoundCertificate equationCount) : Bool :=
  model.checkExpressionNonnegative equations (expression.sub (.constant bound)) certificate

def checkExpressionUpper (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (expression : NativePolynomialExpression S) (bound : SignedRatio)
    (certificate : model.ExpressionBoundCertificate equationCount) : Bool :=
  model.checkExpressionNonnegative equations ((.constant bound : NativePolynomialExpression S).sub expression) certificate

theorem checkExpressionLower_sound (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (expression : NativePolynomialExpression S) (bound : SignedRatio)
    (certificate : model.ExpressionBoundCertificate equationCount) (accepted : model.checkExpressionLower equations expression bound certificate = true)
    (fits : model.SatisfiesProbabilityEquations equations) : SignedRatio.LE bound (model.expressionValue expression) :=
  model.checkExpressionNonnegative_sound equations (expression.sub (.constant bound)) certificate accepted fits

theorem checkExpressionUpper_sound (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (expression : NativePolynomialExpression S) (bound : SignedRatio)
    (certificate : model.ExpressionBoundCertificate equationCount) (accepted : model.checkExpressionUpper equations expression bound certificate = true)
    (fits : model.SatisfiesProbabilityEquations equations) : SignedRatio.LE (model.expressionValue expression) bound :=
  model.checkExpressionNonnegative_sound equations ((.constant bound : NativePolynomialExpression S).sub expression) certificate accepted fits

theorem polynomialEvidenceEquations_withSourceLaw (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (equations : Fin equationCount → NativeProbabilityEquation S) :
    (model.withSourceLaw law).polynomialEvidenceEquations equations = model.polynomialEvidenceEquations equations := by
  funext index
  unfold polynomialEvidenceEquations
  split
  · rfl
  · rw [expressionPolynomial_withSourceLaw]

theorem checkExpressionNonnegative_withSourceLaw (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (equations : Fin equationCount → NativeProbabilityEquation S)
    (expression : NativePolynomialExpression S) (certificate : model.ExpressionBoundCertificate equationCount) :
    (model.withSourceLaw law).checkExpressionNonnegative equations expression certificate = model.checkExpressionNonnegative equations expression certificate := by
  unfold checkExpressionNonnegative
  rw [polynomialEvidenceEquations_withSourceLaw, expressionPolynomial_withSourceLaw]

/-- Uniform validity over every fitted independent source law on this
template. The data-fit premise refers to the replacement model itself. -/
theorem checkExpressionNonnegative_sound_forSourceLaw (model : FiniteHiddenDAGSCM S projection)
    (equations : Fin equationCount → NativeProbabilityEquation S) (expression : NativePolynomialExpression S)
    (certificate : model.ExpressionBoundCertificate equationCount) (accepted : model.checkExpressionNonnegative equations expression certificate = true)
    (law : FiniteProduct.IndependentLaw model.Noise) (fits : (model.withSourceLaw law).SatisfiesProbabilityEquations equations) :
    SignedRatio.Nonnegative ((model.withSourceLaw law).expressionValue expression) := by
  apply checkExpressionNonnegative_sound (model.withSourceLaw law) equations expression certificate
  · rw [checkExpressionNonnegative_withSourceLaw]
    exact accepted
  · exact fits

/-- The full observed table is assembled automatically, not left as a
producer's claim that its selected equations happen to cover every cell. -/
def observationalEquations (S : ObservedSignature) (reference : FiniteProbRecord S.Assignment)
    (index : Fin S.assignmentEnumeration.length) : NativeProbabilityEquation S :=
  let event := FiniteProbRecord.singletonEvent (S.assignmentEnumeration.get index)
  ⟨⟨HardIntervention.empty S, event⟩, reference.probVal event⟩

theorem satisfies_observationalEquations_iff (model : FiniteHiddenDAGSCM S projection) (reference : FiniteProbRecord S.Assignment) :
    model.SatisfiesProbabilityEquations (observationalEquations S reference) ↔
      (forall event, QProb.Equiv (model.observationalValue event) (reference.probVal event)) := by
  constructor
  · intro fits event
    apply FiniteProbRecord.probVal_extensional_of_singletons _ _ S.assignmentEnumeration
      S.assignmentEnumeration_nodup S.assignmentEnumeration_complete (fun assignment => ?_) event
    rcases List.mem_iff_get.mp (S.assignmentEnumeration_complete assignment) with ⟨index, same⟩
    have fitted := fits index
    change QProb.Equiv (model.observationalValue (FiniteProbRecord.singletonEvent (S.assignmentEnumeration.get index)))
      (reference.probVal (FiniteProbRecord.singletonEvent (S.assignmentEnumeration.get index))) at fitted
    rw [same] at fitted
    exact fitted
  · intro same index
    exact same (FiniteProbRecord.singletonEvent (S.assignmentEnumeration.get index))

end FiniteHiddenDAGSCM
end Causality
end Thesis
