import Thesis.Probability.FiniteProbabilityPolynomialEncoding
import Thesis.Probability.PolynomialBoundCertificate

namespace Thesis
namespace Probability
namespace FiniteProbabilityPolynomial

open FiniteProduct RationalPolynomial

universe u
variable {sources : Nat} {Value : Fin sources → Type u}

/-!
# Checked polynomial bounds on actual finite probability values

`compileEncoded` constructs a polynomial together with its genuine source
probability assignment and the proofs of its nonnegative-cell and normalized
source constraints.  The lower/upper bound checkers consume that constructed
data, so a certificate producer need not supply a polynomial-likelihood
interface or assert that the model satisfies its basic probability laws.

The certificate's algebraic identity and coefficient signs are still checked
exactly.  Its conclusion is an inequality about the actual event probability
of the supplied independent law.  Rejection is not a disproof of the bound,
and the construction does not search for certificates or claim graph-wide
coverage across different structural mechanisms and hidden alphabets.
-/

/-- A probability compiler result with its semantic binding and proved source
constraints. The field `correct` is established by `compileEncoded`, rather
than requested as an unchecked correspondence from a certificate producer. -/
structure Compiled (law : IndependentLaw Value) (event : Event (Assignment sources Value)) where
  variableCount : Nat
  code : (index : Fin sources) → Value index → Fin variableCount
  polynomial : Polynomial variableCount
  parameters : Fin variableCount → SignedRatio
  sourceEquations : Fin sources → Polynomial variableCount
  correct : SignedRatio.Equiv (evaluate polynomial parameters) (law.prior.probVal event).toSignedRatio
  nonnegative : forall index, SignedRatio.Nonnegative (parameters index)
  normalized : forall index, SignedRatio.Equiv (evaluate (sourceEquations index) parameters) SignedRatio.zero

/-- Deduplicate the supplied source enumerations, encode their cells, and
assemble the polynomial, actual parameters and normalization proofs together.
Completeness of the finite enumerations is the only coverage premise. -/
def compileEncoded (law : IndependentLaw Value) (values : (index : Fin sources) → List (Value index))
    (complete : forall index value, value ∈ values index) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (event : Event (Assignment sources Value)) : Compiled law event := by
  let witness := encoding values complete decEq
  let code := sourceCode witness
  let parameters := sourceParameters law decEq witness
  refine ⟨witness.card, code, compile values decEq code event, parameters, normalization values decEq code,
    compile_sound law values complete decEq code parameters (sourceParameters_binding law decEq witness) event,
    sourceParameters_nonnegative law decEq witness, ?_⟩
  exact normalization_sound law values complete decEq code parameters (sourceParameters_binding law decEq witness)

/-- A supplied certificate may use individual cell nonnegativity and source
normalization. Both constraint families are already proved by the compiler;
the checker still verifies every coefficient sign and the full identity. -/
def Compiled.checkNonnegative {law : IndependentLaw Value} {event : Event (Assignment sources Value)} (compiled : Compiled law event)
    (target : Polynomial compiled.variableCount)
    (certificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount sources) : Bool :=
  PolynomialBoundCertificate.check coordinate compiled.sourceEquations target certificate

theorem Compiled.checkNonnegative_sound {law : IndependentLaw Value} {event : Event (Assignment sources Value)} (compiled : Compiled law event)
    (target : Polynomial compiled.variableCount)
    (certificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount sources)
    (accepted : compiled.checkNonnegative target certificate = true) : SignedRatio.Nonnegative (evaluate target compiled.parameters) :=
  PolynomialBoundCertificate.check_sound coordinate compiled.sourceEquations target certificate accepted compiled.parameters
    (fun index => (SignedRatio.nonnegative_congr (evaluate_coordinate index compiled.parameters)).mpr (compiled.nonnegative index)) compiled.normalized

/-- Certify `probability - bound ≥ 0`. No division or event-support premise
is needed for an unconditional event, even when its probability is zero. -/
def Compiled.checkLower {law : IndependentLaw Value} {event : Event (Assignment sources Value)} (compiled : Compiled law event)
    (bound : SignedRatio) (certificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount sources) : Bool :=
  compiled.checkNonnegative (sub compiled.polynomial (constant bound)) certificate

/-- Certify `bound - probability ≥ 0`, using the same exact source constraints
as the lower-bound checker. Signed bounds are allowed; signs are not guessed. -/
def Compiled.checkUpper {law : IndependentLaw Value} {event : Event (Assignment sources Value)} (compiled : Compiled law event)
    (bound : SignedRatio) (certificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount sources) : Bool :=
  compiled.checkNonnegative (sub (constant bound) compiled.polynomial) certificate

theorem Compiled.checkLower_sound {law : IndependentLaw Value} {event : Event (Assignment sources Value)} (compiled : Compiled law event)
    (bound : SignedRatio) (certificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount sources)
    (accepted : compiled.checkLower bound certificate = true) : SignedRatio.LE bound (law.prior.probVal event).toSignedRatio := by
  have positive := compiled.checkNonnegative_sound _ certificate accepted
  have evaluated := SignedRatio.equiv_trans (evaluate_sub compiled.polynomial (constant bound) compiled.parameters)
    (SignedRatio.add_congr compiled.correct (SignedRatio.neg_congr (evaluate_constant bound compiled.parameters)))
  exact (SignedRatio.nonnegative_congr evaluated).mp positive

theorem Compiled.checkUpper_sound {law : IndependentLaw Value} {event : Event (Assignment sources Value)} (compiled : Compiled law event)
    (bound : SignedRatio) (certificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount sources)
    (accepted : compiled.checkUpper bound certificate = true) : SignedRatio.LE (law.prior.probVal event).toSignedRatio bound := by
  have positive := compiled.checkNonnegative_sound _ certificate accepted
  have evaluated := SignedRatio.equiv_trans (evaluate_sub (constant bound) compiled.polynomial compiled.parameters)
    (SignedRatio.add_congr (evaluate_constant bound compiled.parameters) (SignedRatio.neg_congr compiled.correct))
  exact (SignedRatio.nonnegative_congr evaluated).mp positive

end FiniteProbabilityPolynomial
end Probability
end Thesis
