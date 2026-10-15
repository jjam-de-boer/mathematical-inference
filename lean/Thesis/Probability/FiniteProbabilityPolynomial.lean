import Thesis.Probability.RationalPolynomialFinite
import Thesis.Probability.RationalValues
import Thesis.Probability.FiniteProductReplacement

namespace Thesis
namespace Probability

namespace QProb

theorem toSignedRatio_listSum (values : List QProb) :
    (listSum values).toSignedRatio = SignedRatio.listSum (values.map toSignedRatio) := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [listSum, toSignedRatio_add, List.map_cons, SignedRatio.listSum, inductionHypothesis]

theorem toSignedRatio_qProduct (sources : Nat) (values : Fin sources → QProb) :
    (FiniteProduct.qProduct sources values).toSignedRatio =
      RationalMonomial.product sources (fun index => (values index).toSignedRatio) := by
  induction sources with
  | zero => rfl
  | succ sources inductionHypothesis =>
      simp only [FiniteProduct.qProduct, RationalMonomial.product, toSignedRatio_mul]
      rw [inductionHypothesis]

end QProb

namespace RationalPolynomial

variable {variables : Nat}

def finProduct : (sources : Nat) → (Fin sources → Polynomial variables) → Polynomial variables
  | 0, _ => constant SignedRatio.one
  | sources + 1, polynomials => mul (polynomials (Fin.last sources)) (finProduct sources (fun index => polynomials index.castSucc))

theorem evaluate_finProduct (sources : Nat) (polynomials : Fin sources → Polynomial variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (finProduct sources polynomials) values)
      (RationalMonomial.product sources (fun index => evaluate (polynomials index) values)) := by
  induction sources with
  | zero => exact evaluate_constant SignedRatio.one values
  | succ sources inductionHypothesis =>
      exact SignedRatio.equiv_trans (evaluate_mul _ _ values)
        (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (inductionHypothesis (fun index => polynomials index.castSucc)))

end RationalPolynomial

namespace FiniteProbabilityPolynomial

open FiniteProduct RationalPolynomial

universe u
variable {sources variables : Nat} {Value : Fin sources → Type u}

/-!
# Compile finite independent-source event probabilities into polynomials

Each coordinate state is assigned a polynomial variable.  A joint assignment
contributes the product of its coordinate variables; the event polynomial is
the sum of those products over all selected assignments.  The supplied finite
coordinate lists are deduplicated at joint-assignment level, so repeated
enumeration labels cannot multiply a probability accidentally.

The semantic theorem uses the actual independent prior and coordinate records.
It proves equality with their ordinary event probability for every parameter
assignment binding variables to the respective singleton probabilities.  It
does not assume a symbolic likelihood interface or trust a producer's claim
that the printed polynomial represents a causal query.  A native adapter must
construct the variable encoding and binding and supply the structural readout.

Zero-probability states, repeated record atoms, heterogeneous finite coordinate
types and an empty source family are permitted.  No conditional is evaluated
or divided out by this unconditional event compiler.
-/

def assignments (values : (index : Fin sources) → List (Value index)) (decEq : (index : Fin sources) → DecidableEq (Value index)) :
    List (Assignment sources Value) :=
  @deduplicate _ (assignmentDecidableEq sources Value decEq) (enumeration sources Value values)

theorem assignments_complete (values : (index : Fin sources) → List (Value index))
    (complete : forall index value, value ∈ values index) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (assignment : Assignment sources Value) : assignment ∈ assignments values decEq := by
  letI : DecidableEq (Assignment sources Value) := assignmentDecidableEq sources Value decEq
  exact (mem_deduplicate _ _).mpr (enumeration_complete sources Value values complete assignment)

theorem assignments_nodup (values : (index : Fin sources) → List (Value index)) (decEq : (index : Fin sources) → DecidableEq (Value index)) :
    (assignments values decEq).Nodup := by
  letI : DecidableEq (Assignment sources Value) := assignmentDecidableEq sources Value decEq
  exact deduplicate_nodup _

def sourceProduct (code : (index : Fin sources) → Value index → Fin variables) (assignment : Assignment sources Value) : Polynomial variables :=
  finProduct sources (fun index => coordinate (code index (assignment index)))

def compile (values : (index : Fin sources) → List (Value index)) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (code : (index : Fin sources) → Value index → Fin variables) (event : Event (Assignment sources Value)) : Polynomial variables :=
  sum (((assignments values decEq).filter event).map (sourceProduct code))

def cellProbability (law : IndependentLaw Value) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (index : Fin sources) (value : Value index) : QProb :=
  (law.factor index).probVal (@FiniteProbRecord.singletonEvent _ (decEq index) value)

theorem singleton_product_law (law : IndependentLaw Value) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (assignment : Assignment sources Value) :
    QProb.Equiv (law.prior.probVal (@FiniteProbRecord.singletonEvent _ (assignmentDecidableEq sources Value decEq) assignment))
      (qProduct sources (fun index => cellProbability law decEq index (assignment index))) := by
  have rectangular := law.product_law (fun index => @FiniteProbRecord.singletonEvent _ (decEq index) (assignment index))
  rw [rectangularEvent_assignment_singleton decEq assignment] at rectangular
  exact rectangular

theorem sourceProduct_sound (law : IndependentLaw Value) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (code : (index : Fin sources) → Value index → Fin variables) (parameters : Fin variables → SignedRatio)
    (binding : forall index value, SignedRatio.Equiv (parameters (code index value)) (cellProbability law decEq index value).toSignedRatio)
    (assignment : Assignment sources Value) :
    SignedRatio.Equiv (evaluate (sourceProduct code assignment) parameters)
      (qProduct sources (fun index => cellProbability law decEq index (assignment index))).toSignedRatio := by
  have compared := RationalMonomial.product_congr sources
    (fun index => evaluate (coordinate (code index (assignment index))) parameters)
    (fun index => (cellProbability law decEq index (assignment index)).toSignedRatio)
    (fun index => SignedRatio.equiv_trans (evaluate_coordinate _ parameters) (binding index (assignment index)))
  rw [← QProb.toSignedRatio_qProduct] at compared
  exact SignedRatio.equiv_trans (evaluate_finProduct sources _ parameters) compared

/-- The constructed polynomial evaluates to the same event probability as
the supplied finite independent law.  In particular the result holds at zero
source cells; no reciprocal of a source probability appears in the proof. -/
theorem compile_sound (law : IndependentLaw Value) (values : (index : Fin sources) → List (Value index))
    (complete : forall index value, value ∈ values index) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (code : (index : Fin sources) → Value index → Fin variables) (parameters : Fin variables → SignedRatio)
    (binding : forall index value, SignedRatio.Equiv (parameters (code index value)) (cellProbability law decEq index value).toSignedRatio)
    (event : Event (Assignment sources Value)) :
    SignedRatio.Equiv (evaluate (compile values decEq code event) parameters) (law.prior.probVal event).toSignedRatio := by
  letI : DecidableEq (Assignment sources Value) := assignmentDecidableEq sources Value decEq
  let states := assignments values decEq
  have expanded := law.prior.probVal_equiv_listSum_singletons states (assignments_nodup values decEq)
    (assignments_complete values complete decEq) event
  have encoded := QProb.toSignedRatio_congr expanded
  rw [QProb.toSignedRatio_listSum] at encoded
  simp only [List.map_map, Function.comp_def] at encoded
  have terms := SignedRatio.listSum_map_congr (states.filter event)
    (fun assignment => evaluate (sourceProduct code assignment) parameters)
    (fun assignment => (law.prior.probVal (FiniteProbRecord.singletonEvent assignment)).toSignedRatio)
    (fun assignment => SignedRatio.equiv_trans (sourceProduct_sound law decEq code parameters binding assignment)
      (QProb.toSignedRatio_congr (QProb.equiv_symm (singleton_product_law law decEq assignment))))
  exact SignedRatio.equiv_trans (by
    simpa only [compile, states, List.map_map, Function.comp_def] using
      evaluate_sum ((states.filter event).map (sourceProduct code)) parameters)
    (SignedRatio.equiv_trans terms (SignedRatio.equiv_symm encoded))

end FiniteProbabilityPolynomial
end Probability
end Thesis
