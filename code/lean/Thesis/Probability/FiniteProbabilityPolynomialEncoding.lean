import Thesis.Probability.FiniteProbabilityPolynomial
import Thesis.Probability.SignedRatioOrder

namespace Thesis
namespace Probability
namespace FiniteProbabilityPolynomial

open FiniteProduct RationalPolynomial

universe u
variable {sources variables : Nat} {Value : Fin sources → Type u}

/-!
# Construct the source-variable encoding and its probability constraints

One variable is allocated to each distinct coordinate/state pair in the
supplied finite source presentation.  Both encoding and decoding are actual
finite data with proved inverse laws; callers do not choose an encoding or
assume a binding to their model's probabilities.

The resulting parameter assignment uses the coordinate records' genuine
singleton probabilities, including zeros and repeated atom labels.  Every
parameter is nonnegative and every coordinate's distinct-state sum is one.
These facts justify the constraints that the bound checker will consume.
They do not imply that arbitrary additional observational constraints hold.
-/

abbrev Cell (Value : Fin sources → Type u) := Sigma Value

def cellDecidableEq (decEq : (index : Fin sources) → DecidableEq (Value index)) : DecidableEq (Cell Value) := by
  letI : (index : Fin sources) → DecidableEq (Value index) := decEq
  infer_instance

def cells (values : (index : Fin sources) → List (Value index)) : List (Cell Value) :=
  (List.finRange sources).flatMap (fun index => (values index).map (fun value => (⟨index, value⟩ : Cell Value)))

theorem cells_complete (values : (index : Fin sources) → List (Value index))
    (complete : forall index value, value ∈ values index) (cell : Cell Value) : cell ∈ cells values := by
  rcases cell with ⟨index, value⟩
  exact List.mem_flatMap.mpr ⟨index, List.mem_finRange index, List.mem_map.mpr ⟨value, complete index value, rfl⟩⟩

def encoding (values : (index : Fin sources) → List (Value index)) (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin sources) → DecidableEq (Value index)) : FiniteWitness (Cell Value) := by
  letI : DecidableEq (Cell Value) := cellDecidableEq decEq
  exact FiniteWitness.ofList (deduplicate (cells values))
    (fun cell => (mem_deduplicate _ _).mpr (cells_complete values complete cell)) (deduplicate_nodup _)

def sourceCode (witness : FiniteWitness (Cell Value)) (index : Fin sources) (value : Value index) : Fin witness.card :=
  witness.encode ⟨index, value⟩

def sourceParameters (law : IndependentLaw Value) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (witness : FiniteWitness (Cell Value)) (index : Fin witness.card) : SignedRatio :=
  let cell := witness.decode index
  (cellProbability law decEq cell.1 cell.2).toSignedRatio

theorem sourceParameters_binding (law : IndependentLaw Value) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (witness : FiniteWitness (Cell Value)) (index : Fin sources) (value : Value index) :
    SignedRatio.Equiv (sourceParameters law decEq witness (sourceCode witness index value))
      (cellProbability law decEq index value).toSignedRatio := by
  dsimp only [sourceParameters, sourceCode]
  rw [witness.decode_encode]
  exact SignedRatio.equiv_refl _

theorem sourceParameters_nonnegative (law : IndependentLaw Value) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (witness : FiniteWitness (Cell Value)) (index : Fin witness.card) :
    SignedRatio.Nonnegative (sourceParameters law decEq witness index) := QProb.toSignedRatio_nonnegative _

def statesAt (values : (index : Fin sources) → List (Value index)) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (index : Fin sources) : List (Value index) := @deduplicate _ (decEq index) (values index)

theorem statesAt_complete (values : (index : Fin sources) → List (Value index)) (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin sources) → DecidableEq (Value index)) (index : Fin sources) (value : Value index) : value ∈ statesAt values decEq index := by
  letI : DecidableEq (Value index) := decEq index
  exact (mem_deduplicate _ _).mpr (complete index value)

def normalization (values : (index : Fin sources) → List (Value index)) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (code : (index : Fin sources) → Value index → Fin variables) (index : Fin sources) : Polynomial variables :=
  sub (sum ((statesAt values decEq index).map fun value => coordinate (code index value))) (constant SignedRatio.one)

theorem cellProbabilities_sum (law : IndependentLaw Value) (values : (index : Fin sources) → List (Value index))
    (complete : forall index value, value ∈ values index) (decEq : (index : Fin sources) → DecidableEq (Value index)) (index : Fin sources) :
    QProb.Equiv (QProb.listSum ((statesAt values decEq index).map (cellProbability law decEq index))) QProb.one := by
  letI : DecidableEq (Value index) := decEq index
  have dissected := (law.factor index).probVal_membership_equiv_listSum (statesAt values decEq index) (deduplicate_nodup _)
  have allSelected : FiniteProbRecord.membershipEvent (statesAt values decEq index) = topEvent := by
    funext value
    exact decide_eq_true (statesAt_complete values complete decEq index value)
  rw [allSelected] at dissected
  exact QProb.equiv_trans (QProb.equiv_symm dissected) (law.factor index).normalization

theorem normalization_sound (law : IndependentLaw Value) (values : (index : Fin sources) → List (Value index))
    (complete : forall index value, value ∈ values index) (decEq : (index : Fin sources) → DecidableEq (Value index))
    (code : (index : Fin sources) → Value index → Fin variables) (parameters : Fin variables → SignedRatio)
    (binding : forall index value, SignedRatio.Equiv (parameters (code index value)) (cellProbability law decEq index value).toSignedRatio)
    (index : Fin sources) : SignedRatio.Equiv (evaluate (normalization values decEq code index) parameters) SignedRatio.zero := by
  let states := statesAt values decEq index
  have evaluated := evaluate_sum (states.map fun value => coordinate (code index value)) parameters
  simp only [List.map_map, Function.comp_def] at evaluated
  have bound := SignedRatio.listSum_map_congr states
    (fun value => evaluate (coordinate (code index value)) parameters)
    (fun value => (cellProbability law decEq index value).toSignedRatio)
    (fun value => SignedRatio.equiv_trans (evaluate_coordinate _ parameters) (binding index value))
  have total := QProb.toSignedRatio_congr (cellProbabilities_sum law values complete decEq index)
  rw [QProb.toSignedRatio_listSum, QProb.toSignedRatio_one] at total
  simp only [List.map_map, Function.comp_def] at total
  have normalized := SignedRatio.equiv_trans evaluated (SignedRatio.equiv_trans bound total)
  exact SignedRatio.equiv_trans (evaluate_sub _ _ parameters)
    ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_trans normalized (SignedRatio.equiv_symm (evaluate_constant SignedRatio.one parameters))))

end FiniteProbabilityPolynomial
end Probability
end Thesis
