import Thesis.Probability.ConstructiveRealBilinearFubini
import Thesis.Probability.ConstructiveRealRationalEntropyLaw

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

theorem realDot_sub_values (size : Nat) (coefficients : Fin size → Int)
    (first second : Fin size → ConstructiveReal) :
    Equiv (realDot size coefficients (fun i => sub (first i) (second i)))
      (sub (realDot size coefficients first) (realDot size coefficients second)) :=
  equiv_trans (FiniteLinear.realDot_pair size coefficients _)
    (equiv_trans (FiniteLinear.pair_sub_second size _ first second)
      (add_congr (equiv_symm (FiniteLinear.realDot_pair size coefficients first)) (neg_congr (equiv_symm (FiniteLinear.realDot_pair size coefficients second)))))

/-- Rational row evaluation agrees with the generic finite bilinear sum. -/
theorem realRationalDot_pair (size : Nat) (coefficients : Fin size → SignedRatio) (values : Fin size → ConstructiveReal) :
    Equiv (realRationalDot size coefficients values) (FiniteLinear.pair size (fun i => ofSignedRatio (coefficients i)) values) := by
  induction size with
  | zero => exact equiv_refl zero
  | succ size ih =>
      exact equiv_trans (add_congr (equiv_refl _) (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))
        (equiv_trans (add_comm _ _) (equiv_symm (FiniteLinear.pair_succ size _ _)))

theorem realRationalDot_sub_values (size : Nat) (coefficients : Fin size → SignedRatio)
    (first second : Fin size → ConstructiveReal) :
    Equiv (realRationalDot size coefficients (fun i => sub (first i) (second i)))
      (sub (realRationalDot size coefficients first) (realRationalDot size coefficients second)) :=
  equiv_trans (realRationalDot_pair size coefficients _)
    (equiv_trans (FiniteLinear.pair_sub_second size _ first second)
      (add_congr (equiv_symm (realRationalDot_pair size coefficients first)) (neg_congr (equiv_symm (realRationalDot_pair size coefficients second)))))

theorem realRationalDot_negated (size : Nat) (coefficients : Fin size → SignedRatio) (values : Fin size → ConstructiveReal) :
    Equiv (realRationalDot size (fun i => SignedRatio.neg (coefficients i)) values) (neg (realRationalDot size coefficients values)) := by
  induction size with
  | zero => exact ofSignedRatio_neg SignedRatio.zero
  | succ size ih =>
      exact equiv_trans (add_congr (equiv_trans (mul_congr (ofSignedRatio_neg _) (equiv_refl _)) (neg_mul _ _))
        (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc))) (equiv_symm (neg_add _ _))

/-- Reverse the inequality, preserving its original rational presentation. -/
def RationalConstraint.reverse (row : RationalConstraint variables) : RationalConstraint variables :=
  ⟨fun i => SignedRatio.neg (row.coefficients i), SignedRatio.neg row.bound⟩

theorem RationalConstraint.reverse_real_lower (row : RationalConstraint variables) (values : Fin variables → ConstructiveReal) :
    row.reverse.RealHolds values ↔ LE (ofSignedRatio row.bound) (realRationalDot variables row.coefficients values) :=
  (le_congr (realRationalDot_negated variables row.coefficients values) (ofSignedRatio_neg row.bound)).trans (neg_le_neg_iff _ _)

theorem RationalConstraint.reverse_exact (row : RationalConstraint variables) (values : Fin variables → ConstructiveReal)
    (exactRow : Equiv (realRationalDot variables row.coefficients values) (ofSignedRatio row.bound)) :
    Equiv (realRationalDot variables row.reverse.coefficients values) (ofSignedRatio row.reverse.bound) :=
  equiv_trans (realRationalDot_negated variables row.coefficients values)
    (equiv_trans (neg_congr exactRow) (equiv_symm (ofSignedRatio_neg row.bound)))

end Thesis.Probability.Distros.RationalLinear

namespace Thesis.Probability.Distros.RationalEntropyProblem
open ConstructiveReal

/-- Fixed rational expectations are represented by pairs of original
closed inequalities. Redundant features and either sign of data are allowed. -/
def equalities (variables : Nat) (nonempty : 0 < variables) (features : List (RationalLinear.RationalConstraint variables)) : RationalEntropyProblem variables :=
  ⟨nonempty, features.flatMap (fun row => [row, row.reverse])⟩

theorem equalities_exact (nonempty : 0 < variables) (features : List (RationalLinear.RationalConstraint variables))
    (law : (equalities variables nonempty features).RealLaw) (row : RationalLinear.RationalConstraint variables) (member : row ∈ features) :
    Equiv (RationalLinear.realRationalDot variables row.coefficients (fun i => (law.mass i).value)) (ofSignedRatio row.bound) :=
  ⟨law.valid row (List.mem_flatMap.mpr ⟨row, member, List.mem_cons_self ..⟩),
    (row.reverse_real_lower _).mp (law.valid row.reverse (List.mem_flatMap.mpr
      ⟨row, member, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩))⟩

/-- Every actual row in the paired representation has its bound exactly;
this includes the reversed rows and all duplicate occurrences. -/
theorem equalities_allRows_exact (nonempty : 0 < variables) (features : List (RationalLinear.RationalConstraint variables))
    (law : (equalities variables nonempty features).RealLaw) (row : RationalLinear.RationalConstraint variables)
    (member : row ∈ (equalities variables nonempty features).rows) :
    Equiv (RationalLinear.realRationalDot variables row.coefficients (fun i => (law.mass i).value)) (ofSignedRatio row.bound) := by
  obtain ⟨original, listed, inside⟩ := List.mem_flatMap.mp member
  have exactRow := equalities_exact nonempty features law original listed
  rcases List.mem_cons.mp inside with same | later
  · cases same; exact exactRow
  · have same := List.mem_singleton.mp later
    cases same
    exact original.reverse_exact _ exactRow

end Thesis.Probability.Distros.RationalEntropyProblem
