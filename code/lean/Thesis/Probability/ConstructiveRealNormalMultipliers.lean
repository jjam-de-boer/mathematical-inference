import Thesis.Probability.ConstructiveRealDualSystem

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear
open IntegerLinearAlgebra

/-- Actual multipliers and normalization offset, including nonnegative
signs and attained dual value. Complementary slackness follows from these
identities and primal feasibility, without selecting an active subset. -/
structure NormalMultipliers (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (gradient : Fin columns → ConstructiveReal) (target : ConstructiveReal) where
  offset : ConstructiveReal
  coefficient : Fin rows → ConstructiveReal
  nonnegative : ∀ r, LE zero (coefficient r)
  represents : ∀ i, Equiv (gradient i) (add offset (realDot rows (fun r => matrix r i) coefficient))
  attained : Equiv (add offset (realDot rows bounds coefficient)) target

/-- Sign rows, both orientations of each stationarity equation, and both
orientations of the attained-value equation. This list uses every original
row; zero and redundant constraints do not require a rank assumption. -/
def multiplierSignatures (rows columns : Nat) : List (DualSignature rows columns) :=
  (((List.finRange rows).map DualSignature.signConstraint) ++
    ((List.finRange columns).flatMap (fun i => [DualSignature.columnConstraint i, (DualSignature.columnConstraint i).reverse]))) ++
    [DualSignature.valueConstraint, DualSignature.valueConstraint.reverse]

private theorem sign_member (r : Fin rows) :
    (DualSignature.signConstraint r : DualSignature rows columns) ∈ multiplierSignatures rows columns :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩))

private theorem column_member (i : Fin columns) :
    (DualSignature.columnConstraint i : DualSignature rows columns) ∈ multiplierSignatures rows columns :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_cons_self ..⟩))

private theorem reverse_column_member (i : Fin columns) :
    (DualSignature.columnConstraint i : DualSignature rows columns).reverse ∈ multiplierSignatures rows columns :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨i, List.mem_finRange i, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩))

private theorem value_member :
    (DualSignature.valueConstraint : DualSignature rows columns) ∈ multiplierSignatures rows columns :=
  List.mem_append_right _ (List.mem_cons_self ..)

private theorem reverse_value_member :
    (DualSignature.valueConstraint : DualSignature rows columns).reverse ∈ multiplierSignatures rows columns :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- Compute signed normal-cone coefficients from the full variational
condition at a quantitatively positive simplex point. The Farkas premise
is proved by explicit feasible perturbations, and finite elimination
returns the coefficients as data. No independent-row, activity-decision,
or multiplier-existence premise is imposed. -/
def normalMultipliers (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (masses gradient : Fin columns → ConstructiveReal)
    (lower : Fin columns → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (masses i))
    (normalized : Equiv (realDot columns (fun _ => 1) masses) one)
    (valid : ∀ r, LE (realDot columns (matrix r) masses) (realInteger (bounds r)))
    (variational : SimplexVariational matrix bounds masses gradient) :
    NormalMultipliers matrix bounds gradient (FiniteLinear.pair columns masses gradient) := by
  let target := FiniteLinear.pair columns masses gradient
  let signatures := multiplierSignatures rows columns
  let solved := solveFarkas (dualRows matrix bounds gradient target signatures)
    (farkas_of_variational matrix bounds masses gradient lower positive normalized valid variational signatures)
  have holds (signature : DualSignature rows columns) (member : signature ∈ signatures) :
      (signature.row matrix bounds gradient target).Holds solved.val :=
    solved.property _ (List.mem_map.mpr ⟨signature, member, rfl⟩)
  have equality (signature : DualSignature rows columns) (free : ∀ r, signature.cone r = 0)
      (member : signature ∈ signatures) (reverseMember : signature.reverse ∈ signatures) :
      Equiv (realDot (rows + 1) (signature.row matrix bounds gradient target).coefficients solved.val)
        (signature.row matrix bounds gradient target).bound :=
    ⟨holds signature member, (signature.reverse_holds_iff matrix bounds gradient target free solved.val).mp (holds signature.reverse reverseMember)⟩
  refine ⟨solved.val (Fin.last rows), (fun r => solved.val r.castSucc), ?_, ?_, ?_⟩
  · intro r
    have negative := (le_congr (sign_evaluation matrix bounds gradient target r solved.val)
      (sign_bound matrix bounds gradient target r)).mp (holds (DualSignature.signConstraint r) (sign_member r))
    exact (le_congr (equiv_refl _) (zero_add _)).mp ((neg_le_iff_nonnegative_add _ zero).mp negative)
  · intro i
    exact equiv_trans (equiv_symm (column_bound matrix bounds gradient target i))
      (equiv_trans (equiv_symm (equality (DualSignature.columnConstraint i) (fun _ => rfl) (column_member i) (reverse_column_member i)))
        (column_evaluation matrix bounds gradient target i solved.val))
  · exact equiv_trans (equiv_symm (value_evaluation matrix bounds gradient target solved.val))
      (equiv_trans (equality DualSignature.valueConstraint (fun _ => rfl) value_member reverse_value_member)
        (value_bound matrix bounds gradient target))

end Thesis.Probability.AnalyticLinear
