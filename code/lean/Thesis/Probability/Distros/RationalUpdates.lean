import Thesis.Probability.Distros.RationalAggregation
import Thesis.Probability.Distros.ReinforcedUpdates

/-!
Supported rational-parameter updating from actual count observations.

The public update adds each observed count to its rational parameter.
Integer-encoding lemmas relate this to reinforced-state updates, so the
conclusion follows from conditioning the original finite sequential path
law. `rationalCountsSupported` retains a positive-evidence requirement;
no posterior continuation is assigned to an impossible histogram. The
main theorem identifies the entire future word law with parameters
alpha + counts, and its pushforward gives the future count-vector law.
-/

namespace Thesis.Probability.Distros

/-- Sufficient-count update in rational parameter units: `alpha_i + count_i`. -/
def updateRationalParameters : List QProb → List Nat → List QProb
  | [], _ => []
  | alphas, [] => alphas
  | alpha :: alphas, count :: counts => QProb.add alpha (QProb.ofNat count) :: updateRationalParameters alphas counts

theorem updateRationalParameters_length (alphas : List QProb) (counts : List Nat) :
    (updateRationalParameters alphas counts).length = alphas.length := by
  induction alphas generalizing counts with
  | nil => rfl
  | cons alpha alphas ih => cases counts <;> simp only [updateRationalParameters, List.length_cons, ih]

theorem updateRationalParameters_congr {alphas betas : List QProb}
    (same : RationalParametersEquiv alphas betas) (counts : List Nat) :
    RationalParametersEquiv (updateRationalParameters alphas counts) (updateRationalParameters betas counts) := by
  induction alphas generalizing betas counts with
  | nil => cases betas with
      | nil => exact .refl []
      | cons beta betas => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; exact False.elim (by omega)
  | cons alpha alphas ih => cases betas with
      | nil => have dim := same.1; simp only [List.length_nil, List.length_cons] at dim; exact False.elim (by omega)
      | cons beta betas => cases counts with
          | nil => exact same
          | cons count counts =>
              exact .cons (QProb.add_congr (same.2 0) (QProb.equiv_refl _))
                (ih ⟨Nat.succ.inj same.1, fun i => same.2 (i + 1)⟩ counts)

/-- Adding denominator times a count to an integer weight is equivalent
to adding that count after dividing back into rational parameter units. -/
theorem updateRationalParameters_ratios (weights counts : List Nat) (denominator : Nat) (positive : 0 < denominator) :
    RationalParametersEquiv
      (urnRatioParameters (reinforcedState denominator weights counts) denominator positive)
      (updateRationalParameters (urnRatioParameters weights denominator positive) counts) := by
  induction weights generalizing counts with
  | nil => exact .refl []
  | cons weight weights ih => cases counts with
      | nil => exact .refl _
      | cons count counts =>
          apply RationalParametersEquiv.cons ?_ (ih counts)
          simp only [QProb.Equiv, QProb.add, QProb.ofNat, Nat.mul_one, Nat.add_mul]
          ac_rfl

/-- Encoding and count updating commute up to rational parameter
equivalence, even when the original fractions have different presentations. -/
theorem updateRationalParameters_encoding (alphas : List QProb) (counts : List Nat) :
    RationalParametersEquiv
      (urnRatioParameters (reinforcedState (QProb.listSum alphas).den (rationalUrnWeights alphas) counts)
        (QProb.listSum alphas).den (QProb.listSum alphas).den_pos)
      (updateRationalParameters alphas counts) :=
  (updateRationalParameters_ratios _ counts _ _).trans
    (updateRationalParameters_congr (rationalParameters_encoding alphas) counts)

/-- The updated total remains positive for a matching count vector.
The proof transfers positivity from the integer reinforced state. -/
theorem updateRationalParameters_positive (alphas : List QProb) (counts : List Nat)
    (positive : 0 < (QProb.listSum alphas).num) (dimension : counts.length = alphas.length) :
    0 < (QProb.listSum (updateRationalParameters alphas counts)).num := by
  apply (updateRationalParameters_encoding alphas counts).positive
  apply urnRatioParameters_positive
  rw [reinforcedState_sum _ _ _ (by rw [rationalUrnWeights_length]; exact dimension), rationalUrnWeights_sum]
  omega

/-- Positive probability of the actual observed count vector, including
zero-weight colours rather than assuming every possible vector is supported. -/
def rationalCountsSupported (m : Nat) (alphas : List QProb) (counts : List Nat) : Prop :=
  reinforcedCountsSupported m (rationalUrnWeights alphas) (QProb.listSum alphas).den counts

instance (m : Nat) (alphas : List QProb) (counts : List Nat) :
    Decidable (rationalCountsSupported m alphas counts) :=
  inferInstanceAs (Decidable (reinforcedCountsSupported m (rationalUrnWeights alphas) (QProb.listSum alphas).den counts))

/-- Supported observations have the declared dimension and total, so the
conditional interface can recover those shape facts from support alone. -/
theorem rationalCountsSupported_shape (m : Nat) (alphas : List QProb) (counts : List Nat)
    (supported : rationalCountsSupported m alphas counts) : counts.length = alphas.length ∧ counts.sum = m := by
  have shape := reinforcedCountsSupported_shape m (rationalUrnWeights alphas) counts (QProb.listSum alphas).den supported
  simpa only [rationalUrnWeights_length] using shape

/-- Condition the rational path law on prefix counts and retain its future. -/
def rationalCountsContinuation (m n : Nat) (alphas : List QProb) (counts : List Nat)
    (positive : 0 < (QProb.listSum alphas).num) (supported : rationalCountsSupported m alphas counts) : Distro (List Nat) :=
  reinforcedCountsContinuation m n (rationalUrnWeights alphas) counts (QProb.listSum alphas).den
    (by rw [rationalUrnWeights_sum]; exact positive)
    (by rw [rationalUrnWeights_length]; exact (rationalCountsSupported_shape m alphas counts supported).1) supported

/-- Actual conditioning gives the full future path law with parameters
`alpha + counts`, independently of their original common denominator. -/
theorem rationalCountsContinuation_updated (m n : Nat) (alphas : List QProb) (counts : List Nat)
    (positive : 0 < (QProb.listSum alphas).num) (supported : rationalCountsSupported m alphas counts) :
    (rationalCountsContinuation m n alphas counts positive supported).SameLaw
      (rationalPolyaDistro n (updateRationalParameters alphas counts)
        (updateRationalParameters_positive alphas counts positive (rationalCountsSupported_shape m alphas counts supported).1)) := by
  have dimension : counts.length = (rationalUrnWeights alphas).length := by
    rw [rationalUrnWeights_length]; exact (rationalCountsSupported_shape m alphas counts supported).1
  have weightsPositive : 0 < (rationalUrnWeights alphas).sum := by rw [rationalUrnWeights_sum]; exact positive
  have updatedPositive : 0 < (reinforcedState (QProb.listSum alphas).den (rationalUrnWeights alphas) counts).sum := by
    rw [reinforcedState_sum _ _ _ dimension]; omega
  have conditioned := reinforcedCountsContinuation_updated m n (rationalUrnWeights alphas) counts
    (QProb.listSum alphas).den weightsPositive dimension supported
  exact conditioned.trans ((reinforcedUrn_rationalParameters n _ _ updatedPositive (QProb.listSum alphas).den_pos).trans
    (rationalPolya_sameLaw_parameters n _ _ _ _ (updateRationalParameters_encoding alphas counts)))

/-- The count-vector posterior uses the same sufficient-count update. -/
theorem rationalCountsContinuation_count_updated (m n : Nat) (alphas : List QProb) (counts : List Nat)
    (positive : 0 < (QProb.listSum alphas).num) (supported : rationalCountsSupported m alphas counts) :
    ((rationalCountsContinuation m n alphas counts positive supported).map (colourCounts alphas.length)).SameLaw
      (rationalDirichletMultinomialDistro n (updateRationalParameters alphas counts)
        (updateRationalParameters_positive alphas counts positive (rationalCountsSupported_shape m alphas counts supported).1)) := by
  have paths := (rationalCountsContinuation_updated m n alphas counts positive supported).map (colourCounts alphas.length)
  have correspondence := rationalPolya_count_correspondence n (updateRationalParameters alphas counts)
    (updateRationalParameters_positive alphas counts positive (rationalCountsSupported_shape m alphas counts supported).1)
  rw [updateRationalParameters_length] at correspondence
  exact paths.trans correspondence

end Thesis.Probability.Distros
