import Thesis.Probability.Distros.ReinforcedUrn
namespace Thesis.Probability.Distros

/-- Clear a common denominator from all rational urn parameters. -/
def rationalUrnWeights : List QProb → List Nat
  | [] => []
  | alpha :: alphas => (alpha.num * (QProb.listSum alphas).den) ::
      (rationalUrnWeights alphas).map (fun a => alpha.den * a)

theorem rationalUrnWeights_length (alphas : List QProb) : (rationalUrnWeights alphas).length = alphas.length := by
  induction alphas with
  | nil => rfl
  | cons alpha alphas ih => simp only [rationalUrnWeights, List.length_cons, List.length_map, ih]

theorem rationalUrnWeights_sum (alphas : List QProb) :
    (rationalUrnWeights alphas).sum = (QProb.listSum alphas).num := by
  induction alphas with
  | nil => rfl
  | cons alpha alphas ih =>
      simp only [rationalUrnWeights, List.sum_cons, natList_sum_map_scale, ih, QProb.listSum, QProb.add]
      ac_rfl

theorem getD_map_scale (values : List Nat) (c index : Nat) :
    (values.map (fun a => c * a)).getD index 0 = c * values.getD index 0 := by
  induction values generalizing index with
  | nil => simp only [List.map_nil, List.getD_nil, Nat.mul_zero]
  | cons value values ih =>
      cases index with
      | zero => simp only [List.map_cons, List.getD_cons_zero]
      | succ index => simp only [List.map_cons, List.getD_cons_succ, ih]

/-- Every encoded count represents precisely its original rational parameter. -/
theorem rationalUrnWeights_parameter (alphas : List QProb) (index : Nat) :
    QProb.Equiv (⟨(rationalUrnWeights alphas).getD index 0, (QProb.listSum alphas).den,
      (QProb.listSum alphas).den_pos⟩ : QProb) (alphas.getD index QProb.zero) := by
  induction alphas generalizing index with
  | nil => simp only [rationalUrnWeights, List.getD_nil, QProb.Equiv, QProb.zero, Nat.zero_mul]
  | cons alpha alphas ih =>
      cases index with
      | zero =>
          simp only [rationalUrnWeights, List.getD_cons_zero, QProb.listSum, QProb.add, QProb.Equiv]
          ac_rfl
      | succ index =>
          simp only [rationalUrnWeights, List.getD_cons_succ, getD_map_scale, QProb.listSum, QProb.add, QProb.Equiv]
          calc
            _ = alpha.den * ((rationalUrnWeights alphas).getD index 0 * (alphas.getD index QProb.zero).den) := by ac_rfl
            _ = _ := by rw [ih index]; ac_rfl

/-- Actual Pólya paths with arbitrary nonnegative rational parameters and
unit reinforcement in parameter units. Integer counts add their common denominator. -/
def rationalPolyaDistro (n : Nat) (alphas : List QProb) (positive : 0 < (QProb.listSum alphas).num) : Distro (List Nat) :=
  reinforcedUrnDistro n (rationalUrnWeights alphas) (QProb.listSum alphas).den
    (by rw [rationalUrnWeights_sum]; exact positive)

def rationalDirichletMultinomialDistro (n : Nat) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num) : Distro (List Nat) :=
  reinforcedCountDistro n (rationalUrnWeights alphas) (QProb.listSum alphas).den
    (by rw [rationalUrnWeights_sum]; exact positive)

theorem rationalPolya_count_correspondence (n : Nat) (alphas : List QProb)
    (positive : 0 < (QProb.listSum alphas).num) :
    ((rationalPolyaDistro n alphas positive).map (colourCounts alphas.length)).SameLaw
      (rationalDirichletMultinomialDistro n alphas positive) := by
  simpa only [rationalUrnWeights_length] using reinforcedUrn_count_correspondence n (rationalUrnWeights alphas)
    (QProb.listSum alphas).den (by rw [rationalUrnWeights_sum]; exact positive)

/-- Pointwise rational equivalence on lists of the same dimension. -/
def RationalParametersEquiv (alphas betas : List QProb) : Prop :=
  alphas.length = betas.length ∧ ∀ i, QProb.Equiv (alphas.getD i QProb.zero) (betas.getD i QProb.zero)

theorem scaledLists_eq_of_cross (alphas betas : List Nat) (c d : Nat) (dimension : alphas.length = betas.length)
    (cross : ∀ i, c * alphas.getD i 0 = d * betas.getD i 0) :
    alphas.map (fun a => c * a) = betas.map (fun a => d * a) := by
  induction alphas generalizing betas with
  | nil => cases betas with
      | nil => rfl
      | cons beta betas => simp only [List.length_nil, List.length_cons] at dimension; omega
  | cons alpha alphas ih => cases betas with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons beta betas =>
          have head : c * alpha = d * beta := by simpa only [List.getD_cons_zero] using cross 0
          simp only [List.map_cons, head]
          rw [ih betas (Nat.succ.inj dimension) (fun i => by simpa only [List.getD_cons_succ] using cross (i + 1))]

theorem rationalUrnWeights_cross {alphas betas : List QProb} (same : RationalParametersEquiv alphas betas) :
    (rationalUrnWeights alphas).map (fun a => (QProb.listSum betas).den * a) =
      (rationalUrnWeights betas).map (fun a => (QProb.listSum alphas).den * a) := by
  apply scaledLists_eq_of_cross
  · rw [rationalUrnWeights_length, rationalUrnWeights_length]
    exact same.1
  · intro i
    have h := QProb.equiv_trans (rationalUrnWeights_parameter alphas i)
      (QProb.equiv_trans (same.2 i) (QProb.equiv_symm (rationalUrnWeights_parameter betas i)))
    change (rationalUrnWeights alphas).getD i 0 * (QProb.listSum betas).den =
      (rationalUrnWeights betas).getD i 0 * (QProb.listSum alphas).den at h
    simpa only [Nat.mul_comm] using h

/-- Equivalent presentations of each rational parameter give the same
actual ordered reinforced-urn law. -/
theorem rationalPolya_sameLaw_parameters (n : Nat) (alphas betas : List QProb)
    (ha : 0 < (QProb.listSum alphas).num) (hb : 0 < (QProb.listSum betas).num)
    (same : RationalParametersEquiv alphas betas) :
    (rationalPolyaDistro n alphas ha).SameLaw (rationalPolyaDistro n betas hb) := by
  have left := reinforcedUrn_scale_sameLaw n (rationalUrnWeights alphas) (QProb.listSum alphas).den
    (QProb.listSum betas).den (by rw [rationalUrnWeights_sum]; exact ha) (QProb.listSum betas).den_pos
  have right := reinforcedUrn_scale_sameLaw n (rationalUrnWeights betas) (QProb.listSum betas).den
    (QProb.listSum alphas).den (by rw [rationalUrnWeights_sum]; exact hb) (QProb.listSum alphas).den_pos
  simp only [rationalUrnWeights_cross same, Nat.mul_comm (QProb.listSum betas).den (QProb.listSum alphas).den] at left
  exact left.symm.trans right

theorem rationalDirichletMultinomial_sameLaw_parameters (n : Nat) (alphas betas : List QProb)
    (ha : 0 < (QProb.listSum alphas).num) (hb : 0 < (QProb.listSum betas).num)
    (same : RationalParametersEquiv alphas betas) :
    (rationalDirichletMultinomialDistro n alphas ha).SameLaw (rationalDirichletMultinomialDistro n betas hb) := by
  have left := reinforcedCount_scale_sameLaw n (rationalUrnWeights alphas) (QProb.listSum alphas).den
    (QProb.listSum betas).den (by rw [rationalUrnWeights_sum]; exact ha) (QProb.listSum betas).den_pos
  have right := reinforcedCount_scale_sameLaw n (rationalUrnWeights betas) (QProb.listSum betas).den
    (QProb.listSum alphas).den (by rw [rationalUrnWeights_sum]; exact hb) (QProb.listSum alphas).den_pos
  simp only [rationalUrnWeights_cross same, Nat.mul_comm (QProb.listSum betas).den (QProb.listSum alphas).den] at left
  exact left.symm.trans right

theorem rationalUrnWeights_ofNat (alphas : List Nat) :
    (QProb.listSum (alphas.map QProb.ofNat)).den = 1 ∧ rationalUrnWeights (alphas.map QProb.ofNat) = alphas := by
  induction alphas with
  | nil => exact ⟨rfl, rfl⟩
  | cons alpha alphas ih =>
      constructor
      · simp only [List.map_cons, QProb.listSum, QProb.add, QProb.ofNat, ih.1, Nat.mul_one]
      · simp only [List.map_cons, rationalUrnWeights, QProb.ofNat, ih.1, ih.2, Nat.mul_one, Nat.one_mul]
        change alpha :: alphas.map id = alpha :: alphas
        rw [List.map_id]

theorem rationalPolya_ofNat (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    rationalPolyaDistro n (alphas.map QProb.ofNat)
      (by rw [← rationalUrnWeights_sum, (rationalUrnWeights_ofNat alphas).2]; exact positive) =
      multicolourPolyaDistro n alphas positive := by
  unfold rationalPolyaDistro
  simp only [(rationalUrnWeights_ofNat alphas).1, (rationalUrnWeights_ofNat alphas).2]
  exact reinforcedUrn_one n alphas positive

theorem rationalDirichletMultinomial_ofNat (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    rationalDirichletMultinomialDistro n (alphas.map QProb.ofNat)
      (by rw [← rationalUrnWeights_sum, (rationalUrnWeights_ofNat alphas).2]; exact positive) =
      dirichletMultinomialDistro n alphas positive := by
  unfold rationalDirichletMultinomialDistro
  simp only [(rationalUrnWeights_ofNat alphas).1, (rationalUrnWeights_ofNat alphas).2]
  exact reinforcedCount_one n alphas positive

end Thesis.Probability.Distros
