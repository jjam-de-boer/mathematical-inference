import Thesis.Probability.Distros.StepRising
namespace Thesis.Probability.Distros
open Combinatorics

/-- A draw returns the selected ball and adds `increment` balls of that
colour. Zero increment is independent sampling from a fixed urn. -/
def reinforcedUrnAtoms : Nat → List Nat → Nat → List (List Nat × Nat)
  | 0, _, _ => [([], 1)]
  | n + 1, alphas, increment => (finWeighted alphas.length (fun i => alphas.getD i.val 0)).flatMap fun head =>
      (reinforcedUrnAtoms n (alphas.modify head.1.val (fun a => a + increment)) increment).map
        (fun rest => (head.1.val :: rest.1, head.2 * rest.2))

theorem reinforcedUrnAtoms_word_weights (n : Nat) (alphas : List Nat) (increment : Nat) :
    reinforcedUrnAtoms n alphas increment = (unitWordAtoms alphas.length n).map
      (fun atom => (atom.1, atom.2 * stepKernel increment alphas (colourCounts alphas.length atom.1))) := by
  induction n generalizing alphas with
  | zero => simp only [reinforcedUrnAtoms, unitWordAtoms, List.map_cons, List.map_nil,
      colourCounts, stepKernel_zeros, Nat.mul_one]
  | succ n ih =>
      rw [reinforcedUrnAtoms, finWeighted_reweight, List.flatMap_map]
      simp only [unitWordAtoms, List.map_flatMap]
      apply congrArg (fun f => (finWeighted alphas.length (fun _ => 1)).flatMap f)
      funext head
      rw [ih, List.length_modify]
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro rest _
      simp only [colourCounts]
      rw [stepKernel_increment increment alphas _ (colourCounts_length _ _).symm head.1.val head.1.isLt]
      ac_rfl

theorem totalMass_reinforcedUrnAtoms (n : Nat) (alphas : List Nat) (increment : Nat) :
    FiniteProbRecord.totalMass (reinforcedUrnAtoms n alphas increment) = stepRising alphas.sum increment n := by
  induction n generalizing alphas with
  | zero => rfl
  | succ n ih =>
      rw [reinforcedUrnAtoms, totalMass_flatMap]
      have row (head : Fin alphas.length × Nat) :
          FiniteProbRecord.totalMass
            ((reinforcedUrnAtoms n (alphas.modify head.1.val (fun a => a + increment)) increment).map
              (fun rest => (head.1.val :: rest.1, head.2 * rest.2))) =
          head.2 * stepRising (alphas.sum + increment) increment n := by
        rw [FiniteProbRecord.totalMass_map_weight, ih, sum_modify_add alphas head.1.val increment head.1.isLt]
      rw [List.map_congr_left (fun head _ => row head)]
      rw [← natIntegral_eq_sum (finWeighted alphas.length (fun i => alphas.getD i.val 0))
        (fun _ => stepRising (alphas.sum + increment) increment n)]
      rw [natIntegral_constant, totalMass_finWeighted, finWeight_getD_sum, stepRising]

def reinforcedUrnDistro (n : Nat) (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum) : Distro (List Nat) :=
  ofWeightedAtoms (reinforcedUrnAtoms n alphas increment) (by
    rw [totalMass_reinforcedUrnAtoms]; exact stepRising_pos _ _ _ positive)

theorem reinforcedUrn_den (n : Nat) (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum) :
    (reinforcedUrnDistro n alphas increment positive).record.den = stepRising alphas.sum increment n :=
  totalMass_reinforcedUrnAtoms n alphas increment

/-- Raw uniform-word counting and occupancy coefficients have exactly the
same integral, because their categorical laws share the same denominator. -/
theorem unitOccupancy_integral (n colours : Nat) (f : List Nat → Nat) (positive : 0 < colours) :
    natIntegral (multinomialAtoms n (List.replicate colours 1)) f =
      natIntegral (unitWordAtoms colours n) (fun word => f (colourCounts colours word)) := by
  let ones := List.replicate colours 1
  have onePositive : 0 < ones.sum := by simpa only [ones, List.sum_replicate_nat, Nat.mul_one] using positive
  have same := (multinomial_categorical_correspondence n ones onePositive).expectNat f
  rw [categoricalOccupancyDistro, Distro.expectNat_map] at same
  change natIntegral (categoricalWordDistro ones onePositive n).record.atoms
      (fun word => f (colourCounts ones.length word)) * (multinomialDistro n ones onePositive).record.den =
    natIntegral (multinomialAtoms n ones) f * (categoricalWordDistro ones onePositive n).record.den at same
  have den : (multinomialDistro n ones onePositive).record.den = (categoricalWordDistro ones onePositive n).record.den := by
    rw [multinomial_den, categoricalWord_den]
  rw [den] at same
  have raw := Nat.eq_of_mul_eq_mul_right (categoricalWordDistro ones onePositive n).record.den_pos same
  change natIntegral (multinomialAtoms n ones) f = _
  rw [← raw]
  rw [unitWordAtoms_categorical colours n positive]
  simp only [ones, List.length_replicate]

def reinforcedCountAtoms (n : Nat) (alphas : List Nat) (increment : Nat) : List (List Nat × Nat) :=
  (multinomialAtoms n (List.replicate alphas.length 1)).map
    (fun atom => (atom.1, atom.2 * stepKernel increment alphas atom.1))

theorem totalMass_reinforcedCountAtoms (n : Nat) (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum) :
    FiniteProbRecord.totalMass (reinforcedCountAtoms n alphas increment) = stepRising alphas.sum increment n := by
  rw [reinforcedCountAtoms, totalMass_reweight, unitOccupancy_integral n alphas.length _
    (list_length_positive_of_sum alphas positive), ← totalMass_reweight, ← reinforcedUrnAtoms_word_weights,
    totalMass_reinforcedUrnAtoms]

def reinforcedCountDistro (n : Nat) (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum) : Distro (List Nat) :=
  ofWeightedAtoms (reinforcedCountAtoms n alphas increment) (by
    rw [totalMass_reinforcedCountAtoms n alphas increment positive]; exact stepRising_pos _ _ _ positive)

theorem reinforcedCount_den (n : Nat) (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum) :
    (reinforcedCountDistro n alphas increment positive).record.den = stepRising alphas.sum increment n :=
  totalMass_reinforcedCountAtoms n alphas increment positive

/-- The occupancy law of the actual sequential urn, for every increment. -/
theorem reinforcedUrn_count_correspondence (n : Nat) (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum) :
    ((reinforcedUrnDistro n alphas increment positive).map (colourCounts alphas.length)).SameLaw
      (reinforcedCountDistro n alphas increment positive) := by
  intro event
  change FiniteProbRecord.eventMass
      ((reinforcedUrnAtoms n alphas increment).map (fun atom => (colourCounts alphas.length atom.1, atom.2))) event *
      (reinforcedCountDistro n alphas increment positive).record.den =
    FiniteProbRecord.eventMass (reinforcedCountAtoms n alphas increment) event *
      (reinforcedUrnDistro n alphas increment positive).record.den
  rw [reinforcedCount_den, reinforcedUrn_den,
    FiniteProbRecord.eventMass_map_labels _ (colourCounts alphas.length) event,
    reinforcedUrnAtoms_word_weights, reinforcedCountAtoms,
    eventMass_reweight (unitWordAtoms alphas.length n)
      (fun word => stepKernel increment alphas (colourCounts alphas.length word))
      (fun word => event (colourCounts alphas.length word)), eventMass_reweight,
    unitOccupancy_integral n alphas.length _ (list_length_positive_of_sum alphas positive)]

theorem Distro.eq_of_atoms {μ ν : Distro Ω} (same : μ.record.atoms = ν.record.atoms) : μ = ν := by
  apply Distro.eq_of_atoms_den same
  rw [← μ.record.total_mass, ← ν.record.total_mass, same]

theorem reinforcedUrn_one (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    reinforcedUrnDistro n alphas 1 positive = multicolourPolyaDistro n alphas positive := by
  apply Distro.eq_of_atoms
  change reinforcedUrnAtoms n alphas 1 = multicolourPolyaAtoms n alphas
  rw [reinforcedUrnAtoms_word_weights, multicolourPolyaAtoms_word_weights]
  apply List.map_congr_left
  intro atom _
  rw [stepKernel_one]

theorem reinforcedCount_one (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    reinforcedCountDistro n alphas 1 positive = dirichletMultinomialDistro n alphas positive := by
  apply Distro.eq_of_atoms
  change reinforcedCountAtoms n alphas 1 = dirichletMultinomialAtoms n alphas
  simp only [reinforcedCountAtoms, dirichletMultinomialAtoms]
  apply List.map_congr_left
  intro atom _
  rw [stepKernel_one]

theorem modify_add_zero (values : List Nat) (index : Nat) : values.modify index (fun x => x + 0) = values := by
  induction values generalizing index with
  | nil => exact List.modify_nil _ _
  | cons value values ih =>
      cases index with
      | zero => simp only [List.modify_zero_cons, Nat.add_zero]
      | succ index => rw [List.modify_succ_cons, ih]

theorem reinforcedUrn_zero (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    reinforcedUrnDistro n alphas 0 positive = categoricalWordDistro alphas positive n := by
  apply Distro.eq_of_atoms
  change reinforcedUrnAtoms n alphas 0 = (categoricalWordDistro alphas positive n).record.atoms
  induction n with
  | zero => rfl
  | succ n ih =>
      change reinforcedUrnAtoms (n + 1) alphas 0 =
        (FiniteProbRecord.weightedCartesian (listCategoricalDistro alphas positive).record.atoms
          (categoricalWordDistro alphas positive n).record.atoms).map
            (fun source => (source.1.1.val :: source.1.2, source.2))
      simp only [reinforcedUrnAtoms, modify_add_zero, ih, FiniteProbRecord.weightedCartesian,
        List.map_flatMap, List.map_map, Function.comp_def]
      rfl

/-- With no reinforcement, occupancy is the ordinary multinomial law. -/
theorem reinforcedCount_zero (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    (reinforcedCountDistro n alphas 0 positive).SameLaw (multinomialDistro n alphas positive) := by
  have same := reinforcedUrn_count_correspondence n alphas 0 positive
  rw [reinforcedUrn_zero] at same
  exact same.symm.trans (multinomial_categorical_correspondence n alphas positive)

/-- Categorical selection followed by the selected reinforced continuation. -/
theorem reinforcedUrn_first_step (n : Nat) (alphas : List Nat) (increment : Nat) (positive : 0 < alphas.sum)
    (event : Event (List Nat)) :
    QProb.Equiv ((reinforcedUrnDistro (n + 1) alphas increment positive).record.probVal event)
      ((listCategoricalDistro alphas positive).expectation (fun colour =>
        (reinforcedUrnDistro n (alphas.modify colour.val (fun a => a + increment)) increment
          (by rw [sum_modify_add alphas colour.val increment colour.isLt]; omega)).record.probVal
            (fun word => event (colour.val :: word)))) := by
  let T := stepRising (alphas.sum + increment) increment n
  have hT : 0 < T := stepRising_pos _ _ _ (by omega)
  let mass (colour : Fin alphas.length) := FiniteProbRecord.eventMass
    (reinforcedUrnAtoms n (alphas.modify colour.val (fun a => a + increment)) increment)
      (fun word => event (colour.val :: word))
  have normalized (colour : Fin alphas.length) :
      QProb.Equiv ((reinforcedUrnDistro n (alphas.modify colour.val (fun a => a + increment)) increment
        (by rw [sum_modify_add alphas colour.val increment colour.isLt]; omega)).record.probVal
          (fun word => event (colour.val :: word))) (⟨mass colour, T, hT⟩ : QProb) := by
    change mass colour * T = mass colour * FiniteProbRecord.totalMass
      (reinforcedUrnAtoms n (alphas.modify colour.val (fun a => a + increment)) increment)
    rw [totalMass_reinforcedUrnAtoms, sum_modify_add alphas colour.val increment colour.isLt]
  have massEq : FiniteProbRecord.eventMass (reinforcedUrnAtoms (n + 1) alphas increment) event =
      natIntegral (listCategoricalDistro alphas positive).record.atoms mass := by
    rw [reinforcedUrnAtoms, eventMass_flatMap]
    have rows : ((finWeighted alphas.length (fun i => alphas.getD i.val 0)).map
        (fun head => FiniteProbRecord.eventMass
          ((reinforcedUrnAtoms n (alphas.modify head.1.val (fun a => a + increment)) increment).map
            (fun rest => (head.1.val :: rest.1, head.2 * rest.2))) event)) =
      (finWeighted alphas.length (fun i => alphas.getD i.val 0)).map (fun head => head.2 * mass head.1) := by
      apply List.map_congr_left
      intro head _
      exact FiniteProbRecord.eventMass_map_weight _ (fun word => head.1.val :: word) head.2 event
    rw [rows, ← natIntegral_eq_sum]
    rfl
  refine QProb.equiv_trans ?_ (QProb.equiv_symm
    ((listCategoricalDistro alphas positive).expectation_congr _ _ normalized))
  change QProb.Equiv ((reinforcedUrnDistro (n + 1) alphas increment positive).record.probVal event)
    (QProb.div (rationalIntegral (listCategoricalDistro alphas positive).record.atoms
      (fun colour => (⟨mass colour, T, hT⟩ : QProb)))
      (QProb.ofNat (listCategoricalDistro alphas positive).record.den) _)
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (QProb.div_congr
    (rationalIntegral_commonDen _ mass T hT) (QProb.equiv_refl _)
      (listCategoricalDistro alphas positive).record.den_pos (listCategoricalDistro alphas positive).record.den_pos))
  change FiniteProbRecord.eventMass (reinforcedUrnAtoms (n + 1) alphas increment) event *
    (T * (listCategoricalDistro alphas positive).record.den) =
    (natIntegral (listCategoricalDistro alphas positive).record.atoms mass * 1) *
      (reinforcedUrnDistro (n + 1) alphas increment positive).record.den
  rw [massEq, listCategorical_den, reinforcedUrn_den, stepRising, Nat.mul_one]
  dsimp only [T]
  ac_rfl


theorem reinforcedCount_support (n : Nat) (alphas : List Nat) (increment : Nat) (atom : List Nat × Nat)
    (member : atom ∈ reinforcedCountAtoms n alphas increment) :
    atom.1.length = alphas.length ∧ atom.1.sum = n := by
  rcases List.mem_map.mp member with ⟨source, hs, eq⟩
  cases eq
  have support := multinomialAtoms_support n (List.replicate alphas.length 1) source hs
  exact ⟨support.1.trans List.length_replicate, support.2⟩

theorem reinforcedCount_pmf (n : Nat) (alphas counts : List Nat) (increment : Nat) (positive : 0 < alphas.sum) :
    QProb.Equiv ((reinforcedCountDistro n alphas increment positive).pmf counts)
      ⟨if counts.sum = n then multinomialWeight (List.replicate alphas.length 1) counts * stepKernel increment alphas counts else 0,
        stepRising alphas.sum increment n, stepRising_pos _ _ _ positive⟩ := by
  change FiniteProbRecord.eventMass (reinforcedCountAtoms n alphas increment)
    (FiniteProbRecord.singletonEvent counts) * stepRising alphas.sum increment n =
    _ * (reinforcedCountDistro n alphas increment positive).record.den
  rw [reinforcedCountAtoms, eventMass_reweight_singleton, eventMass_multinomialAtoms, reinforcedCount_den]
  by_cases eq : counts.sum = n
  · simp only [eq, if_true]
  · simp only [eq, if_false, Nat.zero_mul]

theorem natList_sum_map_scale (c : Nat) (values : List Nat) :
    (values.map (fun a => c * a)).sum = c * values.sum := by
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.mul_zero]
  | cons value values ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem unitWordAtoms_count_sum (n colours : Nat) (positive : 0 < colours) (atom : List Nat × Nat)
    (member : atom ∈ unitWordAtoms colours n) : (colourCounts colours atom.1).sum = n := by
  rw [unitWordAtoms_categorical colours n positive] at member
  have support := categoricalWord_counts_support (List.replicate colours 1)
    (by simpa only [List.sum_replicate_nat, Nat.mul_one] using positive) n atom member
  simpa only [List.length_replicate] using support

theorem reinforcedUrnAtoms_scale (n : Nat) (alphas : List Nat) (increment c : Nat) (positive : 0 < alphas.sum) :
    reinforcedUrnAtoms n (alphas.map (fun a => c * a)) (c * increment) =
      (reinforcedUrnAtoms n alphas increment).map (fun atom => (atom.1, c ^ n * atom.2)) := by
  rw [reinforcedUrnAtoms_word_weights, reinforcedUrnAtoms_word_weights]
  simp only [List.length_map, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro atom member
  rw [stepKernel_scale, unitWordAtoms_count_sum n alphas.length (list_length_positive_of_sum alphas positive) atom member]
  ac_rfl

/-- Scaling initial ball counts and reinforcement together leaves the law unchanged. -/
theorem reinforcedUrn_scale_sameLaw (n : Nat) (alphas : List Nat) (increment c : Nat)
    (positive : 0 < alphas.sum) (hc : 0 < c) :
    (reinforcedUrnDistro n (alphas.map (fun a => c * a)) (c * increment)
      (by rw [natList_sum_map_scale]; exact Nat.mul_pos hc positive)).SameLaw
      (reinforcedUrnDistro n alphas increment positive) := by
  have eq : reinforcedUrnDistro n (alphas.map (fun a => c * a)) (c * increment)
      (by rw [natList_sum_map_scale]; exact Nat.mul_pos hc positive) =
      (reinforcedUrnDistro n alphas increment positive).rescaleWeights (c ^ n) (Nat.pow_pos hc) := by
    apply Distro.eq_of_atoms
    exact reinforcedUrnAtoms_scale n alphas increment c positive
  rw [eq]
  exact Distro.rescaleWeights_sameLaw _ _ _

theorem reinforcedCount_scale_sameLaw (n : Nat) (alphas : List Nat) (increment c : Nat)
    (positive : 0 < alphas.sum) (hc : 0 < c) :
    (reinforcedCountDistro n (alphas.map (fun a => c * a)) (c * increment)
      (by rw [natList_sum_map_scale]; exact Nat.mul_pos hc positive)).SameLaw
      (reinforcedCountDistro n alphas increment positive) := by
  have eq : reinforcedCountDistro n (alphas.map (fun a => c * a)) (c * increment)
      (by rw [natList_sum_map_scale]; exact Nat.mul_pos hc positive) =
      (reinforcedCountDistro n alphas increment positive).rescaleWeights (c ^ n) (Nat.pow_pos hc) := by
    apply Distro.eq_of_atoms
    change reinforcedCountAtoms n (alphas.map (fun a => c * a)) (c * increment) =
      (reinforcedCountAtoms n alphas increment).map (fun atom => (atom.1, c ^ n * atom.2))
    simp only [reinforcedCountAtoms, List.length_map, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro atom member
    rw [stepKernel_scale, (multinomialAtoms_support n (List.replicate alphas.length 1) atom member).2]
    ac_rfl
  rw [eq]
  exact Distro.rescaleWeights_sameLaw _ _ _

end Thesis.Probability.Distros
