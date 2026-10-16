import Thesis.Probability.Distros.CategoricalProduct
import Thesis.Probability.Distros.FactorialMoments
import Thesis.Probability.Distros.Reweight
import Thesis.Probability.Distros.Degenerate

namespace Thesis.Probability.Distros
open Combinatorics

/-! Sequential finite multicolour reinforcement and its Dirichlet-multinomial
occupancy law. The total parameter is positive; individual colours may have
weight zero. All parameters and atom weights are natural numbers. -/

/-- Product of the rising-factorial factors of a count vector. -/
def risingKernel : List Nat → List Nat → Nat
  | [], [] => 1
  | alpha :: alphas, count :: counts => risingFactorial alpha count * risingKernel alphas counts
  | _, _ => 0

theorem risingKernel_zeros (alphas : List Nat) : risingKernel alphas (List.replicate alphas.length 0) = 1 := by
  induction alphas with
  | nil => rfl
  | cons alpha alphas ih => simp only [List.length_cons, List.replicate_succ, risingKernel, risingFactorial, Nat.one_mul, ih]

theorem risingKernel_increment (alphas counts : List Nat) (dimension : alphas.length = counts.length)
    (index : Nat) (within : index < alphas.length) :
    risingKernel alphas (counts.modify index (fun c => c + 1)) =
      alphas.getD index 0 * risingKernel (alphas.modify index (fun a => a + 1)) counts := by
  induction alphas generalizing counts index with
  | nil => simp only [List.length_nil] at within; omega
  | cons alpha alphas ih =>
      cases counts with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons count counts =>
          cases index with
          | zero =>
              simp only [List.modify_zero_cons, List.getD_cons_zero, risingKernel, risingFactorial_head]
              ac_rfl
          | succ index =>
              simp only [List.modify_succ_cons, List.getD_cons_succ, risingKernel]
              rw [ih counts (Nat.succ.inj dimension) index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
              ac_rfl

/-- Unit-weight enumeration of every ordered colour word. -/
def unitWordAtoms (colours : Nat) : Nat → List (List Nat × Nat)
  | 0 => [([], 1)]
  | n + 1 => (finWeighted colours (fun _ => 1)).flatMap fun head =>
      (unitWordAtoms colours n).map (fun rest => (head.1.val :: rest.1, head.2 * rest.2))

/-- Draw with the current categorical weights, then add one unit to the
colour drawn before continuing. -/
def multicolourPolyaAtoms : Nat → List Nat → List (List Nat × Nat)
  | 0, _ => [([], 1)]
  | n + 1, alphas => (finWeighted alphas.length (fun i => alphas.getD i.val 0)).flatMap fun head =>
      (multicolourPolyaAtoms n (alphas.modify head.1.val (fun a => a + 1))).map
        (fun rest => (head.1.val :: rest.1, head.2 * rest.2))

theorem finWeighted_reweight (colours : Nat) (weight : Fin colours → Nat) :
    finWeighted colours weight = (finWeighted colours (fun _ => 1)).map
      (fun atom => (atom.1, atom.2 * weight atom.1)) := by
  induction colours with
  | zero => rfl
  | succ colours ih =>
      simp only [finWeighted, List.map_append, List.map_cons, List.map_nil, List.map_map,
        Function.comp_def, Nat.one_mul]
      rw [ih]
      simp only [List.map_map, Function.comp_def]

theorem multicolourPolyaAtoms_word_weights (n : Nat) (alphas : List Nat) :
    multicolourPolyaAtoms n alphas = (unitWordAtoms alphas.length n).map
      (fun atom => (atom.1, atom.2 * risingKernel alphas (colourCounts alphas.length atom.1))) := by
  induction n generalizing alphas with
  | zero => simp only [multicolourPolyaAtoms, unitWordAtoms, List.map_cons, List.map_nil,
      colourCounts, risingKernel_zeros, Nat.mul_one]
  | succ n ih =>
      rw [multicolourPolyaAtoms, finWeighted_reweight, List.flatMap_map]
      simp only [unitWordAtoms, List.map_flatMap]
      apply congrArg (fun f => (finWeighted alphas.length (fun _ => 1)).flatMap f)
      funext head
      rw [ih, List.length_modify]
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro rest _
      simp only [colourCounts]
      rw [risingKernel_increment alphas _ (colourCounts_length _ _).symm head.1.val head.1.isLt]
      ac_rfl

theorem getD_replicate_of_lt (length value index : Nat) (within : index < length) :
    (List.replicate length value).getD index 0 = value := by
  induction length generalizing index with
  | zero => omega
  | succ length ih =>
      cases index with
      | zero => simp only [List.replicate_succ, List.getD_cons_zero]
      | succ index =>
          simp only [List.replicate_succ, List.getD_cons_succ]
          exact ih index (by omega)

theorem unitWordAtoms_categorical (colours n : Nat) (positive : 0 < colours) :
    unitWordAtoms colours n = (categoricalWordDistro (List.replicate colours 1)
      (by simpa only [List.sum_replicate_nat, Nat.mul_one] using positive) n).record.atoms := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have weights : (fun i : Fin (List.replicate colours 1).length => (List.replicate colours 1).getD i.val 0) =
          (fun _ => 1) := by
        funext i
        exact getD_replicate_of_lt colours 1 i.val (by simpa only [List.length_replicate] using i.isLt)
      change unitWordAtoms colours (n + 1) =
        (FiniteProbRecord.weightedCartesian
          (finWeighted (List.replicate colours 1).length (fun i => (List.replicate colours 1).getD i.val 0))
          (categoricalWordDistro _ _ n).record.atoms).map
            (fun source => (source.1.1.val :: source.1.2, source.2))
      rw [weights, List.length_replicate, ← ih]
      simp only [unitWordAtoms, FiniteProbRecord.weightedCartesian, List.map_flatMap, List.map_map, Function.comp_def]

theorem totalMass_multicolourPolyaAtoms (n : Nat) (alphas : List Nat) :
    FiniteProbRecord.totalMass (multicolourPolyaAtoms n alphas) = risingFactorial alphas.sum n := by
  induction n generalizing alphas with
  | zero => rfl
  | succ n ih =>
      rw [multicolourPolyaAtoms, totalMass_flatMap]
      have row (head : Fin alphas.length × Nat) :
          FiniteProbRecord.totalMass
            ((multicolourPolyaAtoms n (alphas.modify head.1.val (fun a => a + 1))).map
              (fun rest => (head.1.val :: rest.1, head.2 * rest.2))) =
          head.2 * risingFactorial (alphas.sum + 1) n := by
        rw [FiniteProbRecord.totalMass_map_weight, ih, sum_modify_succ alphas head.1.val head.1.isLt]
      rw [List.map_congr_left (fun head _ => row head)]
      rw [← natIntegral_eq_sum (finWeighted alphas.length (fun i => alphas.getD i.val 0))
        (fun _ => risingFactorial (alphas.sum + 1) n)]
      rw [natIntegral_constant, totalMass_finWeighted, finWeight_getD_sum, risingFactorial_head]

def multicolourPolyaDistro (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) : Distro (List Nat) :=
  ofWeightedAtoms (multicolourPolyaAtoms n alphas) (by
    rw [totalMass_multicolourPolyaAtoms]; exact risingFactorial_pos _ _ positive)

theorem multicolourPolya_den (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    (multicolourPolyaDistro n alphas positive).record.den = risingFactorial alphas.sum n :=
  totalMass_multicolourPolyaAtoms n alphas

theorem list_length_positive_of_sum (alphas : List Nat) (positive : 0 < alphas.sum) : 0 < alphas.length := by
  cases alphas with
  | nil => simp only [List.sum_nil] at positive; omega
  | cons alpha alphas => exact Nat.succ_pos _

/-- One occupancy cell per composition, with multinomial coefficient
multiplied by the rising factors. -/
def dirichletMultinomialAtoms (n : Nat) (alphas : List Nat) : List (List Nat × Nat) :=
  (multinomialAtoms n (List.replicate alphas.length 1)).map
    (fun atom => (atom.1, atom.2 * risingKernel alphas atom.1))

theorem dirichletMultinomial_integral (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    natIntegral (multinomialAtoms n (List.replicate alphas.length 1)) (risingKernel alphas) =
      risingFactorial alphas.sum n := by
  let ones := List.replicate alphas.length 1
  have onePositive : 0 < ones.sum := by
    simpa only [ones, List.sum_replicate_nat, Nat.mul_one] using list_length_positive_of_sum alphas positive
  have same := (multinomial_categorical_correspondence n ones onePositive).expectNat (risingKernel alphas)
  rw [categoricalOccupancyDistro, Distro.expectNat_map] at same
  change natIntegral (categoricalWordDistro ones onePositive n).record.atoms
      (fun word => risingKernel alphas (colourCounts ones.length word)) *
      (multinomialDistro n ones onePositive).record.den =
    natIntegral (multinomialAtoms n ones) (risingKernel alphas) *
      (categoricalWordDistro ones onePositive n).record.den at same
  have denominators : (multinomialDistro n ones onePositive).record.den =
      (categoricalWordDistro ones onePositive n).record.den := by rw [multinomial_den, categoricalWord_den]
  rw [denominators] at same
  have raw := Nat.eq_of_mul_eq_mul_right (categoricalWordDistro ones onePositive n).record.den_pos same
  rw [← raw]
  change natIntegral (categoricalWordDistro (List.replicate alphas.length 1) onePositive n).record.atoms
    (fun word => risingKernel alphas (colourCounts (List.replicate alphas.length 1).length word)) = _
  rw [← unitWordAtoms_categorical alphas.length n (list_length_positive_of_sum alphas positive), List.length_replicate]
  rw [← totalMass_reweight, ← multicolourPolyaAtoms_word_weights, totalMass_multicolourPolyaAtoms]

theorem totalMass_dirichletMultinomialAtoms (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    FiniteProbRecord.totalMass (dirichletMultinomialAtoms n alphas) = risingFactorial alphas.sum n := by
  rw [dirichletMultinomialAtoms, totalMass_reweight, dirichletMultinomial_integral n alphas positive]

def dirichletMultinomialDistro (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) : Distro (List Nat) :=
  ofWeightedAtoms (dirichletMultinomialAtoms n alphas) (by
    rw [totalMass_dirichletMultinomialAtoms n alphas positive]; exact risingFactorial_pos _ _ positive)

theorem dirichletMultinomial_den (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    (dirichletMultinomialDistro n alphas positive).record.den = risingFactorial alphas.sum n :=
  totalMass_dirichletMultinomialAtoms n alphas positive

theorem multicolourPolya_reweight (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    multicolourPolyaDistro n alphas positive =
      (categoricalWordDistro (List.replicate alphas.length 1)
        (by simpa only [List.sum_replicate_nat, Nat.mul_one] using list_length_positive_of_sum alphas positive) n).reweightNat
        (fun word => risingKernel alphas (colourCounts alphas.length word)) (by
          rw [← unitWordAtoms_categorical alphas.length n (list_length_positive_of_sum alphas positive),
            ← totalMass_reweight, ← multicolourPolyaAtoms_word_weights, totalMass_multicolourPolyaAtoms]
          exact risingFactorial_pos _ _ positive) := by
  apply Distro.eq_of_atoms_den
  · change multicolourPolyaAtoms n alphas =
      (categoricalWordDistro (List.replicate alphas.length 1) _ n).record.atoms.map
        (fun atom => (atom.1, atom.2 * risingKernel alphas (colourCounts alphas.length atom.1)))
    rw [multicolourPolyaAtoms_word_weights, unitWordAtoms_categorical alphas.length n (list_length_positive_of_sum alphas positive)]
  · rw [multicolourPolya_den, Distro.reweightNat_den,
      ← unitWordAtoms_categorical alphas.length n (list_length_positive_of_sum alphas positive),
      ← totalMass_reweight, ← multicolourPolyaAtoms_word_weights, totalMass_multicolourPolyaAtoms]

/-- Reading counts from the actual reinforced categorical draws produces
the Dirichlet-multinomial law on every Boolean event. -/
theorem dirichletMultinomial_polya_correspondence (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) :
    ((multicolourPolyaDistro n alphas positive).map (colourCounts alphas.length)).SameLaw
      (dirichletMultinomialDistro n alphas positive) := by
  let ones := List.replicate alphas.length 1
  have onePositive : 0 < ones.sum := by
    simpa only [ones, List.sum_replicate_nat, Nat.mul_one] using list_length_positive_of_sum alphas positive
  let word := categoricalWordDistro ones onePositive n
  let occupancy := categoricalOccupancyDistro n ones onePositive
  let multinomial := multinomialDistro n ones onePositive
  have hp : 0 < natIntegral multinomial.record.atoms (risingKernel alphas) := by
    change 0 < natIntegral (multinomialAtoms n (List.replicate alphas.length 1)) (risingKernel alphas)
    rw [dirichletMultinomial_integral n alphas positive]
    exact risingFactorial_pos _ _ positive
  have hp' : 0 < natIntegral occupancy.record.atoms (risingKernel alphas) := by
    have same := (multinomial_categorical_correspondence n ones onePositive).expectNat (risingKernel alphas)
    change natIntegral occupancy.record.atoms (risingKernel alphas) * multinomial.record.den =
      natIntegral multinomial.record.atoms (risingKernel alphas) * occupancy.record.den at same
    have h : 0 < natIntegral multinomial.record.atoms (risingKernel alphas) * occupancy.record.den :=
      Nat.mul_pos hp occupancy.record.den_pos
    rw [← same] at h
    exact Nat.pos_of_mul_pos_right h
  have actual : (multicolourPolyaDistro n alphas positive).map (colourCounts alphas.length) =
      occupancy.reweightNat (risingKernel alphas) hp' := by
    rw [multicolourPolya_reweight]
    have dim : ones.length = alphas.length := List.length_replicate
    have hmap := Distro.reweightNat_map word (colourCounts alphas.length) (risingKernel alphas)
      (by simpa only [occupancy, categoricalOccupancyDistro, word, dim] using hp')
    simpa only [word, occupancy, categoricalOccupancyDistro, ones, List.length_replicate] using hmap
  have named : dirichletMultinomialDistro n alphas positive = multinomial.reweightNat (risingKernel alphas) hp := by
    apply Distro.eq_of_atoms_den
    · rfl
    · rfl
  rw [actual, named]
  exact (multinomial_categorical_correspondence n ones onePositive).reweightNat (risingKernel alphas) hp' hp

/-- Categorical selection followed by the selected reinforced continuation. -/
theorem multicolourPolya_first_step (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum)
    (event : Event (List Nat)) :
    QProb.Equiv ((multicolourPolyaDistro (n + 1) alphas positive).record.probVal event)
      ((listCategoricalDistro alphas positive).expectation (fun colour =>
        (multicolourPolyaDistro n (alphas.modify colour.val (fun a => a + 1))
          (by rw [sum_modify_succ alphas colour.val colour.isLt]; omega)).record.probVal
            (fun word => event (colour.val :: word)))) := by
  let T := risingFactorial (alphas.sum + 1) n
  have hT : 0 < T := risingFactorial_pos _ _ (by omega)
  let mass (colour : Fin alphas.length) := FiniteProbRecord.eventMass
    (multicolourPolyaAtoms n (alphas.modify colour.val (fun a => a + 1)))
      (fun word => event (colour.val :: word))
  have normalized (colour : Fin alphas.length) :
      QProb.Equiv ((multicolourPolyaDistro n (alphas.modify colour.val (fun a => a + 1))
        (by rw [sum_modify_succ alphas colour.val colour.isLt]; omega)).record.probVal
          (fun word => event (colour.val :: word))) (⟨mass colour, T, hT⟩ : QProb) := by
    change mass colour * T = mass colour * FiniteProbRecord.totalMass
      (multicolourPolyaAtoms n (alphas.modify colour.val (fun a => a + 1)))
    rw [totalMass_multicolourPolyaAtoms, sum_modify_succ alphas colour.val colour.isLt]
  have massEq : FiniteProbRecord.eventMass (multicolourPolyaAtoms (n + 1) alphas) event =
      natIntegral (listCategoricalDistro alphas positive).record.atoms mass := by
    rw [multicolourPolyaAtoms, eventMass_flatMap]
    have rows : ((finWeighted alphas.length (fun i => alphas.getD i.val 0)).map
        (fun head => FiniteProbRecord.eventMass
          ((multicolourPolyaAtoms n (alphas.modify head.1.val (fun a => a + 1))).map
            (fun rest => (head.1.val :: rest.1, head.2 * rest.2))) event)) =
      (finWeighted alphas.length (fun i => alphas.getD i.val 0)).map (fun head => head.2 * mass head.1) := by
      apply List.map_congr_left
      intro head _
      exact FiniteProbRecord.eventMass_map_weight _ (fun word => head.1.val :: word) head.2 event
    rw [rows, ← natIntegral_eq_sum]
    rfl
  refine QProb.equiv_trans ?_ (QProb.equiv_symm
    ((listCategoricalDistro alphas positive).expectation_congr _ _ normalized))
  change QProb.Equiv ((multicolourPolyaDistro (n + 1) alphas positive).record.probVal event)
    (QProb.div (rationalIntegral (listCategoricalDistro alphas positive).record.atoms
      (fun colour => (⟨mass colour, T, hT⟩ : QProb)))
      (QProb.ofNat (listCategoricalDistro alphas positive).record.den) _)
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (QProb.div_congr
    (rationalIntegral_commonDen _ mass T hT) (QProb.equiv_refl _)
      (listCategoricalDistro alphas positive).record.den_pos (listCategoricalDistro alphas positive).record.den_pos))
  change FiniteProbRecord.eventMass (multicolourPolyaAtoms (n + 1) alphas) event *
    (T * (listCategoricalDistro alphas positive).record.den) =
    (natIntegral (listCategoricalDistro alphas positive).record.atoms mass * 1) *
      (multicolourPolyaDistro (n + 1) alphas positive).record.den
  rw [massEq, listCategorical_den, multicolourPolya_den, risingFactorial_head, Nat.mul_one]
  dsimp only [T]
  ac_rfl

theorem eventMass_reweight_singleton [DecidableEq Ω] (atoms : List (Ω × Nat)) (weight : Ω → Nat) (value : Ω) :
    FiniteProbRecord.eventMass (atoms.map (fun atom => (atom.1, atom.2 * weight atom.1)))
      (FiniteProbRecord.singletonEvent value) =
      FiniteProbRecord.eventMass atoms (FiniteProbRecord.singletonEvent value) * weight value := by
  induction atoms with
  | nil => simp only [List.map_nil, FiniteProbRecord.eventMass, Nat.zero_mul]
  | cons atom atoms ih =>
      by_cases eq : atom.1 = value
      · simp only [List.map_cons, FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
          eq, decide_true, if_true] at ih ⊢
        rw [ih, Nat.add_mul]
      · simp only [List.map_cons, FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
          eq, decide_false, Bool.false_eq_true, if_false] at ih ⊢
        exact ih

def dirichletMultinomialWeight (alphas counts : List Nat) : Nat :=
  multinomialWeight (List.replicate alphas.length 1) counts * risingKernel alphas counts

/-- The finite PMF, including zero individual alpha values. -/
theorem dirichletMultinomial_pmf (n : Nat) (alphas counts : List Nat) (positive : 0 < alphas.sum) :
    QProb.Equiv ((dirichletMultinomialDistro n alphas positive).pmf counts)
      ⟨if counts.sum = n then dirichletMultinomialWeight alphas counts else 0,
        risingFactorial alphas.sum n, risingFactorial_pos _ _ positive⟩ := by
  change FiniteProbRecord.eventMass (dirichletMultinomialAtoms n alphas)
    (FiniteProbRecord.singletonEvent counts) * risingFactorial alphas.sum n =
    _ * (dirichletMultinomialDistro n alphas positive).record.den
  rw [dirichletMultinomialAtoms, eventMass_reweight_singleton, eventMass_multinomialAtoms,
    dirichletMultinomial_den]
  by_cases eq : counts.sum = n
  · simp only [eq, if_true, dirichletMultinomialWeight]
  · simp only [eq, if_false, Nat.zero_mul]

def twoColourWord (word : List Bool) : List Nat := word.map (fun colour => if colour then 0 else 1)

theorem multicolourPolyaAtoms_two (n a b : Nat) :
    multicolourPolyaAtoms n [a, b] =
      (polyaPathAtoms n a b).map (fun atom => (twoColourWord atom.1, atom.2)) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      simp only [multicolourPolyaAtoms, List.length_cons, List.length_nil, finWeighted,
        List.map_nil, List.nil_append, List.cons_append, List.map_cons, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Fin.val_castSucc, Fin.val_last, List.getD_cons_zero,
        List.getD_cons_succ, List.modify_zero_cons, List.modify_succ_cons, ih,
        List.map_map, Function.comp_def, polyaPathAtoms, List.map_append,
        twoColourWord, List.map_cons, Bool.false_eq_true, if_false, if_true]

theorem colourCounts_two_successes (word : List Bool) :
    (colourCounts 2 (twoColourWord word)).getD 0 0 = polyaSuccesses word := by
  induction word with
  | nil => rfl
  | cons colour word ih =>
      cases colour <;>
        simp only [twoColourWord, List.map_cons, Bool.false_eq_true, if_false, if_true, colourCounts] at *
      · rw [getD_modify_add _ 1 0 1 (by rw [colourCounts_length]; decide)]
        simpa only [Nat.add_one_ne_zero, if_false, Nat.add_zero, polyaSuccesses] using ih
      · rw [getD_modify_add _ 0 0 1 (by rw [colourCounts_length]; decide)]
        simpa only [if_true, polyaSuccesses] using congrArg (fun x => x + 1) ih

/-- The two-colour specialization recovers beta-binomial, including either
zero-colour endpoint. -/
theorem dirichletMultinomial_two_betaBinomial (n a b : Nat) (positive : 0 < a + b) :
    ((dirichletMultinomialDistro n [a, b] (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive)).map
      (fun counts => polyaCountFin n (counts.getD 0 0))).SameLaw
      (betaBinomialDistroOfTotal n a b positive) := by
  have correspondence := dirichletMultinomial_polya_correspondence n [a, b]
    (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive)
  have same := correspondence.symm.map (fun counts => polyaCountFin n (counts.getD 0 0))
  have actual : (((multicolourPolyaDistro n [a, b]
      (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive)).map (colourCounts [a, b].length)).map
        (fun counts => polyaCountFin n (counts.getD 0 0))) = polyaUrnDistro n a b positive := by
    apply Distro.eq_of_atoms_den
    · change ((multicolourPolyaAtoms n [a, b]).map _).map _ = _
      rw [multicolourPolyaAtoms_two]
      simp only [List.map_map, Function.comp_def, polyaUrnDistro, polyaCountRecord,
        polyaPathRecord, FiniteProbRecord.map]
      apply List.map_congr_left
      intro atom _
      change (polyaCountFin n ((colourCounts 2 (twoColourWord atom.1)).getD 0 0), atom.2) = _
      rw [colourCounts_two_successes]
    · simp only [Distro.map, FiniteProbRecord.map]
      rw [multicolourPolya_den]
      rfl
  rw [actual] at same
  exact same.trans (polyaUrn_total_correspondence n a b positive)

theorem dirichletMultinomial_support (n : Nat) (alphas : List Nat) (atom : List Nat × Nat)
    (member : atom ∈ dirichletMultinomialAtoms n alphas) :
    atom.1.length = alphas.length ∧ atom.1.sum = n := by
  rcases List.mem_map.mp member with ⟨source, hs, eq⟩
  cases eq
  have support := multinomialAtoms_support n (List.replicate alphas.length 1) source hs
  exact ⟨support.1.trans List.length_replicate, support.2⟩

def dirichletMultinomialCoordinate (n : Nat) (alphas : List Nat) (positive : 0 < alphas.sum) (index : Nat) :
    NatDistro (List Nat) := ⟨dirichletMultinomialDistro n alphas positive, fun counts => counts.getD index 0⟩

/-- The unclipped first coordinate has the beta-binomial numeric law. -/
theorem dirichletMultinomial_two_coordinate (n a b : Nat) (positive : 0 < a + b) :
    (dirichletMultinomialCoordinate n [a, b]
      (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive) 0).SameLaw
      (betaBinomialNatDistroOfTotal n a b positive) := by
  apply (NatDistro.sameLaw_iff_events _ _).mpr
  intro event
  let μ := dirichletMultinomialDistro n [a, b]
    (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using positive)
  have clipped := dirichletMultinomial_two_betaBinomial n a b positive
  refine QProb.equiv_trans (μ.probVal_congr_on_support _ (fun counts => event (min (counts.getD 0 0) n)) ?_) ?_
  · intro atom member
    have support := dirichletMultinomial_support n [a, b] atom member
    have bound : atom.1.getD 0 0 ≤ n := by
      cases counts : atom.1 with
      | nil => simp only [List.getD_nil]; omega
      | cons count counts =>
          simp only [counts, List.sum_cons] at support
          simp only [List.getD_cons_zero]
          omega
    change event (atom.1.getD 0 0) = event (min (atom.1.getD 0 0) n)
    rw [Nat.min_eq_left bound]
  · refine QProb.equiv_trans (QProb.equiv_symm
      (μ.map_probVal (fun counts => polyaCountFin n (counts.getD 0 0)) (fun k => event k.val))) ?_
    exact clipped (fun k => event k.val)

end Thesis.Probability.Distros
