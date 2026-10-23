import Thesis.Probability.Distros.MultinomialAggregation
namespace Thesis.Probability.Distros

/-- A finite table of an arbitrary natural observable. -/
def natTabulate (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => f 0 :: natTabulate (fun i => f (i + 1)) n

theorem natTabulate_length (f : Nat → Nat) (n : Nat) : (natTabulate f n).length = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [natTabulate, List.length_cons, ih]

theorem natTabulate_getD (f : Nat → Nat) (n i : Nat) (within : i < n) : (natTabulate f n).getD i 0 = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih => cases i with
      | zero => rfl
      | succ i => exact ih (fun j => f (j + 1)) i (by omega)

theorem getD_map_on_lt (values : List Nat) (f : Nat → Nat) (i : Nat) (within : i < values.length) :
    (values.map f).getD i 0 = f (values.getD i 0) := by
  induction values generalizing i with
  | nil => simp only [List.length_nil] at within; omega
  | cons value values ih => cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)

/-- Relabelling categorical colours sums their weights within each destination. -/
theorem categorical_aggregation (groups : Nat) (alphas labels : List Nat)
    (positive : 0 < alphas.sum) (dimension : labels.length = alphas.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((listCategoricalDistro alphas positive).map (fun i => labels.getD i.val 0)).SameLaw
      ((listCategoricalDistro (aggregateCounts groups labels alphas)
        (by rw [aggregateCounts_sum groups labels alphas dimension within]; exact positive)).map (fun i => i.val)) := by
  apply (Distro.sameLaw_iff_expectNat _ _).mpr
  intro f
  rw [Distro.expectNat_map, Distro.expectNat_map]
  let grouped := aggregateCounts groups labels alphas
  let args := natTabulate f groups
  have total : grouped.sum = alphas.sum := aggregateCounts_sum groups labels alphas dimension within
  have oldFun : (fun i : Fin alphas.length => f (labels.getD i.val 0)) =
      (fun i => (labels.map f).getD i.val 0) := by
    funext i
    exact (getD_map_on_lt labels f i.val (by rw [dimension]; exact i.isLt)).symm
  have newFun : (fun i : Fin grouped.length => f i.val) = (fun i => args.getD i.val 0) := by
    funext i
    exact (natTabulate_getD f groups i.val (by simpa only [grouped, aggregateCounts_length] using i.isLt)).symm
  have selected : labels.map (fun label => args.getD label 0) = labels.map f := by
    apply List.map_congr_left
    intro label member
    exact natTabulate_getD f groups label (within label member)
  have dot : weightedNatArgument grouped args = weightedNatArgument alphas (labels.map f) := by
    rw [weightedNatArgument_aggregate groups labels alphas args dimension (natTabulate_length f groups) within, selected]
  rw [oldFun, newFun]
  refine QProb.equiv_trans (listCategorical_expectNat alphas (labels.map f) positive
    (by rw [List.length_map, dimension])) ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (listCategorical_expectNat grouped args (by rw [total]; exact positive)
    ((natTabulate_length f groups).trans (aggregateCounts_length _ _ _).symm)))
  change weightedNatArgument alphas (labels.map f) * grouped.sum = weightedNatArgument grouped args * alphas.sum
  rw [total, dot]

theorem modify_add_combine (values : List Nat) (i a b : Nat) :
    (values.modify i (fun x => x + a)).modify i (fun x => x + b) = values.modify i (fun x => x + (a + b)) := by
  induction values generalizing i with
  | nil => simp only [List.modify_nil]
  | cons value values ih => cases i with
      | zero => simp only [List.modify_zero_cons, Nat.add_assoc]
      | succ i => simp only [List.modify_succ_cons, ih]

/-- Updating one original colour updates precisely its destination group. -/
theorem aggregateCounts_modify (groups : Nat) (labels alphas : List Nat)
    (dimension : labels.length = alphas.length) (i increment : Nat) (within : i < alphas.length) :
    aggregateCounts groups labels (alphas.modify i (fun x => x + increment)) =
      (aggregateCounts groups labels alphas).modify (labels.getD i 0) (fun x => x + increment) := by
  induction alphas generalizing labels i with
  | nil => simp only [List.length_nil] at within; omega
  | cons alpha alphas ih => cases labels with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; omega
      | cons label labels => cases i with
          | zero => simp only [List.modify_zero_cons, aggregateCounts, List.getD_cons_zero, modify_add_combine]
          | succ i =>
              simp only [List.modify_succ_cons, aggregateCounts, List.getD_cons_succ]
              rw [ih labels (Nat.succ.inj dimension) i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)]
              exact modify_add_comm _ _ _ _ _

/-- Empty counts remain empty under grouping, including unused groups. -/
theorem aggregateCounts_zeros (groups : Nat) (labels : List Nat) :
    aggregateCounts groups labels (List.replicate labels.length 0) = List.replicate groups 0 := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp only [List.length_cons, List.replicate_succ, aggregateCounts, ih, modify_add_zero]

/-- Grouping a valid word's count vector agrees with counting its relabelled word. -/
theorem aggregateCounts_colourCounts (groups colours : Nat) (labels word : List Nat)
    (dimension : labels.length = colours) (valid : ∀ colour ∈ word, colour < colours) :
    aggregateCounts groups labels (colourCounts colours word) =
      colourCounts groups (word.map (fun colour => labels.getD colour 0)) := by
  induction word with
  | nil => rw [colourCounts, ← dimension, aggregateCounts_zeros]; rfl
  | cons colour word ih =>
      simp only [colourCounts, List.map_cons]
      rw [aggregateCounts_modify groups labels _ (dimension.trans (colourCounts_length colours word).symm)
        colour 1 (by simpa only [colourCounts_length] using valid colour (List.mem_cons_self ..)),
        ih (fun i member => valid i (List.mem_cons_of_mem _ member))]

theorem sum_modify_add_ge (values : List Nat) (i increment : Nat) :
    values.sum ≤ (values.modify i (fun x => x + increment)).sum := by
  induction values generalizing i with
  | nil => simp only [List.modify_nil, Nat.le_refl]
  | cons value values ih => cases i with
      | zero => simp only [List.modify_zero_cons, List.sum_cons]; omega
      | succ i => simp only [List.modify_succ_cons, List.sum_cons]; have h := ih i; omega

theorem Distro.sameLaw_maps_on_support (μ : Distro Ω) (f g : Ω → X)
    (same : ∀ atom ∈ μ.record.atoms, f atom.1 = g atom.1) : (μ.map f).SameLaw (μ.map g) := by
  intro event
  refine QProb.equiv_trans (μ.map_probVal f event) ?_
  refine QProb.equiv_trans (μ.probVal_congr_on_support (fun x => event (f x)) (fun x => event (g x))
    (fun atom member => congrArg event (same atom member))) ?_
  exact QProb.equiv_symm (μ.map_probVal g event)

end Thesis.Probability.Distros
