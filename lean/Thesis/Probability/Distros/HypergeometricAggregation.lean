import Thesis.Probability.Distros.HypergeometricMarginals
import Thesis.Probability.Distros.TriangularSums

namespace Thesis.Probability.Distros
open Combinatorics

/-- Unnormalized subset integral. Keeping this defined for every sample
size permits coarsening proofs without assuming positive intermediate stocks. -/
def hypergeometricIntegral (n : Nat) (stocks : List Nat) (f : List Nat → Nat) : Nat :=
  natIntegral (multivariateHypergeometricAtoms n stocks) f

theorem hypergeometricIntegral_cons (n stock : Nat) (stocks : List Nat) (f : List Nat → Nat) :
    hypergeometricIntegral n (stock :: stocks) f =
      natSum (n + 1) (fun used => binom stock used * hypergeometricIntegral (n - used) stocks (fun counts => f (used :: counts))) := by
  unfold hypergeometricIntegral
  rw [multivariateHypergeometricAtoms, natIntegral_flatMap, sum_map_range_natSum]
  apply natSum_congr
  intro used _
  rw [natIntegral_map_weight]

theorem hypergeometricIntegral_two (n a b : Nat) (stocks : List Nat) (f : List Nat → Nat) :
    hypergeometricIntegral n (a :: b :: stocks) f =
      natSum (n + 1) (fun total => natSum (total + 1) (fun used =>
        binom a used * binom b (total - used) *
          hypergeometricIntegral (n - total) stocks (fun counts => f (used :: (total - used) :: counts)))) := by
  rw [hypergeometricIntegral_cons]
  calc
    _ = natSum (n + 1) (fun i => natSum (n - i + 1) (fun j =>
        binom a i * binom b j * hypergeometricIntegral (n - i - j) stocks (fun counts => f (i :: j :: counts)))) := by
      apply natSum_congr
      intro i _
      rw [hypergeometricIntegral_cons, ← natSum_mul_left]
      apply natSum_congr
      intro j _
      ac_rfl
    _ = natSum (n + 1) (fun total => natSum (total + 1) (fun i =>
        binom a i * binom b (total - i) *
          hypergeometricIntegral (n - i - (total - i)) stocks (fun counts => f (i :: (total - i) :: counts)))) :=
      natSum_triangle n _
    _ = _ := by
      apply natSum_congr
      intro total totalWithin
      apply natSum_congr
      intro used usedWithin
      have index : n - used - (total - used) = n - total := by omega
      rw [index]

def mergeHeadInto (index : Nat) : List Nat → List Nat
  | [] => []
  | head :: tail => tail.modify index (fun old => old + head)

private def swapFirstTwo : List Nat → List Nat
  | first :: second :: tail => second :: first :: tail
  | counts => counts

private theorem hypergeometricIntegral_congr_two (n a b : Nat) (stocks : List Nat) (f g : List Nat → Nat)
    (same : ∀ i j tail, f (i :: j :: tail) = g (i :: j :: tail)) :
    hypergeometricIntegral n (a :: b :: stocks) f = hypergeometricIntegral n (a :: b :: stocks) g := by
  rw [hypergeometricIntegral_cons, hypergeometricIntegral_cons]
  apply natSum_congr
  intro i _
  apply congrArg (fun value => binom a i * value)
  rw [hypergeometricIntegral_cons, hypergeometricIntegral_cons]
  apply natSum_congr
  intro j _
  apply congrArg (fun value => binom b j * value)
  exact natIntegral_congr _ _ _ (same i j)

private theorem hypergeometricIntegral_swap (n a b : Nat) (stocks : List Nat) (f : List Nat → Nat) :
    hypergeometricIntegral n (a :: b :: stocks) (fun counts => f (swapFirstTwo counts)) =
      hypergeometricIntegral n (b :: a :: stocks) f := by
  rw [hypergeometricIntegral_two, hypergeometricIntegral_two]
  apply natSum_congr
  intro total _
  rw [← natSum_reverse total]
  apply natSum_congr
  intro used usedWithin
  have complement : total - (total - used) = used := by omega
  simp only [swapFirstTwo, complement]
  ac_rfl

private theorem hypergeometricIntegral_mergeFirst (n a b : Nat) (stocks : List Nat) (f : List Nat → Nat) :
    hypergeometricIntegral n (a :: b :: stocks) (fun counts => f (mergeHeadInto 0 counts)) =
      hypergeometricIntegral n ((a + b) :: stocks) f := by
  rw [hypergeometricIntegral_two, hypergeometricIntegral_cons]
  apply natSum_congr
  intro total totalWithin
  have row : natSum (total + 1) (fun used => binom a used * binom b (total - used) *
        hypergeometricIntegral (n - total) stocks (fun counts => f (mergeHeadInto 0 (used :: (total - used) :: counts)))) =
      natSum (total + 1) (fun used => (binom a used * binom b (total - used)) *
        hypergeometricIntegral (n - total) stocks (fun counts => f (total :: counts))) := by
    apply natSum_congr
    intro used within
    have balance : total - used + used = total := Nat.sub_add_cancel (by omega)
    simp only [mergeHeadInto, List.modify_zero_cons, balance]
  rw [row, natSum_mul_right, vandermonde]

/-- Merge an arbitrary selected destination with a new first colour. This
is the local coarsening step used for every finite category partition. -/
theorem hypergeometricIntegral_mergeHead (n stock : Nat) (stocks : List Nat) (index : Nat)
    (f : List Nat → Nat) (within : index < stocks.length) :
    hypergeometricIntegral n (stock :: stocks) (fun counts => f (mergeHeadInto index counts)) =
      hypergeometricIntegral n (stocks.modify index (fun old => old + stock)) f := by
  induction index generalizing stocks n f with
  | zero => cases stocks with
      | nil => simp only [List.length_nil] at within; exact False.elim (by omega)
      | cons other stocks =>
          simpa only [List.modify_zero_cons, Nat.add_comm other stock] using
            hypergeometricIntegral_mergeFirst n stock other stocks f
  | succ index ih => cases stocks with
      | nil => simp only [List.length_nil] at within; exact False.elim (by omega)
      | cons other stocks =>
          let continuation : List Nat → Nat := fun counts => match counts with
            | [] => f []
            | head :: tail => f (head :: mergeHeadInto index tail)
          have transport : hypergeometricIntegral n (stock :: other :: stocks) (fun counts => f (mergeHeadInto (index + 1) counts)) =
              hypergeometricIntegral n (stock :: other :: stocks) (fun counts => continuation (swapFirstTwo counts)) := by
            apply hypergeometricIntegral_congr_two
            intro i j tail
            simp only [mergeHeadInto, swapFirstTwo, continuation, List.modify_succ_cons]
          rw [transport, hypergeometricIntegral_swap, List.modify_succ_cons, hypergeometricIntegral_cons, hypergeometricIntegral_cons]
          apply natSum_congr
          intro used _
          apply congrArg (fun value => binom other used * value)
          exact ih stocks (n - used) (fun counts => f (used :: counts)) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within)

private theorem hypergeometricIntegral_nil (n : Nat) (f : List Nat → Nat) :
    hypergeometricIntegral n [] f = if n = 0 then f [] else 0 := by
  by_cases zero : n = 0
  · subst n; rfl
  · simp only [hypergeometricIntegral, multivariateHypergeometricAtoms, if_neg zero, natIntegral]

private theorem hypergeometricIntegral_zeroHead (n : Nat) (stocks : List Nat) (f : List Nat → Nat) :
    hypergeometricIntegral n (0 :: stocks) f = hypergeometricIntegral n stocks (fun counts => f (0 :: counts)) := by
  rw [hypergeometricIntegral_cons]
  have zero : ∀ k, binom 0 k = if k = 0 then 1 else 0 := by
    intro k
    cases k with
    | zero => rfl
    | succ k => simp only [binom_zero_succ, if_neg (Nat.ne_of_gt (Nat.succ_pos k))]
  have terms : natSum (n + 1) (fun used => binom 0 used * hypergeometricIntegral (n - used) stocks (fun counts => f (used :: counts))) =
      natSum (n + 1) (fun used => (if used = 0 then 1 else 0) * hypergeometricIntegral (n - used) stocks (fun counts => f (used :: counts))) := by
    apply natSum_congr
    intro used _
    rw [zero]
  rw [terms, natSum_spike, if_pos (Nat.succ_pos n), Nat.one_mul, Nat.sub_zero]

private theorem hypergeometricIntegral_zeroStocks (n groups : Nat) (f : List Nat → Nat) :
    hypergeometricIntegral n (List.replicate groups 0) f = if n = 0 then f (List.replicate groups 0) else 0 := by
  induction groups generalizing f with
  | zero => exact hypergeometricIntegral_nil n f
  | succ groups ih =>
      rw [List.replicate_succ, hypergeometricIntegral_zeroHead, ih]

/-- Unnormalized category coarsening, valid even for sample sizes whose
normalizer is zero. Destination labels may have empty colour preimages. -/
theorem hypergeometricIntegral_aggregation (n groups : Nat) (stocks labels : List Nat)
    (dimension : labels.length = stocks.length) (within : ∀ label ∈ labels, label < groups) (f : List Nat → Nat) :
    hypergeometricIntegral n stocks (fun counts => f (aggregateCounts groups labels counts)) =
      hypergeometricIntegral n (aggregateCounts groups labels stocks) f := by
  induction stocks generalizing labels n f with
  | nil => cases labels with
      | nil => rw [hypergeometricIntegral_nil, aggregateCounts, hypergeometricIntegral_zeroStocks]; rfl
      | cons label labels => have dim := dimension; simp only [List.length_nil, List.length_cons] at dim; exact False.elim (by omega)
  | cons stock stocks ih => cases labels with
      | nil => have dim := dimension; simp only [List.length_nil, List.length_cons] at dim; exact False.elim (by omega)
      | cons label labels =>
          let grouped := aggregateCounts groups labels stocks
          have labelWithin : label < grouped.length := by
            rw [aggregateCounts_length]
            exact within label (List.mem_cons_self ..)
          rw [hypergeometricIntegral_cons]
          have tails : natSum (n + 1) (fun used => binom stock used * hypergeometricIntegral (n - used) stocks
                (fun counts => f (aggregateCounts groups (label :: labels) (used :: counts)))) =
              natSum (n + 1) (fun used => binom stock used * hypergeometricIntegral (n - used) grouped
                (fun counts => f (counts.modify label (fun old => old + used)))) := by
            apply natSum_congr
            intro used _
            apply congrArg (fun value => binom stock used * value)
            exact ih labels (n - used) (fun counts => f (counts.modify label (fun old => old + used)))
              (Nat.succ.inj dimension) (fun other member => within other (List.mem_cons_of_mem _ member))
          rw [tails]
          have merged := hypergeometricIntegral_mergeHead n stock grouped label f labelWithin
          rw [hypergeometricIntegral_cons] at merged
          exact merged

/-- Any finite colour partition gives the hypergeometric law with summed
population stocks, preserving every event probability. -/
theorem multivariateHypergeometric_aggregation (n groups : Nat) (stocks labels : List Nat)
    (positive : 0 < binom stocks.sum n) (dimension : labels.length = stocks.length)
    (within : ∀ label ∈ labels, label < groups) :
    ((multivariateHypergeometricDistro n stocks positive).map (aggregateCounts groups labels)).SameLaw
      (multivariateHypergeometricDistro n (aggregateCounts groups labels stocks)
        (by rw [aggregateCounts_sum groups labels stocks dimension within]; exact positive)) := by
  intro event
  change FiniteProbRecord.eventMass
      ((multivariateHypergeometricAtoms n stocks).map (fun atom => (aggregateCounts groups labels atom.1, atom.2))) event *
      binom (aggregateCounts groups labels stocks).sum n =
    FiniteProbRecord.eventMass (multivariateHypergeometricAtoms n (aggregateCounts groups labels stocks)) event * binom stocks.sum n
  rw [FiniteProbRecord.eventMass_map_labels, ← natIntegral_indicator, ← natIntegral_indicator]
  change hypergeometricIntegral n stocks (fun counts => if event (aggregateCounts groups labels counts) then 1 else 0) *
      binom (aggregateCounts groups labels stocks).sum n =
    hypergeometricIntegral n (aggregateCounts groups labels stocks) (fun counts => if event counts then 1 else 0) * binom stocks.sum n
  rw [hypergeometricIntegral_aggregation n groups stocks labels dimension within,
    aggregateCounts_sum groups labels stocks dimension within]

end Thesis.Probability.Distros
