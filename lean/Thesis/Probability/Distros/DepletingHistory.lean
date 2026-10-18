import Thesis.Probability.Distros.DepletingUrn

namespace Thesis.Probability.Distros

/-- Remaining stocks after a count vector, with missing counts interpreted as zero. -/
def depletingState : List Nat → List Nat → List Nat
  | [], _ => []
  | stocks, [] => stocks
  | stock :: stocks, count :: counts => (stock - count) :: depletingState stocks counts

def depletingUpdate : List Nat → List Nat → List Nat
  | stocks, [] => stocks
  | stocks, colour :: history => depletingUpdate (stocks.modify colour (fun stock => stock - 1)) history

theorem depletingState_length (stocks counts : List Nat) : (depletingState stocks counts).length = stocks.length := by
  induction stocks generalizing counts with
  | nil => rfl
  | cons stock stocks ih => cases counts <;> simp only [depletingState, List.length_cons, ih]

theorem depletingState_modify_stock (stocks counts : List Nat) (index : Nat) :
    depletingState (stocks.modify index (fun stock => stock - 1)) counts =
      (depletingState stocks counts).modify index (fun stock => stock - 1) := by
  induction stocks generalizing counts index with
  | nil => simp only [List.modify_nil, depletingState]
  | cons stock stocks ih => cases counts with
      | nil => cases index <;> simp only [List.modify_zero_cons, List.modify_succ_cons, depletingState]
      | cons count counts => cases index with
          | zero => simp only [depletingState, List.modify_zero_cons]; congr 1 <;> omega
          | succ index => simp only [depletingState, List.modify_succ_cons, ih]

theorem depletingState_modify_count (stocks counts : List Nat) (dimension : counts.length = stocks.length) (index : Nat) :
    depletingState stocks (counts.modify index (fun count => count + 1)) =
      (depletingState stocks counts).modify index (fun stock => stock - 1) := by
  induction stocks generalizing counts index with
  | nil => simp only [depletingState, List.modify_nil]
  | cons stock stocks ih => cases counts with
      | nil => simp only [List.length_nil, List.length_cons] at dimension; exact False.elim (by omega)
      | cons count counts => cases index with
          | zero => simp only [depletingState, List.modify_zero_cons]; congr 1 <;> omega
          | succ index => simp only [depletingState, List.modify_succ_cons, ih counts (Nat.succ.inj dimension)]

theorem depletingState_zero (stocks : List Nat) : depletingState stocks (List.replicate stocks.length 0) = stocks := by
  induction stocks with
  | nil => rfl
  | cons stock stocks ih => simp only [List.length_cons, List.replicate_succ, depletingState, Nat.sub_zero, ih]

/-- Removing balls in any observed order leaves the same stock vector. -/
theorem depletingUpdate_counts (stocks history : List Nat) :
    depletingUpdate stocks history = depletingState stocks (colourCounts stocks.length history) := by
  induction history generalizing stocks with
  | nil => exact (depletingState_zero stocks).symm
  | cons colour history ih =>
      simp only [depletingUpdate, ih, List.length_modify, colourCounts]
      rw [depletingState_modify_stock, depletingState_modify_count _ _ (colourCounts_length _ _)]

theorem depletingUpdate_length (stocks history : List Nat) :
    (depletingUpdate stocks history).length = stocks.length := by
  rw [depletingUpdate_counts, depletingState_length]

theorem depletingState_getD (stocks counts : List Nat) (index : Nat) :
    (depletingState stocks counts).getD index 0 = stocks.getD index 0 - counts.getD index 0 := by
  induction stocks generalizing counts index with
  | nil => simp only [depletingState, List.getD_nil, Nat.zero_sub]
  | cons stock stocks ih => cases counts with
      | nil => simp only [depletingState, List.getD_nil, Nat.sub_zero]
      | cons count counts => cases index with
          | zero => rfl
          | succ index => exact ih counts index


/-- Coordinatewise stock availability, with explicit matching dimensions. -/
def depletingCountsWithin : List Nat → List Nat → Prop
  | [], [] => True
  | count :: counts, stock :: stocks => count ≤ stock ∧ depletingCountsWithin counts stocks
  | _, _ => False

instance depletingCountsWithin_decidable : (counts stocks : List Nat) → Decidable (depletingCountsWithin counts stocks)
  | [], [] => inferInstanceAs (Decidable True)
  | [], _ :: _ => inferInstanceAs (Decidable False)
  | _ :: _, [] => inferInstanceAs (Decidable False)
  | count :: counts, stock :: stocks =>
      letI : Decidable (depletingCountsWithin counts stocks) := depletingCountsWithin_decidable counts stocks
      inferInstanceAs (Decidable (count ≤ stock ∧ depletingCountsWithin counts stocks))

/-- Positive falling-kernel weight rules out every overdrawn colour. -/
theorem jointFalling_positive_within (counts stocks : List Nat) (positive : 0 < jointFalling counts stocks) :
    depletingCountsWithin counts stocks := by
  induction counts generalizing stocks with
  | nil => cases stocks with
      | nil => exact True.intro
      | cons stock stocks => change 0 < 0 at positive; exact False.elim (by omega)
  | cons count counts ih => cases stocks with
      | nil => change 0 < 0 at positive; exact False.elim (by omega)
      | cons stock stocks =>
          have head := Nat.pos_of_mul_pos_right positive
          have tail := Nat.pos_of_mul_pos_left positive
          have within : count ≤ stock := by
            by_cases enough : count ≤ stock
            · exact enough
            · rw [fallingFactorial_eq_zero stock count (by omega)] at head
              omega
          exact ⟨within, ih stocks tail⟩

theorem multicolourDepletingAtoms_kernel_positive (n : Nat) (stocks : List Nat) (atom : List Nat × Nat)
    (member : atom ∈ multicolourDepletingAtoms n stocks) (positive : 0 < atom.2) :
    0 < jointFalling (colourCounts stocks.length atom.1) stocks := by
  rw [multicolourDepletingAtoms_word_weights] at member
  rcases List.mem_map.mp member with ⟨source, _, same⟩
  cases same
  exact Nat.pos_of_mul_pos_left positive

/-- Stock conservation is stated with an explicit no-overdraw certificate. -/
theorem depletingState_sum (stocks counts : List Nat)
    (within : depletingCountsWithin counts stocks) :
    (depletingState stocks counts).sum + counts.sum = stocks.sum := by
  induction stocks generalizing counts with
  | nil => cases counts with
      | nil => rfl
      | cons count counts => exact False.elim within
  | cons stock stocks ih => cases counts with
      | nil => exact False.elim within
      | cons count counts =>
          have tail := ih counts within.2
          have balance := Nat.sub_add_cancel within.1
          simp only [depletingState, List.sum_cons]
          omega

/-- Splitting the actual ordered path record at any fixed draw boundary. -/
theorem multicolourDepletingAtoms_append (m n : Nat) (stocks : List Nat) :
    multicolourDepletingAtoms (m + n) stocks =
      (multicolourDepletingAtoms m stocks).flatMap (fun front =>
        (multicolourDepletingAtoms n (depletingUpdate stocks front.1)).map
          (fun back => (front.1 ++ back.1, front.2 * back.2))) := by
  induction m generalizing stocks with
  | zero => simp only [Nat.zero_add, multicolourDepletingAtoms, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, depletingUpdate, List.nil_append, Nat.one_mul]; exact (List.map_id' _).symm
  | succ m ih =>
      have index : m + 1 + n = (m + n) + 1 := by omega
      rw [index, multicolourDepletingAtoms]
      simp only [ih, multicolourDepletingAtoms, List.flatMap_assoc, List.map_flatMap, List.flatMap_map,
        List.map_map, Function.comp_def, depletingUpdate, List.cons_append, Nat.mul_assoc]

end Thesis.Probability.Distros
