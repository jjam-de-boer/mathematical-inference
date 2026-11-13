import Thesis.Probability.Distros.DepletingHistory
import Thesis.Probability.Distros.CategoricalSampling

namespace Thesis.Probability.Distros

/-- The multiplicity of a specified ordered sampling-without-replacement path. -/
def depletingWordWeight : List Nat → List Nat → Nat
  | _, [] => 1
  | stocks, colour :: history => stocks.getD colour 0 *
      depletingWordWeight (stocks.modify colour (fun stock => stock - 1)) history

theorem depletingWordWeight_kernel (stocks history : List Nat)
    (valid : ∀ colour ∈ history, colour < stocks.length) :
    depletingWordWeight stocks history = jointFalling (colourCounts stocks.length history) stocks := by
  induction history generalizing stocks with
  | nil => exact (jointFalling_zeroOrders stocks).symm
  | cons colour history ih =>
      rw [depletingWordWeight, ih]
      · simp only [List.length_modify, colourCounts]
        exact (jointFalling_increment stocks _ (colourCounts_length _ _).symm colour
          (valid colour (List.mem_cons_self ..))).symm
      · intro other member
        simpa only [List.length_modify] using valid other (List.mem_cons_of_mem _ member)

theorem multicolourDepleting_word_mass (stocks : List Nat) (history : List Nat)
    (valid : ∀ colour ∈ history, colour < stocks.length) :
    FiniteProbRecord.eventMass (multicolourDepletingAtoms history.length stocks)
      (FiniteProbRecord.singletonEvent history) = depletingWordWeight stocks history := by
  induction history generalizing stocks with
  | nil => simp only [multicolourDepletingAtoms, FiniteProbRecord.eventMass,
      FiniteProbRecord.singletonEvent, decide_true, if_true, Nat.add_zero, depletingWordWeight]
  | cons colour history ih =>
      rw [List.length_cons, multicolourDepletingAtoms, eventMass_flatMap]
      have rows : ((finWeighted stocks.length (fun i => stocks.getD i.val 0)).map
          (fun head => FiniteProbRecord.eventMass
            ((multicolourDepletingAtoms history.length (stocks.modify head.1.val (fun a => a - 1))).map
              (fun rest => (head.1.val :: rest.1, head.2 * rest.2)))
            (FiniteProbRecord.singletonEvent (colour :: history)))) =
          (finWeighted stocks.length (fun i => stocks.getD i.val 0)).map
            (fun head => head.2 * (if head.1.val = colour then
              FiniteProbRecord.eventMass (multicolourDepletingAtoms history.length
                (stocks.modify head.1.val (fun a => a - 1)))
                (FiniteProbRecord.singletonEvent history) else 0)) := by
        apply List.map_congr_left
        intro head _
        rw [FiniteProbRecord.eventMass_map_weight]
        by_cases same : head.1.val = colour
        · simp only [same, if_true]
          congr 1
          apply FiniteProbRecord.eventMass_congr
          intro rest
          simp only [FiniteProbRecord.singletonEvent, List.cons.injEq, true_and]
        · have ev : (fun rest => FiniteProbRecord.singletonEvent (colour :: history) (head.1.val :: rest)) =
              (fun _ => false) := by
            funext rest
            simp only [FiniteProbRecord.singletonEvent, List.cons.injEq, same, false_and, decide_false]
          rw [ev, FiniteProbRecord.eventMass_false, if_neg same]
      rw [rows, ← natIntegral_eq_sum _ (fun head : Fin stocks.length => if head.val = colour then
        FiniteProbRecord.eventMass (multicolourDepletingAtoms history.length
          (stocks.modify head.val (fun a => a - 1))) (FiniteProbRecord.singletonEvent history) else 0)]
      rw [categorical_head_select stocks colour (fun index => FiniteProbRecord.eventMass
        (multicolourDepletingAtoms history.length (stocks.modify index (fun a => a - 1)))
        (FiniteProbRecord.singletonEvent history)) (valid colour (List.mem_cons_self ..))]
      rw [ih]
      · rfl
      · intro other member
        simpa only [List.length_modify] using valid other (List.mem_cons_of_mem _ member)


/-- The first draw is exactly the existing categorical constructor, encoded
as a one-letter word. Equality includes the actual weighted atom record. -/
theorem multicolourDepleting_one_categorical (stocks : List Nat) (positive : 0 < stocks.sum) :
    multicolourDepletingDistro 1 stocks (by omega) =
      (listCategoricalDistro stocks positive).map (fun colour => [colour.val]) := by
  apply Distro.eq_of_atoms
  change multicolourDepletingAtoms 1 stocks =
    (finWeighted stocks.length (fun i => stocks.getD i.val 0)).map (fun atom => ([atom.1.val], atom.2))
  simp only [multicolourDepletingAtoms, List.map_cons, List.map_nil, Nat.mul_one]
  exact List.map_eq_flatMap.symm

theorem multicolourDepleting_word_pmf (stocks history : List Nat)
    (valid : ∀ colour ∈ history, colour < stocks.length) (within : history.length ≤ stocks.sum) :
    QProb.Equiv ((multicolourDepletingDistro history.length stocks within).pmf history)
      ⟨jointFalling (colourCounts stocks.length history) stocks, fallingFactorial stocks.sum history.length,
        fallingFactorial_pos _ _ within⟩ := by
  change FiniteProbRecord.eventMass (multicolourDepletingAtoms history.length stocks)
      (FiniteProbRecord.singletonEvent history) * fallingFactorial stocks.sum history.length =
    jointFalling (colourCounts stocks.length history) stocks *
      (multicolourDepletingDistro history.length stocks within).record.den
  rw [multicolourDepleting_word_mass stocks history valid, depletingWordWeight_kernel stocks history valid,
    multicolourDepleting_den]

theorem multicolourDepleting_one_colour (stocks : List Nat) (positive : 0 < stocks.sum)
    (index : Nat) (within : index < stocks.length) :
    QProb.Equiv ((multicolourDepletingDistro 1 stocks (by omega)).pmf [index])
      ⟨stocks.getD index 0, stocks.sum, positive⟩ := by
  have single := multicolourDepleting_word_pmf stocks [index] (by
    intro colour member
    have same := List.mem_singleton.mp member
    subst colour
    exact within) (by simp only [List.length_cons, List.length_nil]; omega)
  have zero : jointFalling (List.replicate stocks.length 0) (stocks.modify index (fun stock => stock - 1)) = 1 := by
    simpa only [List.length_modify] using jointFalling_zeroOrders (stocks.modify index (fun stock => stock - 1))
  have kernel : jointFalling (colourCounts stocks.length [index]) stocks = stocks.getD index 0 := by
    simp only [colourCounts]
    rw [jointFalling_increment stocks _ (by rw [List.length_replicate]) index within, zero, Nat.mul_one]
  simpa only [kernel, fallingFactorial, Nat.mul_one] using single

end Thesis.Probability.Distros
