import Thesis.Causality.PetriCharacteristicAnalysis

namespace Thesis.Causality.Examples.PetriCharacteristic

open PetriNet Thesis.Causality.PetriCharacteristic

/-!
# Characteristic equations and the firing-order boundary

For the ordinary net below, a signed balance from zero to one has a
solution. Coverability also succeeds by creating two tokens. Exact
reachability fails because all enabled nonempty executions first reach
two tokens and never decrease. Making the blocked edge a designated
bridge is different: the bridge equations retain its full source guard.
The positive bridge begins with enough tokens and has an unspecified
final counter in the second segment.
-/

private def tokens (count : Nat) : Marking 1 := fun _ => count

def overshoot : Thesis.Causality.PetriNet 1 2 where
  consume := fun edge _ => if edge = 0 then 2 else 0
  produce := fun edge _ => if edge = 0 then 3 else 2

def overshootQuery := PetriExactEndpoints.ordinaryQuery overshoot (fun _ => some 0) (fun _ => some 1)

def overshootSequence := ofEndpointQuery overshootQuery

/-- One actual balance row and two count columns remain after eliminating
the fixed endpoints and the one-state tautological control row. -/
example : IntegerEquations.System 1 2 := overshootSequence.system

theorem overshoot_equations_feasible : overshootSequence.system.isFeasible = true := by
  decide +kernel

theorem one_coverable : overshoot.Coverable (tokens 0) (tokens 1) :=
  ⟨tokens 2, ⟨[1], (check_exact overshoot _ _ _).mp (by decide +kernel)⟩, fun _ => Nat.le_succ 1⟩

private theorem never_decreases {before after : Marking 1} {word : List (Fin 2)}
    (execution : overshoot.Execution before word after) : Below before after := by
  induction execution with
  | nil => exact fun _ => Nat.le_refl _
  | @cons before middle after edge rest fired remaining ih =>
      intro place
      have enabled := fired.1 place
      have actual := congrFun fired.2 place
      change overshoot.consume edge place ≤ before place at enabled
      change middle place = before place - overshoot.consume edge place + overshoot.produce edge place at actual
      have bound := ih place
      change middle place ≤ after place at bound
      by_cases first : edge = 0
      · simp only [overshoot, if_pos first] at enabled actual
        omega
      · simp only [overshoot, if_neg first] at enabled actual
        omega

private theorem from_zero {after : Marking 1} {word : List (Fin 2)}
    (execution : overshoot.Execution (tokens 0) word after) : after 0 = 0 ∨ 2 ≤ after 0 := by
  cases execution with
  | nil => exact Or.inl rfl
  | @cons _ middle _ edge rest fired remaining =>
      have enabled := fired.1 (0 : Fin 1)
      have actual := congrFun fired.2 (0 : Fin 1)
      change overshoot.consume edge 0 ≤ 0 at enabled
      change middle 0 = 0 - overshoot.consume edge 0 + overshoot.produce edge 0 at actual
      have bound := never_decreases remaining (0 : Fin 1)
      change middle 0 ≤ after 0 at bound
      by_cases first : edge = 0
      · simp only [overshoot, if_pos first] at enabled
        exact False.elim (by omega)
      · simp only [overshoot, if_neg first] at actual
        exact Or.inr (by omega)

theorem one_not_reachable : ¬ overshoot.Reachable (tokens 0) (tokens 1) := by
  rintro ⟨word, execution⟩
  rcases from_zero execution with zero | tooMany
  · change 1 = 0 at zero
    omega
  · change 2 ≤ 1 at tooMany
    omega

private def controlled : ControlledPetriNet 1 1 2 := ⟨overshoot, fun _ => 0, fun _ => 0⟩

def bridgeSequence (source : Nat) : Sequence 1 1 2 1 where
  net := controlled
  segment := fun i =>
    if i = 0 then ⟨0, 0, fun _ => some source, fun _ => some source, fun _ => false⟩
    else ⟨0, 0, fun _ => some (source + 1), fun _ => none, fun _ => false⟩
  bridge := fun _ => 0

theorem blocked_bridge_refuted : ¬ ∃ values, (bridgeSequence 0).Model values := by
  rintro ⟨values, model⟩
  have enabled := ((Sequence.Model.bridgeFires (bridgeSequence 0) model 0).2.2.1 (0 : Fin 1))
  change 2 ≤ 0 at enabled
  omega

theorem enabled_bridge_feasible : ∃ values, (bridgeSequence 2).system.Satisfies values := by
  apply (Sequence.model_iff_feasible (sequence := bridgeSequence 2)).mp
  refine ⟨fun name => match name with | .exit _ _ => 3 | _ => 0, ?_⟩
  constructor <;> decide +kernel

/-- With no counters or edges there is no token-balance obstruction.
Control flow must still reject changing the control state. -/
def noControlPath : Sequence 0 2 0 0 :=
  oneSegment ⟨⟨Fin.elim0, Fin.elim0⟩, Fin.elim0, Fin.elim0⟩
    ⟨0, 1, Fin.elim0, Fin.elim0, Fin.elim0⟩

theorem wrong_control_flow_refuted : noControlPath.system.isFeasible = false := by
  decide +kernel

end Thesis.Causality.Examples.PetriCharacteristic
