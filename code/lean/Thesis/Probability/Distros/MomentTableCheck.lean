import Thesis.Probability.Distros.FactorialMomentRealization

namespace Thesis.Probability.Distros

/-- A finite scan either certifies all listed masses or exhibits an actual
negative cell. Its witnesses are computed, without choosing a representative. -/
inductive FiniteMassCheck (cells : List A) (mass : A → SignedRatio) where
  | nonnegative (proof : ∀ cell ∈ cells, SignedRatio.Nonnegative (mass cell))
  | negative (cell : A) (member : cell ∈ cells) (proof : (mass cell).num < 0)

def checkFiniteMasses (cells : List A) (mass : A → SignedRatio) : FiniteMassCheck cells mass :=
  match cells with
  | [] => .nonnegative (by intro cell member; exact False.elim (List.not_mem_nil member))
  | cell :: cells =>
    if positive : 0 ≤ (mass cell).num then
      match checkFiniteMasses cells mass with
      | .nonnegative proof => .nonnegative (by
          intro other member
          rcases List.mem_cons.mp member with same | listed
          · subst other; exact positive
          · exact proof other listed)
      | .negative other member proof => .negative other (List.mem_cons_of_mem cell member) proof
    else .negative cell (List.mem_cons_self ..) (by omega)

/-- A returned obstruction is data with a kernel-checked explanation. -/
inductive FactorialTableObstruction (moments : Nat → QProb) (bound : Nat) where
  | negative (value : Nat) (within : value ≤ bound)
      (proof : (inverseFactorialTable moments bound value).num < 0)
  | unnormalized (proof : ¬ SignedRatio.Equiv
      (SignedRatio.listSum ((List.range (bound + 1)).map (inverseFactorialTable moments bound))) SignedRatio.one)

theorem FactorialTableObstruction.not_valid {moments : Nat → QProb} {bound : Nat}
    (obstruction : FactorialTableObstruction moments bound) : ¬ FactorialMomentTableValid moments bound := by
  intro valid
  cases obstruction with
  | negative value within negative => have nonnegative := valid.1 value within; change 0 ≤ _ at nonnegative; omega
  | unnormalized proof => exact proof valid.2

theorem FactorialTableObstruction.not_realizable {moments : Nat → QProb} {bound : Nat}
    (obstruction : FactorialTableObstruction moments bound) :
    ¬ ∃ μ : Distro Nat, μ.AlmostSurely (fun value => value ≤ bound) ∧
      ∀ order, order ≤ bound → QProb.Equiv (factorialMoment (⟨μ, id⟩ : NatDistro Nat) order) (moments order) :=
  fun law => obstruction.not_valid ((factorialMomentTable_realizable_iff moments bound).mpr law)

/-- The successful output includes the actual law and all required proofs. -/
structure FactorialTableRealization (moments : Nat → QProb) (bound : Nat) where
  distro : Distro Nat
  bounded : distro.AlmostSurely (fun value => value ≤ bound)
  momentsAgree : ∀ order, order ≤ bound → QProb.Equiv
    (factorialMoment (⟨distro, id⟩ : NatDistro Nat) order) (moments order)
  retains : ∀ value, value ≤ bound → ∃ weight, (value, weight) ∈ distro.record.atoms

/-- Executable complete decision procedure. A success retains every grid
cell, including zero masses; a failure gives a concrete checked obstruction. -/
def checkFactorialMomentTable (moments : Nat → QProb) (bound : Nat) :
    Sum (FactorialTableRealization moments bound) (FactorialTableObstruction moments bound) :=
  match checkFiniteMasses (List.range (bound + 1)) (inverseFactorialTable moments bound) with
  | .negative value member proof => .inr (.negative value (by have upper := List.mem_range.mp member; omega) proof)
  | .nonnegative proof =>
    if normalized : SignedRatio.Equiv
        (SignedRatio.listSum ((List.range (bound + 1)).map (inverseFactorialTable moments bound))) SignedRatio.one then
      let valid : FactorialMomentTableValid moments bound :=
        ⟨fun value within => proof value (List.mem_range.mpr (Nat.lt_succ_of_le within)), normalized⟩
      .inl ⟨(realizedFactorialDistro moments bound valid).distro,
        realizedFactorialDistro_bounded moments bound valid, realizedFactorialDistro_moments moments bound valid, realizedFactorialDistro_retains moments bound valid⟩
    else .inr (.unnormalized normalized)

/-- Success is equivalent to validity; neither a valid table nor an
invalid one can be classified incorrectly by the executable procedure. -/
theorem checkFactorialMomentTable_success_iff (moments : Nat → QProb) (bound : Nat) :
    (match checkFactorialMomentTable moments bound with | .inl _ => True | .inr _ => False) ↔
      FactorialMomentTableValid moments bound := by
  cases result : checkFactorialMomentTable moments bound with
  | inl law =>
      constructor
      · intro _
        exact factorialMomentTable_valid_of_moments (⟨law.distro, id⟩ : NatDistro Nat) moments bound law.bounded law.momentsAgree
      · intro _; trivial
  | inr obstruction =>
      constructor
      · intro impossible; exact False.elim impossible
      · intro valid; exact False.elim (obstruction.not_valid valid)

end Thesis.Probability.Distros
