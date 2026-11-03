import Thesis.CausalTransport.NativeQueryDemand

namespace Thesis.Causality.NativeSupportGuard

open Probability NativeDemandTyping

/-!
# A checked guard for one observable support/reference cell

The reference is encoded by its position in the existing complete finite
dictionary. No representative or inverse is selected from an existence
proof, and no declared null reference is replaced by a default value.

The resulting one-row guard uses the existing guard language and checker.
Its acceptance domain is exactly the supplied support pattern and reference.
Checking it still requires the demand in every matching causal profile.
Unlike the optional compiled guard, constructing this row does not require
the observed pattern to occur in the supplied profile catalogue. An empty
catalogue can check the row vacuously, but supplies no original-model coverage
or source-support witness for a subsequent soundness application.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

def referenceCode (fixed : S.Assignment) : Nat := ((referenceWitness S).encode fixed).val

theorem assignment_referenceCode (fixed : S.Assignment) :
    ProbabilityCode.assignment S (referenceCode fixed) = some fixed := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨((referenceWitness S).encode fixed).isLt, (referenceWitness S).decode_encode fixed⟩

def pointCell (observed : List Bool) (fixed : S.Assignment) : Cell := ⟨observed, referenceCode fixed⟩

def point (observed : List Bool) (fixed : S.Assignment) : Code := [pointCell observed fixed]

theorem point_accepts_iff (observed : List Bool) (fixed : S.Assignment)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    accepts (point observed fixed) record reference = true ↔
      observed = pattern S record ∧ fixed = reference := by
  simp only [accepts, point, List.any_cons, List.any_nil, Bool.or_false, pointCell, Cell.accepts,
    assignment_referenceCode, Bool.and_eq_true_iff, decide_eq_true_eq]

theorem point_accepts_self (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment) :
    accepts (point (pattern S record) fixed) record fixed = true :=
  (point_accepts_iff ..).mpr ⟨rfl, rfl⟩

/-- Universal checking of the one supplied row, including all matching
profiles. This is the original Boolean guard checker, not a new interface. -/
theorem point_checked_iff (profiles : List (NativeTemplateInstance P)) (demand : Demand S)
    (observed : List Bool) (fixed : S.Assignment) :
    check profiles demand (point observed fixed) = true ↔
      ∀ entry, entry ∈ profiles → observed = pattern S entry.model.observationalDist → demand P entry.model fixed = true := by
  simp only [check, point, List.all_cons, List.all_nil, Bool.and_true, checkCell, pointCell,
    assignment_referenceCode, List.all_eq_true]
  constructor
  · intro checked entry listed matched
    simpa only [if_pos matched] using checked entry listed
  · intro checked entry listed
    split
    · next matched => exact checked entry listed matched
    · rfl

end Thesis.Causality.NativeSupportGuard
