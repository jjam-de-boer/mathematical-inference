import Thesis.CausalTransport.CausalAbstractionInverse
import Thesis.Examples.CausalAbstractionSynthesis

/-!
# What an exact AND collapse reveals about its two causes

Keep just the two Boolean roots of the AND fixture. A measured AND success
probability of one quarter fixes the joint event that both roots are true.
Each individual root has a range from one quarter to one: the unused
coarse mass can be assigned to either value of that root. The solver must
produce both endpoints as actual fine models. Forcing both roots to true
can never give a coarse false value, even with arbitrary shared noise.
-/

namespace Thesis.Examples.CausalAbstractionInverse

open Probability Causality
open Causality.CausalAbstractionSynthesis (Aggregation interventionDecidableEq)
open Causality.CausalAbstractionInverse
open Thesis.Examples.CausalAbstractionSynthesis (compactSignature compactDoTrue)

def fine : ObservedSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed _ _ := false
  directed_earlier := by intro _ _ edge; cases edge

def bothTrue (state : fine.Assignment) : Bool := state (0 : Fin 2) && state (1 : Fin 2)

def andAggregation : Aggregation fine compactSignature where
  cluster _ _ := true
  cluster_nonempty _ := ⟨(0 : Fin 2), rfl⟩
  cluster_disjoint first second different := by
    have same : first = second := Fin.ext (by
      have left : first.val < 1 := first.isLt
      have right : second.val < 1 := second.isLt
      omega)
    exact False.elim (different same)
  assignmentMap state _ := bothTrue state
  coordinate_local _ first second agree := by
    unfold bothTrue
    rw [agree (0 : Fin 2) rfl, agree (1 : Fin 2) rfl]

def bothForced : HardIntervention fine where
  value _ := some true

def andOmega (action : HardIntervention fine) : Option (HardIntervention compactSignature) :=
  if action = .empty fine then some (.empty compactSignature)
  else if action = bothForced then some compactDoTrue
  else none

def observed : FiniteProbRecord compactSignature.Assignment where
  atoms := [(fun _ => false, 3), (fun _ => true, 1)]
  den := 4
  den_pos := by decide
  total_mass := rfl

def deterministic (value : Bool) : FiniteProbRecord compactSignature.Assignment where
  atoms := [(fun _ => value, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

def spec : Specification fine compactSignature where
  aggregation := andAggregation
  omega := andOmega
  required := [.empty compactSignature, compactDoTrue]
  measurements := [⟨.empty compactSignature, observed⟩, ⟨compactDoTrue, deterministic true⟩]

theorem protocol_valid : spec.Valid := by decide +kernel

/-- The model-independent point answer for the event represented directly
by the macro outcome retains the exact observational value. -/
def pointAnswer : Bool :=
  match spec.solve (.empty fine) bothTrue with
  | .point _ sharp _ => decide (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩)
  | _ => false

theorem point_answer_executes : pointAnswer = true := by decide +kernel

/-- Projecting to AND leaves both attaining fine models accessible through
the interval branch of the actual solver. -/
def rootRange : Bool :=
  match spec.solve (.empty fine) (fun state => state (0 : Fin 2)) with
  | .interval _ sharp _ => decide
      (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩ ∧ SignedRatio.Equiv sharp.upper .one)
  | _ => false

theorem root_range_executes : rootRange = true := by decide +kernel

def conflicting : Specification fine compactSignature :=
  { spec with measurements := [⟨.empty compactSignature, observed⟩,
      ⟨compactDoTrue, deterministic false⟩] }

def incompatibleAnswer : Bool :=
  match conflicting.solve (.empty fine) bothTrue with
  | .incompatible _ _ => true
  | _ => false

theorem incompatible_measurement_refuted : incompatibleAnswer = true := by decide +kernel

def missingObservation : Specification fine compactSignature :=
  { spec with measurements := [⟨compactDoTrue, deterministic true⟩] }

theorem missing_measurement_rejected :
    (match missingObservation.solve (.empty fine) bothTrue with
    | .invalid _ => true
    | _ => false) = true := by decide +kernel

end Thesis.Examples.CausalAbstractionInverse
