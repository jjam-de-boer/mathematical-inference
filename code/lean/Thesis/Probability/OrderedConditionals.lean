import Thesis.Probability.Construction

namespace Thesis.Probability.FiniteProbRecord

/-!
An ordered reconstruction compares one earlier-history cylinder at a time.
Equal history probabilities and equal supported next-value conditionals
determine the extended joint. A null history is handled by monotonicity,
never by inventing a conditional. The two records may have different
denominators, repeated labels and explicitly listed zero-weight atoms.
-/

theorem joint_equiv_of_evidence_and_conditionals
    (left right : FiniteProbRecord Ω) (evidence event : Event Ω)
    (marginal : QProb.Equiv (left.probVal evidence) (right.probVal evidence))
    (conditionals : ∀ (leftPositive : left.EventPositive evidence)
      (rightPositive : right.EventPositive evidence),
      QProb.Equiv ((left.conditionOn evidence leftPositive).probVal event)
        ((right.conditionOn evidence rightPositive).probVal event)) :
    QProb.Equiv (left.probVal (fun sample => evidence sample && event sample))
      (right.probVal (fun sample => evidence sample && event sample)) := by
  by_cases leftPositive : left.EventPositive evidence
  · have rightPositive : right.EventPositive evidence :=
      (QProb.equiv_num_pos_iff marginal).mp leftPositive
    have conditional := conditionals leftPositive rightPositive
    change eventMass left.atoms evidence * right.den =
      eventMass right.atoms evidence * left.den at marginal
    change eventMass (left.atoms.filter (fun atom => evidence atom.1)) event *
        eventMass right.atoms evidence =
      eventMass (right.atoms.filter (fun atom => evidence atom.1)) event *
        eventMass left.atoms evidence at conditional
    rw [eventMass_filter_event, eventMass_filter_event] at conditional
    change eventMass left.atoms (fun sample => evidence sample && event sample) * right.den =
      eventMass right.atoms (fun sample => evidence sample && event sample) * left.den
    apply Nat.eq_of_mul_eq_mul_right rightPositive
    calc
      _ = (eventMass left.atoms (fun sample => evidence sample && event sample) *
          eventMass right.atoms evidence) * right.den := by ac_rfl
      _ = (eventMass right.atoms (fun sample => evidence sample && event sample) *
          eventMass left.atoms evidence) * right.den := by rw [conditional]
      _ = eventMass right.atoms (fun sample => evidence sample && event sample) *
          (eventMass left.atoms evidence * right.den) := by ac_rfl
      _ = eventMass right.atoms (fun sample => evidence sample && event sample) *
          (eventMass right.atoms evidence * left.den) := by rw [marginal]
      _ = _ := by ac_rfl
  · have rightNotPositive : ¬ right.EventPositive evidence := by
      intro positive
      exact leftPositive ((QProb.equiv_num_pos_iff marginal).mpr positive)
    have leftZero : eventMass left.atoms evidence = 0 := Nat.eq_zero_of_not_pos leftPositive
    have rightZero : eventMass right.atoms evidence = 0 := Nat.eq_zero_of_not_pos rightNotPositive
    have selected : ∀ sample, (evidence sample && event sample) = true → evidence sample = true :=
      fun _ both => (Bool.and_eq_true_iff.mp both).1
    have leftBound := eventMass_mono left.atoms _ _ selected
    have rightBound := eventMass_mono right.atoms _ _ selected
    have leftJointZero : eventMass left.atoms (fun sample => evidence sample && event sample) = 0 := by omega
    have rightJointZero : eventMass right.atoms (fun sample => evidence sample && event sample) = 0 := by omega
    change eventMass left.atoms (fun sample => evidence sample && event sample) * right.den =
      eventMass right.atoms (fun sample => evidence sample && event sample) * left.den
    rw [leftJointZero, rightJointZero]
    simp only [Nat.zero_mul]

end Thesis.Probability.FiniteProbRecord

namespace Thesis.Probability.OrderedHistory

universe u
variable {n : Nat} {Value : Fin n → Type u}
variable [coordinateEq : (node : Fin n) → DecidableEq (Value node)]

private instance valueDecidableEq (node : Fin n) : DecidableEq (Value node) := coordinateEq node
private instance assignmentDecidableEq : DecidableEq (FiniteProduct.Assignment n Value) :=
  FiniteProduct.assignmentDecidableEq n Value coordinateEq

def coordinate (node : Fin n) (reference : FiniteProduct.Assignment n Value) :
    Event (FiniteProduct.Assignment n Value) := fun sample => decide (sample node = reference node)

/-- An actual earlier history fixes every listed coordinate, including
unrelated predecessors. It is not merely the list of graph ancestors. -/
def history (nodes : List (Fin n)) (reference : FiniteProduct.Assignment n Value) :
    Event (FiniteProduct.Assignment n Value) := fun sample => nodes.all (fun node => coordinate node reference sample)

theorem history_snoc (nodes : List (Fin n)) (node : Fin n)
    (reference : FiniteProduct.Assignment n Value) :
    history (nodes ++ [node]) reference =
      fun sample => history nodes reference sample && coordinate node reference sample := by
  funext sample
  simp [history, List.all_append]

theorem history_complete (nodes : List (Fin n)) (complete : ∀ node, node ∈ nodes)
    (reference : FiniteProduct.Assignment n Value) :
    history nodes reference = FiniteProbRecord.singletonEvent reference := by
  funext sample
  apply Bool.eq_iff_iff.mpr
  simp only [history, List.all_eq_true, coordinate, decide_eq_true_eq, FiniteProbRecord.singletonEvent]
  constructor
  · intro equal
    funext node
    exact equal node (complete node)
  · intro equal node _member
    exact congrFun equal node

/-- Compare the next-value conditional at each actual past of the supplied
coordinate order. Only supported conditionals are mentioned. No shared
support of full assignments and no positive joint-cell assumption occurs. -/
def ForwardAgreement (nodes : List (Fin n))
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value)) : Prop :=
  ∀ (past : List (Fin n)) (node : Fin n) (suffix : List (Fin n)),
    nodes = past ++ node :: suffix → ∀ reference,
    ∀ (leftPositive : left.EventPositive (history past reference))
      (rightPositive : right.EventPositive (history past reference)),
      QProb.Equiv
        ((left.conditionOn (history past reference) leftPositive).probVal (coordinate node reference))
        ((right.conditionOn (history past reference) rightPositive).probVal (coordinate node reference))

/-- Normalization starts the induction. At each step equal supported
conditionals extend equal past probabilities; a null past has only null
extensions. Hence one common sequence of forward conditional laws determines
the entire finite law, including explicit zero-weight presentations. -/
theorem probVal_equiv_of_forwardAgreement
    (nodes : List (Fin n)) (complete : ∀ node, node ∈ nodes)
    (left right : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (agreement : ForwardAgreement nodes left right)
    (values : (node : Fin n) → List (Value node))
    (valuesComplete : ∀ node value, value ∈ values node)
    (event : Event (FiniteProduct.Assignment n Value)) :
    QProb.Equiv (left.probVal event) (right.probVal event) := by
  have advance : ∀ (todo past : List (Fin n)), nodes = past ++ todo →
      (∀ reference, QProb.Equiv (left.probVal (history past reference))
        (right.probVal (history past reference))) →
      ∀ reference, QProb.Equiv (left.probVal (history nodes reference))
        (right.probVal (history nodes reference)) := by
    intro todo
    induction todo with
    | nil =>
        intro past same equal reference
        have sameNodes : nodes = past := by simpa only [List.append_nil] using same
        rw [sameNodes]
        exact equal reference
    | cons node todo inductionHypothesis =>
        intro past same equal reference
        have next : ∀ current, QProb.Equiv
            (left.probVal (history (past ++ [node]) current))
            (right.probVal (history (past ++ [node]) current)) := by
          intro current
          rw [history_snoc]
          exact FiniteProbRecord.joint_equiv_of_evidence_and_conditionals left right
            (history past current) (coordinate node current) (equal current)
            (agreement past node todo same current)
        have sameNext : nodes = (past ++ [node]) ++ todo := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using same
        exact inductionHypothesis (past ++ [node]) sameNext next reference
  have initial : ∀ reference, QProb.Equiv
      (left.probVal (history [] reference)) (right.probVal (history [] reference)) := by
    intro reference
    exact QProb.equiv_trans left.normalization (QProb.equiv_symm right.normalization)
  have full := advance nodes [] (by rfl) initial
  have singletons : ∀ reference, QProb.Equiv
      (left.probVal (FiniteProbRecord.singletonEvent reference))
      (right.probVal (FiniteProbRecord.singletonEvent reference)) := by
    intro reference
    simpa only [history_complete nodes complete reference] using full reference
  let labels := deduplicate (FiniteProduct.enumeration n Value values)
  exact left.probVal_extensional_of_singletons right labels (deduplicate_nodup _)
    (fun reference => (mem_deduplicate _ _).mpr (FiniteProduct.enumeration_complete _ _ _ valuesComplete reference))
    singletons event

end Thesis.Probability.OrderedHistory
