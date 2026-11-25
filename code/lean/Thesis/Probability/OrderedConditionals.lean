import Thesis.Probability.Construction
import Thesis.Probability.FiniteRecordAlmostSure

namespace Thesis.Probability.FiniteProbRecord

/-!
An ordered reconstruction compares one earlier-history cylinder at a time.
Equal history probabilities and equal supported next-value conditionals
determine the extended joint. A null history is handled by monotonicity,
never by inventing a conditional. The two records may have different
denominators, repeated labels and explicitly listed zero-weight atoms.
-/

/-- Ordinary urn and record support agree independently of repeated labels. -/
theorem ofUrn_support_iff (urn : UrnProb Ω) (evidence : Event Ω) :
    (ofUrn urn).EventPositive evidence ↔ 0 < urn.probNum evidence :=
  QProb.equiv_num_pos_iff (ofUrn_agrees urn evidence)

theorem conditionOn_ofUrn_equiv (urn : UrnProb Ω) (evidence event : Event Ω)
    (supported : (ofUrn urn).EventPositive evidence)
    (urnSupported : 0 < urn.probNum evidence) :
    QProb.Equiv (((ofUrn urn).conditionOn evidence supported).probVal event)
      (urn.condVal event evidence urnSupported) := by
  refine QProb.equiv_trans ((ofUrn urn).conditionOn_probVal evidence event supported) ?_
  refine QProb.equiv_trans (QProb.div_congr
    (ofUrn_agrees urn (fun sample => evidence sample && event sample))
    (ofUrn_agrees urn evidence) supported urnSupported) ?_
  have commute : urn.probNum (fun sample => evidence sample && event sample) =
      urn.probNum (inter event evidence) := count_congr (fun _ => Bool.and_comm _ _)
  simp only [QProb.Equiv, QProb.div, UrnProb.probVal, UrnProb.condVal]
  rw [commute]
  ac_rfl

/-- Zero-weight exceptions to a sure event are harmless. Supported evidence
retains a constant outcome; the false constant gives a defined zero. -/
theorem conditional_constant_on_full_event (record : FiniteProbRecord Ω)
    (sure evidence event : Event Ω) (value : Bool)
    (full : QProb.Equiv (record.probVal sure) QProb.one)
    (constant : ∀ sample, sure sample = true → event sample = value)
    (supported : record.EventPositive evidence) :
    QProb.Equiv ((record.conditionOn evidence supported).probVal event)
      (if value then QProb.one else QProb.zero) := by
  have fullMass : eventMass record.atoms sure = totalMass record.atoms := by
    have total : eventMass record.atoms sure = record.den := by
      simpa only [QProb.Equiv, probVal, QProb.one, Nat.mul_one, Nat.one_mul] using full
    exact total.trans record.total_mass.symm
  have same := eventMass_congr_on_full_event record.atoms sure
    (fun sample => evidence sample && event sample) (fun sample => evidence sample && value)
    fullMass (fun sample selected => congrArg (fun bit => evidence sample && bit) (constant sample selected))
  simp only [conditionOn, probVal, eventMass_filter_event, QProb.Equiv]
  rw [same]
  cases value <;> simp [QProb.one, QProb.zero, eventMass_false]

/-- A proposed transition value determines the joint without a positivity
assumption. Supported evidence uses ordinary division cancellation; null
evidence has only null extensions. Thus this lemma never requests a
conditional on an impossible history. -/
theorem joint_equiv_mul_of_conditionals (record : FiniteProbRecord Ω)
    (evidence event : Event Ω) (value : QProb)
    (conditional : ∀ supported : record.EventPositive evidence,
      QProb.Equiv ((record.conditionOn evidence supported).probVal event) value) :
    QProb.Equiv (record.probVal (fun sample => evidence sample && event sample))
      (QProb.mul (record.probVal evidence) value) := by
  by_cases positive : record.EventPositive evidence
  · have quotient := QProb.equiv_trans
      (QProb.equiv_symm (record.conditionOn_probVal evidence event positive)) (conditional positive)
    exact QProb.equiv_trans
      (QProb.equiv_symm (QProb.mul_div_cancel _ (record.probVal evidence) positive))
      (QProb.mul_congr (QProb.equiv_refl _) quotient)
  · have nullEvidence : eventMass record.atoms evidence = 0 := Nat.eq_zero_of_not_pos positive
    have bound := eventMass_mono record.atoms
      (fun sample => evidence sample && event sample) evidence
      (fun _ selected => (Bool.and_eq_true_iff.mp selected).1)
    have nullJoint : eventMass record.atoms (fun sample => evidence sample && event sample) = 0 := by omega
    simp only [probVal, QProb.Equiv, QProb.mul, nullJoint, nullEvidence, Nat.zero_mul]

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

namespace Thesis.Probability.UrnProb

/-- Urn conditionals equal division of the ordinary joint and evidence
probabilities, extensionally in the unreduced rational presentations. -/
theorem condVal_as_div (urn : UrnProb Ω) (event evidence : Event Ω)
    (supported : 0 < urn.probNum evidence) :
    QProb.Equiv (urn.condVal event evidence supported)
      (QProb.div (urn.probVal (inter event evidence)) (urn.probVal evidence) supported) := by
  simp only [QProb.Equiv, condVal, probVal, QProb.div]
  ac_rfl

/-- Equal full laws preserve all supported conditionals. Outcome positivity
and matched denominator presentations are unnecessary. -/
theorem condVal_congr_of_probVal (left right : UrnProb Ω)
    (agree : ∀ event, QProb.Equiv (left.probVal event) (right.probVal event))
    (event evidence : Event Ω) (leftSupported : 0 < left.probNum evidence)
    (rightSupported : 0 < right.probNum evidence) :
    QProb.Equiv (left.condVal event evidence leftSupported) (right.condVal event evidence rightSupported) :=
  QProb.equiv_trans (left.condVal_as_div event evidence leftSupported)
    (QProb.equiv_trans (QProb.div_congr (agree (inter event evidence)) (agree evidence)
      leftSupported rightSupported) (QProb.equiv_symm (right.condVal_as_div event evidence rightSupported)))

end Thesis.Probability.UrnProb

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

/-- Denominator-free transitions give a full singleton factorization.
The product follows the supplied order. No conditional, positivity or
global factorization hypothesis is hidden in this elementary induction. -/
theorem singleton_factorization
    (nodes : List (Fin n)) (complete : ∀ node, node ∈ nodes)
    (record : FiniteProbRecord (FiniteProduct.Assignment n Value))
    (reference : FiniteProduct.Assignment n Value) (factor : Fin n → QProb)
    (transition : ∀ (past : List (Fin n)) (node : Fin n) (future : List (Fin n)),
      nodes = past ++ node :: future →
      QProb.Equiv
        (record.probVal (fun sample => history past reference sample && coordinate node reference sample))
        (QProb.mul (record.probVal (history past reference)) (factor node))) :
    QProb.Equiv (record.probVal (FiniteProbRecord.singletonEvent reference))
      (nodes.foldl (fun product node => QProb.mul product (factor node)) QProb.one) := by
  have advance : ∀ (todo past : List (Fin n)), nodes = past ++ todo →
      QProb.Equiv (record.probVal (history past reference))
        (past.foldl (fun product node => QProb.mul product (factor node)) QProb.one) →
      QProb.Equiv (record.probVal (history nodes reference))
        (nodes.foldl (fun product node => QProb.mul product (factor node)) QProb.one) := by
    intro todo
    induction todo with
    | nil =>
        intro past same equal
        have sameNodes : nodes = past := by simpa only [List.append_nil] using same
        simpa only [sameNodes] using equal
    | cons node todo inductionHypothesis =>
        intro past same equal
        have next : QProb.Equiv (record.probVal (history (past ++ [node]) reference))
            ((past ++ [node]).foldl (fun product node => QProb.mul product (factor node)) QProb.one) := by
          rw [history_snoc]
          simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
            QProb.equiv_trans (transition past node todo same)
              (QProb.mul_congr equal (QProb.equiv_refl (factor node)))
        have sameNext : nodes = (past ++ [node]) ++ todo := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using same
        exact inductionHypothesis (past ++ [node]) sameNext next
  have whole := advance nodes [] rfl record.normalization
  simpa only [history_complete nodes complete reference] using whole

end Thesis.Probability.OrderedHistory
