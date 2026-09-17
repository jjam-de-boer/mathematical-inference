import Thesis.Probability.Urn

namespace Thesis
namespace Probability

/-!
Finite common-denominator probability records.

The low-level `atoms` representation is a list of labelled natural weights.
It deliberately permits repeated labels: probabilities are obtained by adding
all weights of atoms whose label satisfies the Boolean event.  This makes
finite pushforwards, conditioning, and product constructions executable while
retaining extensional rational equality through `QProb.Equiv`.

The first namespace proves list-level mass identities.  The public
`FiniteProbRecord` structure below packages a nonempty total mass and its
normalisation proof.
-/

namespace FiniteProbRecord

/-- Total natural weight carried by a finite list of weighted atoms. -/
def totalMass : List (Ω × Nat) → Nat
  | [] => 0
  | (_, w) :: atoms => w + totalMass atoms

def eventMass : List (Ω × Nat) → Event Ω → Nat
  | [], _ => 0
  | (ω, w) :: atoms, E =>
      if E ω then w + eventMass atoms E else eventMass atoms E

theorem eventMass_congr (atoms : List (Ω × Nat)) (E F : Event Ω)
    (h : forall value, E value = F value) :
    eventMass atoms E = eventMass atoms F := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      cases atom with
      | mk value weight =>
          change
            (if E value then weight + eventMass atoms E else eventMass atoms E) =
              (if F value then weight + eventMass atoms F else eventMass atoms F)
          rw [h value, ih]

/-- Two-atom event mass is the sum of the included weights. -/
theorem eventMass_pair (x y : Ω) (wx wy : Nat) (event : Event Ω) :
    eventMass [(x, wx), (y, wy)] event =
      (if event x then wx else 0) + (if event y then wy else 0) := by
  cases hx : event x <;> cases hy : event y <;> simp [eventMass, hx, hy]

/-- Mass is monotone in the Boolean event: more outcomes cannot lose weight. -/
theorem eventMass_mono (atoms : List (Ω × Nat)) (E F : Event Ω)
    (h : forall value, E value = true -> F value = true) :
    eventMass atoms E ≤ eventMass atoms F := by
  induction atoms with
  | nil => exact Nat.le_refl 0
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases hE : E value
      · cases hF : F value
        · simp [eventMass, hE, hF]
          exact ih
        · simp [eventMass, hE, hF]
          exact Nat.le_trans ih (Nat.le_add_left (eventMass atoms F) weight)
      · have hF : F value = true := h value hE
        simp [eventMass, hE, hF]
        exact ih

/-- Expand a weighted list into its equivalent unit-cell urn presentation. -/
def expand : List (Ω × Nat) → List Ω
  | [] => []
  | (ω, w) :: atoms => List.replicate w ω ++ expand atoms

theorem length_expand (atoms : List (Ω × Nat)) :
    (expand atoms).length = totalMass atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons a atoms ih =>
      cases a with
      | mk ω w =>
          simp [expand, totalMass, ih]

/-- Count a Boolean event over repeated copies without using choice. -/
theorem countP_replicate_constructive (count : Nat) (value : Ω)
    (E : Event Ω) :
    List.countP E (List.replicate count value) =
      if E value then count else 0 := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ, List.countP_cons, ih]
      cases E value <;> simp

theorem count_expand (atoms : List (Ω × Nat)) (E : Event Ω) :
    count (expand atoms) E = eventMass atoms E := by
  induction atoms with
  | nil =>
      simp [expand, eventMass, count]
  | cons a atoms ih =>
      cases a with
      | mk ω w =>
          simp [expand, eventMass, count, List.countP_append,
            countP_replicate_constructive]
          have ihc :
              List.countP E (expand atoms) = eventMass atoms E := by
            simpa [count] using ih
          rw [ihc]
          cases E ω <;> simp

theorem totalMass_unit (xs : List Ω) :
    totalMass (xs.map (fun ω => (ω, 1))) = xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [totalMass, ih]
      omega

theorem eventMass_unit (xs : List Ω) (E : Event Ω) :
    eventMass (xs.map (fun ω => (ω, 1))) E = count xs E := by
  induction xs with
  | nil =>
      simp [eventMass, count]
  | cons x xs ih =>
      change
        (if E x then
            1 + eventMass (xs.map (fun ω => (ω, 1))) E
          else
            eventMass (xs.map (fun ω => (ω, 1))) E) =
          List.countP E (x :: xs)
      rw [List.countP_cons, ih]
      cases E x <;> simp [count]
      omega

theorem eventMass_top (atoms : List (Ω × Nat)) :
    eventMass atoms topEvent = totalMass atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      simp [eventMass, totalMass, topEvent, ih]

/-- An event cannot carry more mass than the complete weighted support. -/
theorem eventMass_le_totalMass (atoms : List (Ω × Nat)) (E : Event Ω) :
    eventMass atoms E ≤ totalMass atoms := by
  induction atoms with
  | nil => exact Nat.le_refl 0
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases h : E value <;>
        simp [eventMass, totalMass, h] <;> omega

theorem totalMass_filter_event (atoms : List (Ω × Nat))
    (evidence : Event Ω) :
    totalMass (atoms.filter (fun atom => evidence atom.1)) =
      eventMass atoms evidence := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases h : evidence ω <;>
        simp [totalMass, eventMass, h, ih]

theorem eventMass_filter_event (atoms : List (Ω × Nat))
    (evidence event : Event Ω) :
    eventMass (atoms.filter (fun atom => evidence atom.1)) event =
      eventMass atoms (fun ω => evidence ω && event ω) := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases hEvidence : evidence ω <;> cases hEvent : event ω <;>
        simp [eventMass, hEvidence, hEvent, ih]

theorem totalMass_map_labels (atoms : List (Ω × Nat)) (f : Ω → X) :
    totalMass (atoms.map (fun atom => (f atom.1, atom.2))) =
      totalMass atoms := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      change weight +
          totalMass (atoms.map (fun atom => (f atom.1, atom.2))) =
        weight + totalMass atoms
      exact congrArg (fun mass => weight + mass) ih

theorem eventMass_map_labels (atoms : List (Ω × Nat))
    (f : Ω → X) (event : Event X) :
    eventMass (atoms.map (fun atom => (f atom.1, atom.2))) event =
      eventMass atoms (fun ω => event (f ω)) := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases h : event (f ω) <;>
        simp [eventMass, h, ih]

theorem eventMass_scale (atoms : List (Ω × Nat)) (factor : Nat)
    (event : Event Ω) :
    eventMass
        (atoms.map (fun atom => (atom.1, factor * atom.2))) event =
      factor * eventMass atoms event := by
  induction atoms with
  | nil =>
      simp [eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨ω, weight⟩
      cases h : event ω <;>
        simp [eventMass, h, ih, Nat.mul_add]

theorem totalMass_append (left right : List (Ω × Nat)) :
    totalMass (left ++ right) = totalMass left + totalMass right := by
  induction left with
  | nil =>
      simp [totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      simp [totalMass, ih, Nat.add_assoc]

theorem eventMass_append (left right : List (Ω × Nat))
    (event : Event Ω) :
    eventMass (left ++ right) event =
      eventMass left event + eventMass right event := by
  induction left with
  | nil =>
      simp [eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases h : event value <;>
        simp [eventMass, h, ih, Nat.add_assoc]

theorem eventMass_false (atoms : List (Ω × Nat)) :
    eventMass atoms (fun _ => false) = 0 := by
  induction atoms with
  | nil =>
      rfl
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      simp [eventMass, ih]

theorem totalMass_map_weight (atoms : List (Ω × Nat))
    (label : Ω -> X) (factor : Nat) :
    totalMass (atoms.map (fun atom => (label atom.1, factor * atom.2))) =
      factor * totalMass atoms := by
  induction atoms with
  | nil =>
      simp [totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      simp [totalMass, ih, Nat.mul_add]

theorem eventMass_map_weight (atoms : List (Ω × Nat))
    (label : Ω -> X) (factor : Nat) (event : Event X) :
    eventMass (atoms.map (fun atom => (label atom.1, factor * atom.2))) event =
      factor * eventMass atoms (fun value => event (label value)) := by
  induction atoms with
  | nil =>
      simp [eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases h : event (label value) <;>
        simp [eventMass, h, ih, Nat.mul_add]

def weightedCartesian (left : List (Ω × Nat))
    (right : List (X × Nat)) : List ((Ω × X) × Nat) :=
  left.flatMap (fun leftAtom =>
    right.map (fun rightAtom =>
      ((leftAtom.1, rightAtom.1), leftAtom.2 * rightAtom.2)))

theorem totalMass_weightedCartesian (left : List (Ω × Nat))
    (right : List (X × Nat)) :
    totalMass (weightedCartesian left right) =
      totalMass left * totalMass right := by
  induction left with
  | nil =>
      simp [weightedCartesian, totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      change
        totalMass
            (right.map (fun rightAtom =>
              ((value, rightAtom.1), weight * rightAtom.2)) ++
              weightedCartesian atoms right) = _
      rw [totalMass_append,
        totalMass_map_weight right (fun rightValue => (value, rightValue)) weight,
        ih]
      simp [totalMass, Nat.add_mul]

theorem eventMass_weightedCartesian (left : List (Ω × Nat))
    (right : List (X × Nat)) (leftEvent : Event Ω)
    (rightEvent : Event X) :
    eventMass (weightedCartesian left right)
        (fun pair => leftEvent pair.1 && rightEvent pair.2) =
      eventMass left leftEvent * eventMass right rightEvent := by
  induction left with
  | nil =>
      simp [weightedCartesian, eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      change
        eventMass
            (right.map (fun rightAtom =>
              ((value, rightAtom.1), weight * rightAtom.2)) ++
              weightedCartesian atoms right)
            (fun pair => leftEvent pair.1 && rightEvent pair.2) = _
      rw [eventMass_append,
        eventMass_map_weight right
          (fun rightValue => (value, rightValue)) weight, ih]
      cases h : leftEvent value <;>
        simp [eventMass, eventMass_false, h, Nat.add_mul]

/-- Event mass of a cartesian product, expanded along the left factor.
Each left atom contributes its weight times the mass of the slice it
determines on the right. -/
theorem eventMass_weightedCartesian_bind
    (left : List (Ω × Nat)) (right : List (X × Nat))
    (event : Event (Ω × X)) :
    eventMass (weightedCartesian left right) event =
      (left.map fun leftAtom =>
        leftAtom.2 * eventMass right (fun x => event (leftAtom.1, x))).sum := by
  induction left with
  | nil =>
      simp [weightedCartesian, eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      change
        eventMass
            (right.map (fun rightAtom =>
              ((value, rightAtom.1), weight * rightAtom.2)) ++
              weightedCartesian atoms right) event =
          weight * eventMass right (fun x => event (value, x)) +
            (atoms.map fun leftAtom =>
              leftAtom.2 * eventMass right (fun x => event (leftAtom.1, x))).sum
      rw [eventMass_append,
        eventMass_map_weight right (fun rightValue => (value, rightValue)) weight,
        ih]

end FiniteProbRecord

/--
A finite rational probability record in common-denominator form.

The list `atoms` is a finite list of weighted outcomes.  Its weights sum to
the positive denominator `den`.  This is the constructive finite-support
version of a rational probability record after a common denominator has been
chosen.
-/
structure FiniteProbRecord (Ω : Type u) where
  atoms : List (Ω × Nat)
  den : Nat
  den_pos : 0 < den
  total_mass : FiniteProbRecord.totalMass atoms = den

namespace FiniteProbRecord

def probVal (R : FiniteProbRecord Ω) (E : Event Ω) : QProb where
  num := eventMass R.atoms E
  den := R.den
  den_pos := R.den_pos

/-- Every event probability in a finite probability record is nonnegative. -/
theorem probVal_nonneg (R : FiniteProbRecord Ω) (E : Event Ω) :
    QProb.LE QProb.zero (R.probVal E) :=
  QProb.zero_le _

/-- Every event probability in a finite probability record is at most one. -/
theorem probVal_le_one (R : FiniteProbRecord Ω) (E : Event Ω) :
    QProb.LE (R.probVal E) QProb.one := by
  simp only [QProb.LE, probVal, QProb.one, Nat.mul_one, Nat.one_mul]
  rw [← R.total_mass]
  exact eventMass_le_totalMass R.atoms E

/-- The closed-unit-interval bounds for a finite-record event probability. -/
theorem probVal_bounds (R : FiniteProbRecord Ω) (E : Event Ω) :
    QProb.LE QProb.zero (R.probVal E) ∧
      QProb.LE (R.probVal E) QProb.one :=
  ⟨R.probVal_nonneg E, R.probVal_le_one E⟩

theorem probVal_congr (R : FiniteProbRecord Ω) (E F : Event Ω)
    (pointwise : forall value, E value = F value) :
    QProb.Equiv (R.probVal E) (R.probVal F) := by
  have sameMass := eventMass_congr R.atoms E F pointwise
  simp [QProb.Equiv, probVal, sameMass]

theorem probVal_false (R : FiniteProbRecord Ω) :
    QProb.Equiv (R.probVal (fun _ => false)) QProb.zero := by
  simp [QProb.Equiv, probVal, eventMass_false, QProb.zero]

def singletonEvent [DecidableEq Ω] (value : Ω) : Event Ω :=
  fun candidate => decide (candidate = value)

def membershipEvent [DecidableEq Ω] (values : List Ω) : Event Ω :=
  fun candidate => decide (candidate ∈ values)

theorem probVal_union_disjoint (R : FiniteProbRecord Ω) (E F : Event Ω)
    (h : disjoint E F) :
    QProb.Equiv (R.probVal (union E F))
      (QProb.add (R.probVal E) (R.probVal F)) := by
  have hMass : eventMass R.atoms (union E F) =
      eventMass R.atoms E + eventMass R.atoms F := by
    induction R.atoms with
    | nil => rfl
    | cons atom atoms ih =>
        rcases atom with ⟨value, weight⟩
        cases hE : E value <;> cases hF : F value
        · simp [eventMass, union, hE, hF, ih]
        · simp [eventMass, union, hE, hF, ih]
          omega
        · simp [eventMass, union, hE, hF, ih]
          omega
        · exact False.elim (h value hE hF)
  simp [QProb.Equiv, QProb.add, probVal, hMass, Nat.add_mul,
    Nat.mul_assoc]

theorem membershipEvent_cons [DecidableEq Ω] (value : Ω) (values : List Ω) :
    membershipEvent (value :: values) =
      union (singletonEvent value) (membershipEvent values) := by
  funext candidate
  simp [membershipEvent, singletonEvent, union]

theorem singleton_membership_disjoint [DecidableEq Ω]
    {value : Ω} {values : List Ω} (fresh : value ∉ values) :
    disjoint (singletonEvent value) (membershipEvent values) := by
  intro candidate hSingleton hMembership
  have same : candidate = value := by
    simpa [singletonEvent] using hSingleton
  have member : candidate ∈ values := by
    simpa [membershipEvent] using hMembership
  exact fresh (same ▸ member)

theorem probVal_membership_equiv_listSum [DecidableEq Ω]
    (R : FiniteProbRecord Ω) (values : List Ω) (nodup : values.Nodup) :
    QProb.Equiv (R.probVal (membershipEvent values))
      (QProb.listSum (values.map (fun value =>
        R.probVal (singletonEvent value)))) := by
  induction values with
  | nil =>
      have emptyEvent : membershipEvent ([] : List Ω) = fun _ => false := by
        funext value
        simp [membershipEvent]
      rw [emptyEvent]
      simp [QProb.listSum, probVal, eventMass_false,
        QProb.Equiv, QProb.zero]
  | cons value values ih =>
      have fresh : value ∉ values := (List.nodup_cons.mp nodup).1
      have tailNodup : values.Nodup := (List.nodup_cons.mp nodup).2
      rw [membershipEvent_cons]
      exact QProb.equiv_trans
        (probVal_union_disjoint R _ _
          (singleton_membership_disjoint fresh))
        (QProb.add_congr (QProb.equiv_refl _)
          (ih tailNodup))

theorem membershipEvent_filter [DecidableEq Ω]
    (values : List Ω) (complete : forall value, value ∈ values)
    (event : Event Ω) :
    membershipEvent (values.filter event) = event := by
  funext value
  cases hEvent : event value with
  | false => simp [membershipEvent, hEvent]
  | true => simp [membershipEvent, hEvent, complete value]

theorem probVal_equiv_listSum_singletons [DecidableEq Ω]
    (R : FiniteProbRecord Ω) (values : List Ω)
    (nodup : values.Nodup) (complete : forall value, value ∈ values)
    (event : Event Ω) :
    QProb.Equiv (R.probVal event)
      (QProb.listSum ((values.filter event).map
        (fun value => R.probVal (singletonEvent value)))) := by
  have h := probVal_membership_equiv_listSum R (values.filter event)
    (List.Sublist.nodup List.filter_sublist nodup)
  rw [membershipEvent_filter values complete event] at h
  exact h

/-- On a finite enumerated type, singleton masses determine every event. -/
theorem probVal_extensional_of_singletons [DecidableEq Ω]
    (left right : FiniteProbRecord Ω) (values : List Ω)
    (nodup : values.Nodup) (complete : forall value, value ∈ values)
    (singletons : forall value,
      QProb.Equiv (left.probVal (singletonEvent value))
        (right.probVal (singletonEvent value)))
    (event : Event Ω) :
    QProb.Equiv (left.probVal event) (right.probVal event) := by
  exact QProb.equiv_trans
    (probVal_equiv_listSum_singletons left values nodup complete event)
    (QProb.equiv_trans
      (QProb.listSum_map_congr (values.filter event)
        (fun value => left.probVal (singletonEvent value))
        (fun value => right.probVal (singletonEvent value)) singletons)
      (QProb.equiv_symm
        (probVal_equiv_listSum_singletons right values nodup complete event)))

/-- Constructive positivity of a finite event, stated at natural event-mass level. -/
def EventPositive (R : FiniteProbRecord Ω) (event : Event Ω) : Prop :=
  0 < eventMass R.atoms event

instance (R : FiniteProbRecord Ω) (event : Event Ω) :
    Decidable (R.EventPositive event) := by
  unfold EventPositive
  infer_instance

def map (R : FiniteProbRecord Ω) (f : Ω → X) : FiniteProbRecord X where
  atoms := R.atoms.map (fun atom => (f atom.1, atom.2))
  den := R.den
  den_pos := R.den_pos
  total_mass := by
    rw [totalMass_map_labels, R.total_mass]

theorem map_probVal (R : FiniteProbRecord Ω) (f : Ω → X)
    (event : Event X) :
    QProb.Equiv ((R.map f).probVal event)
      (R.probVal (fun omega => event (f omega))) := by
  simp [QProb.Equiv, map, probVal, eventMass_map_labels]

/-- Construct the independent product of two finite probability records. -/
def product (left : FiniteProbRecord Ω) (right : FiniteProbRecord X) :
    FiniteProbRecord (Ω × X) where
  atoms := weightedCartesian left.atoms right.atoms
  den := left.den * right.den
  den_pos := Nat.mul_pos left.den_pos right.den_pos
  total_mass := by
    rw [totalMass_weightedCartesian, left.total_mass, right.total_mass]

/-- Rectangular events in the product have the product of their probabilities. -/
theorem product_probVal (left : FiniteProbRecord Ω)
    (right : FiniteProbRecord X) (leftEvent : Event Ω)
    (rightEvent : Event X) :
    QProb.Equiv
      ((left.product right).probVal
        (fun pair => leftEvent pair.1 && rightEvent pair.2))
      (QProb.mul (left.probVal leftEvent) (right.probVal rightEvent)) := by
  simp [QProb.Equiv, product, probVal, QProb.mul,
    eventMass_weightedCartesian, Nat.mul_assoc]

/-- Bayesian conditioning with a proof-carrying finite support witness. -/
def conditionOn (R : FiniteProbRecord Ω) (evidence : Event Ω)
    (hEvidence : R.EventPositive evidence) : FiniteProbRecord Ω where
  atoms := R.atoms.filter (fun atom => evidence atom.1)
  den := eventMass R.atoms evidence
  den_pos := hEvidence
  total_mass := totalMass_filter_event R.atoms evidence

theorem conditionOn_probVal (R : FiniteProbRecord Ω)
    (evidence event : Event Ω) (hEvidence : R.EventPositive evidence) :
    QProb.Equiv
      ((R.conditionOn evidence hEvidence).probVal event)
      (QProb.div
        (R.probVal (fun omega => evidence omega && event omega))
        (R.probVal evidence) hEvidence) := by
  simp only [conditionOn, probVal, eventMass_filter_event, QProb.div,
    QProb.Equiv]
  ac_rfl

theorem normalization (R : FiniteProbRecord Ω) :
    QProb.Equiv (R.probVal topEvent) QProb.one := by
  simp [QProb.Equiv, probVal, QProb.one, eventMass_top, R.total_mass]

theorem conditionOn_normalization (R : FiniteProbRecord Ω)
    (evidence : Event Ω) (hEvidence : R.EventPositive evidence) :
    QProb.Equiv
      ((R.conditionOn evidence hEvidence).probVal topEvent)
      QProb.one :=
  (R.conditionOn evidence hEvidence).normalization

/--
Bayes' theorem for finite common-denominator records.  Both event-positivity
witnesses are explicit because the two conditional probabilities and the
final division each require a positive denominator.
-/
theorem bayes_formula (R : FiniteProbRecord Ω) (E F : Event Ω)
    (hE : R.EventPositive E) (hF : R.EventPositive F) :
    QProb.Equiv
      ((R.conditionOn F hF).probVal E)
      (QProb.div
        (QProb.mul ((R.conditionOn E hE).probVal F) (R.probVal E))
        (R.probVal F)
        hF) := by
  have hInter :
      eventMass R.atoms (fun value => F value && E value) =
        eventMass R.atoms (fun value => E value && F value) :=
    eventMass_congr R.atoms _ _ (fun value => Bool.and_comm _ _)
  simp only [conditionOn, probVal, eventMass_filter_event, QProb.Equiv,
    QProb.mul, QProb.div]
  rw [hInter]
  ac_rfl

def toUrn (R : FiniteProbRecord Ω) : UrnProb Ω :=
  UrnProb.ofList (expand R.atoms) (by
    rw [length_expand, R.total_mass]
    exact R.den_pos)

def ofUrn (μ : UrnProb Ω) : FiniteProbRecord Ω where
  atoms := μ.support.map (fun ω => (ω, 1))
  den := μ.n
  den_pos := μ.pos
  total_mass := by
    rw [totalMass_unit, μ.support_length]

def AgreesWith (R : FiniteProbRecord Ω) (μ : UrnProb Ω) : Prop :=
  ∀ E : Event Ω, QProb.Equiv (R.probVal E) (μ.probVal E)

theorem toUrn_agrees (R : FiniteProbRecord Ω) :
    AgreesWith R R.toUrn := by
  intro E
  have hsupport : R.toUrn.support = expand R.atoms := by
    simp [toUrn, UrnProb.support_ofList]
  have hcount : R.toUrn.probNum E = eventMass R.atoms E := by
    rw [UrnProb.probNum, hsupport, count_expand]
  have hn : R.toUrn.n = R.den := by
    simp [toUrn, UrnProb.ofList, length_expand, R.total_mass]
  simp [probVal, UrnProb.probVal, QProb.Equiv, hcount, hn]

/--
Finite additivity for an arbitrary finite pairwise-disjoint family.  The proof
passes through the extensionally equivalent unit-cell urn, so the record and
urn presentations expose the same finite-additivity law.
-/
theorem finite_additivity_family (R : FiniteProbRecord Ω)
    (events : List (Event Ω)) (pairwise : events.Pairwise disjoint) :
    QProb.Equiv (R.probVal (unionList events))
      (QProb.listSum (events.map R.probVal)) := by
  exact QProb.equiv_trans
    (R.toUrn_agrees (unionList events))
    (QProb.equiv_trans
      (R.toUrn.finite_additivity_family events pairwise)
      (QProb.listSum_map_congr events R.toUrn.probVal R.probVal
        (fun event => QProb.equiv_symm (R.toUrn_agrees event))))

theorem ofUrn_agrees (μ : UrnProb Ω) :
    AgreesWith (ofUrn μ) μ := by
  intro E
  simp [ofUrn, probVal, UrnProb.probVal, UrnProb.probNum,
    QProb.Equiv, eventMass_unit]

theorem record_to_urn_extensional (R : FiniteProbRecord Ω) :
    ∀ E : Event Ω, QProb.Equiv (R.probVal E) (R.toUrn.probVal E) :=
  R.toUrn_agrees

theorem urn_to_record_extensional (μ : UrnProb Ω) :
    ∀ E : Event Ω, QProb.Equiv ((ofUrn μ).probVal E) (μ.probVal E) :=
  ofUrn_agrees μ

end FiniteProbRecord

end Probability
end Thesis
