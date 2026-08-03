import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability

/-!
Finite dependent-product constructions for probability records.

This module turns independently specified finite coordinate records into one
record on their dependent product.  The recursive implementation works from
the terminal coordinate backwards because that gives a constructively explicit
enumeration and avoids assuming a homogeneous value type.  The resulting
record is used as the latent product prior of a finite SCM.
-/

/-- Remove repeated values while retaining one representative of each value. -/
def deduplicate [DecidableEq X] : List X -> List X
  | [] => []
  | value :: values =>
      let tail := deduplicate values
      if value ∈ tail then tail else value :: tail

theorem mem_deduplicate [DecidableEq X] (value : X) (values : List X) :
    value ∈ deduplicate values <-> value ∈ values := by
  induction values with
  | nil => simp [deduplicate]
  | cons head tail ih =>
      simp only [deduplicate]
      by_cases duplicate : head ∈ deduplicate tail
      · rw [if_pos duplicate]
        constructor
        · intro member
          exact List.mem_cons.mpr (Or.inr (ih.mp member))
        · intro member
          rcases List.mem_cons.mp member with same | member
          · exact same ▸ duplicate
          · exact ih.mpr member
      · rw [if_neg duplicate]
        simp [ih]

theorem deduplicate_nodup [DecidableEq X] (values : List X) :
    (deduplicate values).Nodup := by
  induction values with
  | nil => simp [deduplicate]
  | cons head tail ih =>
      simp only [deduplicate]
      by_cases duplicate : head ∈ deduplicate tail
      · rw [if_pos duplicate]
        exact ih
      · rw [if_neg duplicate]
        exact List.nodup_cons.mpr ⟨duplicate, ih⟩

/-- A finite presentation explicitly identifies a type with `Fin card`. -/
structure FiniteWitness (X : Type u) where
  card : Nat
  encode : X -> Fin card
  decode : Fin card -> X
  decode_encode : forall x, decode (encode x) = x
  encode_decode : forall i, encode (decode i) = i

theorem idxOf_get_of_nodup [DecidableEq X]
    (values : List X) (nodup : values.Nodup) (i : Fin values.length) :
    values.idxOf (values.get i) = i.val := by
  induction values with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
      have parts := List.nodup_cons.mp nodup
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · change List.idxOf (tail.get j) (head :: tail) = j.val + 1
        rw [List.idxOf_cons]
        have different : (head == tail.get j) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro same
          apply parts.1
          rw [same]
          exact List.get_mem tail j
        rw [different]
        simp only [cond_false]
        rw [ih parts.2 j]

/-- An exhaustive duplicate-free list gives an explicit finite presentation. -/
def FiniteWitness.ofList [DecidableEq X]
    (values : List X) (complete : forall x, x ∈ values)
    (nodup : values.Nodup) : FiniteWitness X where
  card := values.length
  encode := fun x =>
    ⟨values.idxOf x, List.idxOf_lt_length_of_mem (complete x)⟩
  decode := fun i => values.get i
  decode_encode := by
    intro x
    apply beq_iff_eq.mp
    change (values.get ⟨values.idxOf x,
      List.idxOf_lt_length_of_mem (complete x)⟩ == x) = true
    simpa [List.get_eq_getElem, List.idxOf] using
      (List.findIdx_getElem
        (p := fun value => value == x)
        (xs := values)
        (w := List.idxOf_lt_length_of_mem (complete x)))
  encode_decode := by
    intro i
    apply Fin.ext
    exact idxOf_get_of_nodup values nodup i

namespace FiniteProduct

/-- A dependent assignment chooses one value for every finite coordinate. -/
abbrev Assignment (n : Nat) (Value : Fin n -> Type u) :=
  (i : Fin n) -> Value i

def assignmentDecidableEq : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> DecidableEq (Value i)) ->
    DecidableEq (Assignment n Value)
  | 0, _, _ => fun left right =>
      isTrue (by
        funext i
        exact Fin.elim0 i)
  | n + 1, Value, decEq => fun left right =>
      match decEq (Fin.last n) (left (Fin.last n)) (right (Fin.last n)) with
      | isFalse differentLast =>
          isFalse (fun equal => differentLast (congrFun equal (Fin.last n)))
      | isTrue equalLast =>
          match assignmentDecidableEq n (fun i => Value i.castSucc)
              (fun i => decEq i.castSucc)
              (fun i => left i.castSucc) (fun i => right i.castSucc) with
          | isFalse differentInitial =>
              isFalse (fun equal => differentInitial (by
                funext i
                exact congrFun equal i.castSucc))
          | isTrue equalInitial =>
              isTrue (by
                funext i
                refine Fin.lastCases ?_ (fun earlier => ?_) i
                · exact equalLast
                · exact congrFun equalInitial earlier)

def snocCases {n : Nat} {motive : Fin (n + 1) -> Sort u}
    (last : motive (Fin.last n))
    (initial : (i : Fin n) -> motive i.castSucc)
    (i : Fin (n + 1)) : motive i :=
  if h : i.val < n then
    let earlier : Fin n := ⟨i.val, h⟩
    have same : earlier.castSucc = i := Fin.ext (Eq.refl i.val)
    same ▸ initial earlier
  else
    have atLast : i.val = n := Nat.eq_of_lt_succ_of_not_lt i.isLt h
    have same : Fin.last n = i := Fin.ext atLast.symm
    same ▸ last

def extend {n : Nat} {Value : Fin (n + 1) -> Type u}
    (last : Value (Fin.last n))
    (initial : (i : Fin n) -> Value i.castSucc) : Assignment (n + 1) Value :=
  fun i => snocCases last initial i

@[simp] theorem extend_last {n : Nat} {Value : Fin (n + 1) -> Type u}
    (last : Value (Fin.last n))
    (initial : (i : Fin n) -> Value i.castSucc) :
    extend last initial (Fin.last n) = last := by
  unfold extend snocCases
  have hnot : Not ((Fin.last n).val < n) := Nat.lt_irrefl n
  rw [dif_neg hnot]

@[simp] theorem extend_castSucc {n : Nat} {Value : Fin (n + 1) -> Type u}
    (last : Value (Fin.last n))
    (initial : (i : Fin n) -> Value i.castSucc) (i : Fin n) :
    extend last initial i.castSucc = initial i := by
  unfold extend snocCases
  have hpos : i.castSucc.val < n := i.isLt
  rw [dif_pos hpos]
  let earlier : Fin n := ⟨i.castSucc.val, hpos⟩
  have hearlier : earlier = i := Fin.ext (Eq.refl i.val)
  cases hearlier
  rfl

theorem castSucc_ne_last {n : Nat} (i : Fin n) :
    i.castSucc ≠ Fin.last n :=
  Fin.ne_of_lt i.castSucc_lt_last

theorem last_ne_castSucc {n : Nat} (i : Fin n) :
    Fin.last n ≠ i.castSucc :=
  Ne.symm (castSucc_ne_last i)

def denominator : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> FiniteProbRecord (Value i)) -> Nat
  | 0, _, _ => 1
  | n + 1, Value, factors =>
      (factors (Fin.last n)).den *
        denominator n (fun i => Value i.castSucc)
          (fun i => factors i.castSucc)

def atoms : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) ->
    List (Assignment n Value × Nat)
  | 0, _, _ => [(fun i => Fin.elim0 i, 1)]
  | n + 1, Value, factors =>
      let prefixAtoms :=
        atoms n (fun i => Value i.castSucc) (fun i => factors i.castSucc)
      (FiniteProbRecord.weightedCartesian
          (factors (Fin.last n)).atoms prefixAtoms).map (fun atom =>
        (extend atom.1.1 atom.1.2, atom.2))

def enumeration : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> List (Value i)) -> List (Assignment n Value)
  | 0, _, _ => [fun i => Fin.elim0 i]
  | n + 1, Value, values =>
      (values (Fin.last n)).flatMap (fun last =>
        (enumeration n (fun i => Value i.castSucc)
          (fun i => values i.castSucc)).map (fun initial =>
            extend last initial))

theorem enumeration_complete (n : Nat) (Value : Fin n -> Type u)
    (values : (i : Fin n) -> List (Value i))
    (complete : forall i value, value ∈ values i)
    (assignment : Assignment n Value) :
    assignment ∈ enumeration n Value values := by
  induction n with
  | zero =>
      have hAssignment : assignment = fun i => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      rw [hAssignment]
      exact List.mem_cons_self
  | succ n ih =>
      rw [enumeration]
      let last := assignment (Fin.last n)
      let initial : (i : Fin n) -> Value i.castSucc :=
        fun i => assignment i.castSucc
      have hLast : last ∈ values (Fin.last n) :=
        complete (Fin.last n) last
      have hInitial :
          initial ∈ enumeration n (fun i => Value i.castSucc)
            (fun i => values i.castSucc) :=
        ih (fun i => Value i.castSucc) (fun i => values i.castSucc)
          (fun i value => complete i.castSucc value) initial
      have hMapped :
          extend last initial ∈
            (enumeration n (fun i => Value i.castSucc)
              (fun i => values i.castSucc)).map (fun initialAssignment =>
                extend last initialAssignment) :=
        List.mem_map_of_mem hInitial
      have hFlat :
          extend last initial ∈
            (values (Fin.last n)).flatMap (fun final =>
              (enumeration n (fun i => Value i.castSucc)
                (fun i => values i.castSucc)).map (fun initialAssignment =>
                  extend final initialAssignment)) :=
        List.mem_flatMap_of_mem hLast hMapped
      have hAssignment : extend last initial = assignment := by
        funext i
        refine Fin.lastCases ?_ (fun earlier => ?_) i
        · change extend last initial (Fin.last n) = last
          exact extend_last last initial
        · change extend last initial earlier.castSucc = initial earlier
          exact extend_castSucc last initial earlier
      exact hAssignment ▸ hFlat

/-- A finite dependent assignment type has an explicit finite presentation. -/
def finiteWitness (n : Nat) (Value : Fin n -> Type u)
    (values : (i : Fin n) -> List (Value i))
    (complete : forall i value, value ∈ values i)
    (decEq : (i : Fin n) -> DecidableEq (Value i)) :
    FiniteWitness (Assignment n Value) := by
  letI : DecidableEq (Assignment n Value) :=
    assignmentDecidableEq n Value decEq
  exact FiniteWitness.ofList
    (deduplicate (enumeration n Value values))
    (fun assignment =>
      (mem_deduplicate assignment (enumeration n Value values)).2
        (enumeration_complete n Value values complete assignment))
    (deduplicate_nodup (enumeration n Value values))

def natProduct : (n : Nat) -> (Fin n -> Nat) -> Nat
  | 0, _ => 1
  | n + 1, values =>
      values (Fin.last n) * natProduct n (fun i => values i.castSucc)

def qProduct : (n : Nat) -> (Fin n -> QProb) -> QProb
  | 0, _ => QProb.one
  | n + 1, values =>
      QProb.mul (values (Fin.last n))
        (qProduct n (fun i => values i.castSucc))


def rectangularEvent : (n : Nat) ->
    (Value : Fin n -> Type u) ->
    ((i : Fin n) -> Value i -> Bool) -> Event (Assignment n Value)
  | 0, _, _, _ => true
  | n + 1, Value, events, assignment =>
      events (Fin.last n) (assignment (Fin.last n)) &&
      rectangularEvent n (fun i => Value i.castSucc)
          (fun i => events i.castSucc) (fun i => assignment i.castSucc)

theorem rectangularEvent_assignment_congr (n : Nat)
    (Value : Fin n -> Type u) (events : (i : Fin n) -> Value i -> Bool)
    (left right : Assignment n Value)
    (h : forall i, left i = right i) :
    rectangularEvent n Value events left =
      rectangularEvent n Value events right := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (events (Fin.last n) (left (Fin.last n)) &&
          rectangularEvent n (fun i => Value i.castSucc)
            (fun i => events i.castSucc) (fun i => left i.castSucc)) =
        (events (Fin.last n) (right (Fin.last n)) &&
          rectangularEvent n (fun i => Value i.castSucc)
            (fun i => events i.castSucc) (fun i => right i.castSucc))
      rw [h (Fin.last n)]
      exact congrArg (fun suffix =>
        events (Fin.last n) (right (Fin.last n)) && suffix)
        (ih (fun i => Value i.castSucc) (fun i => events i.castSucc)
          (fun i => left i.castSucc) (fun i => right i.castSucc)
          (fun i => h i.castSucc))

theorem denominator_pos (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) :
    0 < denominator n Value factors := by
  induction n with
  | zero =>
      simp [denominator]
  | succ n ih =>
      exact Nat.mul_pos (factors (Fin.last n)).den_pos
        (ih (fun i => Value i.castSucc) (fun i => factors i.castSucc))

theorem totalMass_atoms (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) :
    FiniteProbRecord.totalMass (atoms n Value factors) =
      denominator n Value factors := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      let productAtoms :=
        FiniteProbRecord.weightedCartesian
          (factors (Fin.last n)).atoms
          (atoms n (fun i => Value i.castSucc)
            (fun i => factors i.castSucc))
      calc
        FiniteProbRecord.totalMass (atoms (n + 1) Value factors) =
            FiniteProbRecord.totalMass productAtoms := by
              simpa [atoms, productAtoms] using
                FiniteProbRecord.totalMass_map_labels productAtoms
                  (fun pair => extend pair.1 pair.2)
        _ = FiniteProbRecord.totalMass (factors (Fin.last n)).atoms *
              FiniteProbRecord.totalMass
                (atoms n (fun i => Value i.castSucc)
                  (fun i => factors i.castSucc)) := by
              exact FiniteProbRecord.totalMass_weightedCartesian _ _
        _ = denominator (n + 1) Value factors := by
              rw [(factors (Fin.last n)).total_mass,
                ih (fun i => Value i.castSucc)
                  (fun i => factors i.castSucc)]
              rfl

theorem eventMass_atoms (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i))
    (events : (i : Fin n) -> Value i -> Bool) :
    FiniteProbRecord.eventMass (atoms n Value factors)
        (rectangularEvent n Value events) =
      natProduct n (fun i =>
        FiniteProbRecord.eventMass (factors i).atoms (events i)) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      let productAtoms :=
        FiniteProbRecord.weightedCartesian
          (factors (Fin.last n)).atoms
          (atoms n (fun i => Value i.castSucc)
            (fun i => factors i.castSucc))
      have hMap := FiniteProbRecord.eventMass_map_labels productAtoms
        (fun pair : Value (Fin.last n) ×
            Assignment n (fun i => Value i.castSucc) =>
          extend pair.1 pair.2)
        (rectangularEvent (n + 1) Value events)
      have hEvent (pair : Value (Fin.last n) ×
          Assignment n (fun i => Value i.castSucc)) :
          rectangularEvent (n + 1) Value events
              (extend pair.1 pair.2) =
            (events (Fin.last n) pair.1 &&
              rectangularEvent n (fun i => Value i.castSucc)
                (fun i => events i.castSucc) pair.2) := by
        change
          (events (Fin.last n) (extend pair.1 pair.2 (Fin.last n)) &&
            rectangularEvent n (fun i => Value i.castSucc)
              (fun i => events i.castSucc)
              (fun i => extend pair.1 pair.2 i.castSucc)) =
          (events (Fin.last n) pair.1 &&
            rectangularEvent n (fun i => Value i.castSucc)
              (fun i => events i.castSucc) pair.2)
        rw [extend_last]
        exact congrArg (fun suffix =>
          events (Fin.last n) pair.1 && suffix)
          (rectangularEvent_assignment_congr n
            (fun i => Value i.castSucc) (fun i => events i.castSucc)
            (fun i => extend pair.1 pair.2 i.castSucc) pair.2
            (fun i => extend_castSucc pair.1 pair.2 i))
      calc
        FiniteProbRecord.eventMass (atoms (n + 1) Value factors)
            (rectangularEvent (n + 1) Value events) =
            FiniteProbRecord.eventMass productAtoms
              (fun pair => rectangularEvent (n + 1) Value events
                (extend pair.1 pair.2)) := by
              change
                FiniteProbRecord.eventMass
                    (productAtoms.map (fun atom =>
                      (extend atom.1.1 atom.1.2, atom.2)))
                    (rectangularEvent (n + 1) Value events) =
                  FiniteProbRecord.eventMass productAtoms
                    (fun pair => rectangularEvent (n + 1) Value events
                      (extend pair.1 pair.2))
              exact hMap
        _ = FiniteProbRecord.eventMass productAtoms
              (fun pair =>
                events (Fin.last n) pair.1 &&
                  rectangularEvent n (fun i => Value i.castSucc)
                    (fun i => events i.castSucc) pair.2) := by
              exact FiniteProbRecord.eventMass_congr productAtoms _ _ hEvent
        _ = _ := by
              rw [FiniteProbRecord.eventMass_weightedCartesian,
                ih (fun i => Value i.castSucc)
                  (fun i => factors i.castSucc)
                  (fun i => events i.castSucc)]
              rfl

/-- The exact independent product of finitely many probability records. -/
def record (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i)) :
    FiniteProbRecord (Assignment n Value) where
  atoms := atoms n Value factors
  den := denominator n Value factors
  den_pos := denominator_pos n Value factors
  total_mass := totalMass_atoms n Value factors

/-- The product record satisfies its rectangular-event law constructively. -/
theorem record_rectangular_probVal (n : Nat) (Value : Fin n -> Type u)
    (factors : (i : Fin n) -> FiniteProbRecord (Value i))
    (events : (i : Fin n) -> Value i -> Bool) :
    QProb.Equiv
      ((record n Value factors).probVal
        (rectangularEvent n Value events))
      (qProduct n (fun i => (factors i).probVal (events i))) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      let prefixValue := fun i : Fin n => Value i.castSucc
      let prefixFactors := fun i : Fin n => factors i.castSucc
      let prefixEvents := fun i : Fin n => events i.castSucc
      let lastValue := (factors (Fin.last n)).probVal (events (Fin.last n))
      let prefixValueProb :=
        (record n prefixValue prefixFactors).probVal
          (rectangularEvent n prefixValue prefixEvents)
      have hStep :
          QProb.Equiv
            ((record (n + 1) Value factors).probVal
              (rectangularEvent (n + 1) Value events))
            (QProb.mul lastValue prefixValueProb) := by
        simp only [record, FiniteProbRecord.probVal, eventMass_atoms,
          denominator, natProduct, QProb.Equiv, QProb.mul, lastValue,
          prefixValueProb, prefixValue, prefixFactors, prefixEvents]
      exact QProb.equiv_trans hStep
        (QProb.mul_congr (QProb.equiv_refl lastValue)
          (ih prefixValue prefixFactors prefixEvents))

theorem qProduct_congr (n : Nat) {left right : Fin n -> QProb}
    (equivalent : forall i, QProb.Equiv (left i) (right i)) :
    QProb.Equiv (qProduct n left) (qProduct n right) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact QProb.mul_congr (equivalent (Fin.last n))
        (ih (fun i => equivalent i.castSucc))

theorem qProduct_one (n : Nat) :
    QProb.Equiv (qProduct n (fun _ => QProb.one)) QProb.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact QProb.equiv_trans
        (QProb.mul_congr (QProb.equiv_refl QProb.one) ih) (by
          simp [QProb.Equiv, QProb.mul, QProb.one])

theorem qProduct_singleton (n : Nat) (chosen : Fin n)
    (selected : QProb) :
    QProb.Equiv
      (qProduct n (fun i => if i = chosen then selected else QProb.one))
      selected := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      refine Fin.lastCases ?_ (fun earlier => ?_) chosen
      · have hInitial :
            (fun i : Fin n =>
              if i.castSucc = Fin.last n then selected else QProb.one) =
            (fun _ => QProb.one) := by
          funext i
          simp [castSucc_ne_last]
        rw [qProduct, if_pos rfl, hInitial]
        exact QProb.equiv_trans
          (QProb.mul_congr (QProb.equiv_refl selected) (qProduct_one n)) (by
            simp [QProb.Equiv, QProb.mul, QProb.one])
      · have hInitial :
            (fun i : Fin n =>
              if i.castSucc = earlier.castSucc then selected else QProb.one) =
            (fun i => if i = earlier then selected else QProb.one) := by
          funext i
          simp [Fin.ext_iff]
        rw [qProduct, if_neg (last_ne_castSucc earlier), hInitial]
        exact QProb.equiv_trans
          (QProb.mul_congr (QProb.equiv_refl QProb.one) (ih earlier)) (by
            simp [QProb.Equiv, QProb.mul, QProb.one])


theorem rectangularEvent_true (n : Nat) (Value : Fin n -> Type u)
    (assignment : Assignment n Value) :
    rectangularEvent n Value (fun _ _ => true) assignment = true := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [rectangularEvent,
        ih (fun i => Value i.castSucc) (fun i => assignment i.castSucc)]

theorem rectangularEvent_singleton (n : Nat) (Outcome : Type u)
    (chosen : Fin n) (event : Outcome -> Bool)
    (assignment : Fin n -> Outcome) :
    rectangularEvent n (fun _ => Outcome)
        (fun i value => if i = chosen then event value else true) assignment =
      event (assignment chosen) := by
  induction n with
  | zero =>
      exact Fin.elim0 chosen
  | succ n ih =>
      refine Fin.lastCases ?_ (fun earlier => ?_) chosen
      · have hInitialEvents :
            (fun (i : Fin n) (value : Outcome) =>
              if i.castSucc = Fin.last n then event value else true) =
            (fun _ _ => true) := by
          funext i value
          simp [castSucc_ne_last]
        rw [rectangularEvent]
        rw [if_pos rfl]
        change
          (event (assignment (Fin.last n)) &&
              rectangularEvent n (fun _ => Outcome)
                (fun i value =>
                  if i.castSucc = Fin.last n then event value else true)
                (fun i => assignment i.castSucc)) =
            event (assignment (Fin.last n))
        rw [hInitialEvents, rectangularEvent_true]
        simp
      · have hInitialEvents :
            (fun (i : Fin n) (value : Outcome) =>
              if i.castSucc = earlier.castSucc then event value else true) =
            (fun i value => if i = earlier then event value else true) := by
          funext i value
          simp [Fin.ext_iff]
        rw [rectangularEvent]
        change
          ((if Fin.last n = earlier.castSucc then
              event (assignment (Fin.last n)) else true) &&
              rectangularEvent n (fun _ => Outcome)
                (fun i value =>
                  if i.castSucc = earlier.castSucc then event value else true)
                (fun i => assignment i.castSucc)) =
            event (assignment earlier.castSucc)
        rw [if_neg (last_ne_castSucc earlier), hInitialEvents,
          ih earlier (fun i => assignment i.castSucc)]
        simp

/-- A coordinate of the independent product has its declared marginal law. -/
theorem record_coordinate_probVal (n : Nat) (Outcome : Type u)
    (factors : Fin n -> FiniteProbRecord Outcome)
    (chosen : Fin n) (event : Outcome -> Bool) :
    QProb.Equiv
      ((record n (fun _ => Outcome) factors).probVal
        (fun assignment => event (assignment chosen)))
      ((factors chosen).probVal event) := by
  let events : (i : Fin n) -> Outcome -> Bool :=
    fun i value => if i = chosen then event value else true
  have hRectangular :=
    record_rectangular_probVal n (fun _ => Outcome) factors events
  have hEvent :
      rectangularEvent n (fun _ => Outcome) events =
        (fun assignment => event (assignment chosen)) := by
    funext assignment
    exact rectangularEvent_singleton n Outcome chosen event assignment
  rw [hEvent] at hRectangular
  exact QProb.equiv_trans hRectangular
    (QProb.equiv_trans
      (qProduct_congr n (fun i => by
        by_cases h : i = chosen
        · subst i
          simpa [events] using
            (QProb.equiv_refl ((factors chosen).probVal event))
        · exact QProb.equiv_trans
            (FiniteProbRecord.probVal_congr (factors i) _ topEvent
              (fun value => by simp [events, h, topEvent]))
            (by simpa [h] using (factors i).normalization)))
      (qProduct_singleton n chosen ((factors chosen).probVal event)))


end FiniteProduct

/-!
## Generic common-denominator conversion

The finite probability records above store one common denominator.  The
following construction shows that this is not an additional restriction: an
arbitrary normalized family of nonnegative rational masses on a finite type
can be converted to that representation constructively.
-/

namespace CommonDenominator

private def zeroWithDenominator (p : QProb) : QProb where
  num := 0
  den := p.den
  den_pos := p.den_pos

/-- The product of all denominators in a finite rational mass table. -/
def denominator (values : List Ω) (mass : Ω → QProb) : Nat :=
  values.foldr (fun ω den => (mass ω).den * den) 1

theorem denominator_pos (values : List Ω) (mass : Ω → QProb) :
    0 < denominator values mass := by
  induction values with
  | nil =>
      simp [denominator]
  | cons ω values ih =>
      exact Nat.mul_pos (mass ω).den_pos ih

/--
Integer weights obtained by putting every row over `denominator values mass`.
Earlier weights are multiplied whenever a new denominator is introduced.
-/
def atoms : (values : List Ω) → (mass : Ω → QProb) → List (Ω × Nat)
  | [], _ => []
  | ω :: values, mass =>
      (ω, (mass ω).num * denominator values mass) ::
        (atoms values mass).map
          (fun atom => (atom.1, (mass ω).den * atom.2))

/--
The sum of the selected masses.  A non-selected entry contributes a zero with
the entry's own denominator, so the resulting denominator is definitionally
the product of all denominators, independently of the event.
-/
def eventSum : (values : List Ω) → (mass : Ω → QProb) → Event Ω → QProb
  | [], _, _ => QProb.zero
  | ω :: values, mass, event =>
      QProb.add
        (if event ω then mass ω
          else zeroWithDenominator (mass ω))
        (eventSum values mass event)

theorem eventSum_den (values : List Ω) (mass : Ω → QProb)
    (event : Event Ω) :
    (eventSum values mass event).den = denominator values mass := by
  induction values with
  | nil =>
      rfl
  | cons ω values ih =>
      cases hEvent : event ω <;>
        simp [eventSum, denominator, QProb.add, zeroWithDenominator,
          hEvent, ih]

theorem eventMass_atoms (values : List Ω) (mass : Ω → QProb)
    (event : Event Ω) :
    FiniteProbRecord.eventMass (atoms values mass) event =
      (eventSum values mass event).num := by
  induction values with
  | nil =>
      rfl
  | cons ω values ih =>
      rw [atoms]
      simp only [FiniteProbRecord.eventMass]
      rw [FiniteProbRecord.eventMass_scale, ih]
      cases hEvent : event ω <;>
        simp [eventSum, QProb.add, zeroWithDenominator, hEvent,
          eventSum_den, Nat.mul_comm]

/--
A finite rational mass assignment before a common denominator has been chosen.
`values` explicitly witnesses finiteness and exhausts the outcome type.
-/
structure FiniteQMass (Ω : Type u) where
  values : List Ω
  nodup : values.Nodup
  complete : ∀ ω, ω ∈ values
  mass : Ω → QProb
  normalized : QProb.Equiv (eventSum values mass topEvent) QProb.one

namespace FiniteQMass

def probVal (M : FiniteQMass Ω) (event : Event Ω) : QProb :=
  eventSum M.values M.mass event

theorem common_total_mass (M : FiniteQMass Ω) :
    FiniteProbRecord.totalMass (atoms M.values M.mass) =
      denominator M.values M.mass := by
  have hEvent := eventMass_atoms M.values M.mass topEvent
  rw [FiniteProbRecord.eventMass_top] at hEvent
  have hDen := eventSum_den M.values M.mass topEvent
  have hNorm := M.normalized
  simp [QProb.Equiv, QProb.one] at hNorm
  calc
    FiniteProbRecord.totalMass (atoms M.values M.mass) =
        (eventSum M.values M.mass topEvent).num := hEvent
    _ = (eventSum M.values M.mass topEvent).den := hNorm
    _ = denominator M.values M.mass := hDen

/-- Construct the common-denominator probability record. -/
def toRecord (M : FiniteQMass Ω) : FiniteProbRecord Ω where
  atoms := atoms M.values M.mass
  den := denominator M.values M.mass
  den_pos := denominator_pos M.values M.mass
  total_mass := M.common_total_mass

/-- Every decidable event has the same rational probability after conversion. -/
theorem toRecord_preserves (M : FiniteQMass Ω) (event : Event Ω) :
    QProb.Equiv (M.toRecord.probVal event) (M.probVal event) := by
  simp [QProb.Equiv, toRecord, probVal, FiniteProbRecord.probVal,
    eventMass_atoms, eventSum_den]

/-- The resulting urn also preserves every event probability. -/
theorem toUrn_preserves (M : FiniteQMass Ω) (event : Event Ω) :
    QProb.Equiv (M.toRecord.toUrn.probVal event) (M.probVal event) := by
  exact QProb.equiv_trans
    (QProb.equiv_symm (M.toRecord.toUrn_agrees event))
    (M.toRecord_preserves event)

end FiniteQMass
end CommonDenominator

end Probability
end Thesis
