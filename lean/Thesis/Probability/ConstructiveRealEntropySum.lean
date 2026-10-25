import Thesis.Probability.ConstructiveRealEntropyFormula

namespace Thesis.Probability.ConstructiveReal

/-- An auxiliary analytic value in [0,1]. A list of these coordinates is
not asserted to be normalized or to satisfy moment constraints. The actual
finite `Distro` constructors continue to have rational atom weights. -/
structure UnitIntervalValue where
  value : ConstructiveReal
  nonnegative : LE zero value
  bounded : LE value one

namespace UnitIntervalValue

def ofQProb (mass : QProb) (bounded : mass.num ≤ mass.den) : UnitIntervalValue where
  value := ofSignedRatio mass.toSignedRatio
  nonnegative := (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le mass))
  bounded := (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff mass QProb.one).mpr
    (by simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using bounded))

def entropy (mass : UnitIntervalValue) : ConstructiveReal := mass.value.realEntropyTerm mass.nonnegative mass.bounded

def ofBoundedQProb (mass : {q : QProb // q.num ≤ q.den}) : UnitIntervalValue := ofQProb mass.val mass.property

theorem entropy_ofQProb (mass : QProb) (bounded : mass.num ≤ mass.den) :
    Equiv (ofQProb mass bounded).entropy (rationalEntropyTerm mass) :=
  realEntropyTerm_ofQProb mass _ _

end UnitIntervalValue

/-- Finite Shannon sum on auxiliary real coordinates, before any feasibility
claim. Each coordinate denotes a distinct declared state; duplicate record
occurrences must first be aggregated by the existing law interface. Its scalar terms include the continuous zero convention. -/
def realEntropySum (masses : List UnitIntervalValue) : ConstructiveReal := listSum (masses.map UnitIntervalValue.entropy)

theorem listSum_append (first second : List ConstructiveReal) :
    Equiv (listSum (first ++ second)) (add (listSum first) (listSum second)) := by
  induction first with
  | nil => exact equiv_symm (zero_add _)
  | cons value rest ih => exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (add_assoc _ _ _))

theorem listSum_perm {first second : List ConstructiveReal} (same : first.Perm second) :
    Equiv (listSum first) (listSum second) := by
  induction same with
  | nil => exact equiv_refl _
  | cons value _ ih => exact add_congr (equiv_refl value) ih
  | swap first second rest =>
      exact equiv_trans (equiv_symm (add_assoc _ _ _))
        (equiv_trans (add_congr (add_comm _ _) (equiv_refl _)) (add_assoc _ _ _))
  | trans _ _ ihFirst ihSecond => exact equiv_trans ihFirst ihSecond

theorem realEntropySum_perm {first second : List UnitIntervalValue} (same : first.Perm second) :
    Equiv (realEntropySum first) (realEntropySum second) := listSum_perm (same.map UnitIntervalValue.entropy)

theorem realEntropySum_cons_zero (mass : UnitIntervalValue) (vanished : Equiv mass.value zero) (rest : List UnitIntervalValue) :
    Equiv (realEntropySum (mass :: rest)) (realEntropySum rest) := by
  have zeroBound : LE zero one := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  have termZero := equiv_trans (realEntropyTerm_congr vanished mass.nonnegative (le_refl zero) mass.bounded zeroBound)
    (realEntropyTerm_zero (le_refl zero) zeroBound)
  exact equiv_trans (add_congr termZero (equiv_refl _)) (zero_add _)

theorem realEntropySum_nonnegative (masses : List UnitIntervalValue) : LE zero (realEntropySum masses) := by
  apply listSum_nonnegative
  intro value member
  obtain ⟨mass, _, rfl⟩ := List.mem_map.mp member
  exact realEntropyTerm_nonnegative mass.value mass.nonnegative mass.bounded

/-- Finite real sums preserve any supplied coordinatewise distance bounds. -/
theorem within_listSum_map (values : List A) (first second : A → ConstructiveReal) (errors : A → QProb)
    (close : ∀ value ∈ values, Within (errors value) (first value) (second value)) :
    Within (QProb.listSum (values.map errors)) (listSum (values.map first)) (listSum (values.map second)) := by
  induction values with
  | nil => exact within_refl QProb.zero zero
  | cons value rest ih =>
      exact within_add (close value (List.mem_cons_self ..))
        (ih (fun other member => close other (List.mem_cons_of_mem _ member)))

/-- An explicit finite entropy error certificate: input radii are computed
coordinatewise from the proved scalar modulus and output errors add. -/
theorem realEntropySum_within (pairs : List (UnitIntervalValue × UnitIntervalValue))
    (precisions : UnitIntervalValue × UnitIntervalValue → PositiveRatio)
    (close : ∀ pair ∈ pairs, Within (entropyInputPrecision (precisions pair)).half.toQProb pair.1.value pair.2.value) :
    Within (QProb.listSum (pairs.map (fun pair => (precisions pair).toQProb)))
      (realEntropySum (pairs.map Prod.fst)) (realEntropySum (pairs.map Prod.snd)) := by
  simp only [realEntropySum, List.map_map]
  exact within_listSum_map pairs _ _ _ (fun pair member =>
    realEntropyTerm_within pair.1.value pair.2.value pair.1.nonnegative pair.2.nonnegative pair.1.bounded pair.2.bounded
      (precisions pair) (close pair member))

/-- Existing finite exact rational entropy, including zeros and unreduced
fractions, is the restriction of the continuous real-coordinate sum. -/
theorem realEntropySum_ofQProb (masses : List {q : QProb // q.num ≤ q.den}) :
    Equiv (realEntropySum (masses.map UnitIntervalValue.ofBoundedQProb))
      (Thesis.Probability.entropySum (masses.map Subtype.val)).interpret := by
  have distributed := ExactLog.interpret_listSum ((masses.map Subtype.val).map Thesis.Probability.entropyTerm)
  simp only [List.map_map] at distributed
  simp only [Thesis.Probability.entropySum, List.map_map]
  apply equiv_trans _ (equiv_symm distributed)
  simp only [realEntropySum, List.map_map]
  exact listSum_map_congr masses _ _ (fun mass _ => UnitIntervalValue.entropy_ofQProb mass.val mass.property)

/-- Natural and bit entropy sums use the same proved ln(2) conversion. -/
theorem realEntropySum_natural (masses : List UnitIntervalValue) :
    Equiv (mul (realEntropySum masses) lnTwo)
      (listSum (masses.map (fun mass => mass.value.naturalEntropyTerm mass.nonnegative mass.bounded))) := by
  have distributed := listSum_mul (masses.map UnitIntervalValue.entropy) lnTwo
  simpa only [realEntropySum, naturalEntropyTerm, UnitIntervalValue.entropy, List.map_map] using distributed

end Thesis.Probability.ConstructiveReal
