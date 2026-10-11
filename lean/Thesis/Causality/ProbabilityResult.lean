import Thesis.Probability.Core

namespace Thesis
namespace Causality

open Probability

/-!
# Model-independent partial finite-rational probability algebra

These are the existing partial-result definitions and proofs formerly housed
in `Semantics`.  Separating them from SCM evaluation keeps elementary support
work independent of the complete probability facade, structural models,
do-calculus soundness, and completeness.  In particular, local checks of
zero-support algebra need not elaborate or import the large causal proof
development.

All declaration names and their meanings are retained.  A missing result is
still genuinely undefined, never an arbitrary value assigned to division by
zero.  Multiplication and sums in this module remain strict in their operands;
the explicitly guarded operations in `SupportAwareSemantics` are separate
constructions with their own support conditions and agreement proofs.

Support witnesses live in `Type` and retain the displayed rational value.
Finite list recursion constructs them directly, without selecting values
from propositional existence proofs or invoking choice.
-/

namespace ProbabilityResult

/--
The partial result of evaluating a probability expression. `none` means that
the expression has no value at this assignment—for example because a
conditioning denominator is zero. It never means the rational number zero.
-/
abbrev Result := Option QProb

/--
Extensional equality for partial results. A supported result may only agree
with another supported result, and their rational values agree by
cross-multiplication through `QProb.Equiv`.
-/
inductive Equivalent : Result -> Result -> Type
  | unsupported : Equivalent none none
  | value {left right : QProb} :
      QProb.Equiv left right -> Equivalent (some left) (some right)

/-- Evidence that a partial probability result has a rational value. -/
def Supported (result : Result) : Type :=
  Sigma fun value => Equivalent result (some value)

/-- A supported partial result with a strictly positive displayed value.

This is data in `Type`, not an existential proposition: a compiler may read
the value and its support witness without choosing a representative.  Keeping
this basic notion beside `Supported` also lets the completeness machinery
establish positivity before importing any do-calculus soundness theorem. -/
structure PositiveSupportedValue (result : Result) where
  value : QProb
  equivalent : Equivalent result (some value)
  positive : 0 < value.num

/-- Forget positivity while retaining the same constructive support value. -/
def PositiveSupportedValue.toSupported {result : Result}
    (positive : PositiveSupportedValue result) : Supported result :=
  ⟨positive.value, positive.equivalent⟩

def refl (result : Result) : Equivalent result result := by
  cases result with
  | none => exact .unsupported
  | some value => exact .value (QProb.equiv_refl value)

def symm {left right : Result} (h : Equivalent left right) :
    Equivalent right left := by
  cases h with
  | unsupported => exact .unsupported
  | value hvalue => exact .value (QProb.equiv_symm hvalue)

def trans {left middle right : Result}
    (hlm : Equivalent left middle) (hmr : Equivalent middle right) :
    Equivalent left right := by
  cases hlm with
  | unsupported =>
      cases hmr
      exact .unsupported
  | value hlmValue =>
      cases hmr with
      | value hmrValue =>
          exact .value (QProb.equiv_trans hlmValue hmrValue)

/-- Support transports across extensional equality of partial results. -/
noncomputable def Supported.transport {left right : Result}
    (equivalent : Equivalent left right) (supported : Supported left) :
    Supported right := by
  rcases supported with ⟨value, hasValue⟩
  exact ⟨value, trans (symm equivalent) hasValue⟩

/-- Addition is defined only when both summands are supported. -/
def add (left right : Result) : Result :=
  match left with
  | none => none
  | some leftValue =>
      match right with
      | none => none
      | some rightValue => some (QProb.add leftValue rightValue)

/-- Multiplication is defined only when both factors are supported. -/
def multiply (left right : Result) : Result :=
  match left with
  | none => none
  | some leftValue =>
      match right with
      | none => none
      | some rightValue => some (QProb.mul leftValue rightValue)

/--
Division propagates failed support and additionally checks that the displayed
denominator has positive numerator. This is the single point at which a
conditional probability can become `none`.
-/
def divide (numerator denominator : Result) : Result :=
  match numerator with
  | none => none
  | some numeratorValue =>
      match denominator with
      | none => none
      | some denominatorValue =>
          if h : 0 < denominatorValue.num then
            some (QProb.div numeratorValue denominatorValue h)
          else
            none

/-- A finite sum is supported exactly when every listed summand is supported. -/
def sum : List Result -> Result
  | [] => some QProb.zero
  | value :: values => add value (sum values)

/-- Support of an addition exposes support of its left summand. -/
def supported_left_of_add {left right : Result}
    (supported : Supported (add left right)) : Supported left := by
  cases left with
  | none =>
      rcases supported with ⟨value, equivalent⟩
      cases right <;> cases equivalent
  | some value =>
      exact ⟨value, .value (QProb.equiv_refl value)⟩

/-- Support of an addition exposes support of its right summand. -/
def supported_right_of_add {left right : Result}
    (supported : Supported (add left right)) : Supported right := by
  cases right with
  | none =>
      rcases supported with ⟨value, equivalent⟩
      cases left <;> cases equivalent
  | some value =>
      exact ⟨value, .value (QProb.equiv_refl value)⟩

/-- Support of a multiplication exposes support of its left factor. -/
def supported_left_of_multiply {left right : Result}
    (supported : Supported (multiply left right)) : Supported left := by
  cases left with
  | none =>
      rcases supported with ⟨value, equivalent⟩
      cases right <;> cases equivalent
  | some value =>
      exact ⟨value, .value (QProb.equiv_refl value)⟩

/-- Support of a multiplication exposes support of its right factor. -/
def supported_right_of_multiply {left right : Result}
    (supported : Supported (multiply left right)) : Supported right := by
  cases right with
  | none =>
      rcases supported with ⟨value, equivalent⟩
      cases left <;> cases equivalent
  | some value =>
      exact ⟨value, .value (QProb.equiv_refl value)⟩

/-- Support of a quotient exposes support of its numerator. -/
def supported_numerator_of_divide {numerator denominator : Result}
    (supported : Supported (divide numerator denominator)) :
    Supported numerator := by
  cases numerator with
  | none =>
      rcases supported with ⟨value, equivalent⟩
      cases denominator <;> cases equivalent
  | some value =>
      exact ⟨value, .value (QProb.equiv_refl value)⟩

/-- Support of a quotient exposes support of its denominator. -/
def supported_denominator_of_divide {numerator denominator : Result}
    (supported : Supported (divide numerator denominator)) :
    Supported denominator := by
  cases denominator with
  | none =>
      rcases supported with ⟨value, equivalent⟩
      cases numerator <;> cases equivalent
  | some value =>
      exact ⟨value, .value (QProb.equiv_refl value)⟩

/--
Every mapped member of a supported finite sum is itself supported.  The
explicit decidable equality follows the concrete source list instead of
eliminating propositional membership into support data; this keeps the
construction choice-free.
-/
noncomputable def supported_map_of_mem_sum {X : Type} [DecidableEq X]
    (values : List X) (term : X -> Result) (value : X)
    (member : value ∈ values)
    (supported : Supported (sum (values.map term))) : Supported (term value) := by
  induction values with
  | nil =>
      simp at member
  | cons head tail inductionHypothesis =>
      if equal : value = head then
        subst value
        exact supported_left_of_add supported
      else
        have later : value ∈ tail :=
          (List.mem_cons.mp member).resolve_left equal
        exact inductionHypothesis later (supported_right_of_add supported)

def add_congr {left left' right right' : Result}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    Equivalent (add left right) (add left' right') := by
  cases hleft with
  | unsupported =>
      cases hright <;> exact .unsupported
  | value hleftValue =>
      cases hright with
      | unsupported => exact .unsupported
      | value hrightValue =>
          exact .value (QProb.add_congr hleftValue hrightValue)

def multiply_congr {left left' right right' : Result}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    Equivalent (multiply left right) (multiply left' right') := by
  cases hleft with
  | unsupported =>
      cases hright <;> exact .unsupported
  | value hleftValue =>
      cases hright with
      | unsupported => exact .unsupported
      | value hrightValue =>
          exact .value (QProb.mul_congr hleftValue hrightValue)

/-- Commutativity preserves both rational values and failed support.
No positivity premise is needed, and an undefined factor is not silently
replaced by zero.  These are intrinsic algebra laws, not fields added to
the externally supplied primitive do-rule semantics. -/
def multiply_comm (left right : Result) :
    Equivalent (multiply left right) (multiply right left) := by
  cases left with
  | none => cases right <;> exact .unsupported
  | some leftValue =>
      cases right with
      | none => exact .unsupported
      | some rightValue => exact .value (QProb.mul_comm leftValue rightValue)

/-- Associativity is valid even when one or more factors are undefined.
The supported case is exactly the constructive cross-multiplication law
for the existing finite-rational representation. -/
def multiply_assoc (first second third : Result) :
    Equivalent (multiply (multiply first second) third)
      (multiply first (multiply second third)) := by
  cases first with
  | none => cases second <;> cases third <;> exact .unsupported
  | some firstValue =>
      cases second with
      | none => cases third <;> exact .unsupported
      | some secondValue =>
          cases third with
          | none => exact .unsupported
          | some thirdValue =>
              exact .value (QProb.mul_assoc firstValue secondValue thirdValue)

def divide_congr {left left' right right' : Result}
    (hleft : Equivalent left left') (hright : Equivalent right right') :
    Equivalent (divide left right) (divide left' right') := by
  cases hleft with
  | unsupported =>
      cases hright <;> exact .unsupported
  | value hleftValue =>
      cases hright with
      | unsupported => exact .unsupported
      | value hrightValue =>
          rename_i numerator numerator' denominator denominator'
          by_cases hpos : 0 < denominator.num
          · have hpos' : 0 < denominator'.num :=
              (QProb.equiv_num_pos_iff hrightValue).mp hpos
            simp only [divide, dif_pos hpos, dif_pos hpos']
            exact .value
              (QProb.div_congr hleftValue hrightValue hpos hpos')
          · have hpos' : Not (0 < denominator'.num) := by
              intro positive
              exact hpos ((QProb.equiv_num_pos_iff hrightValue).mpr positive)
            simp only [divide, dif_neg hpos, dif_neg hpos']
            exact .unsupported

/-- Dividing two ratios with the same supported denominator cancels it. -/
noncomputable def divide_divide_cancel (numerator middle denominator : QProb)
    (leftSupported : Supported (divide (some numerator) (some middle)))
    (rightSupported : Supported
      (divide
        (divide (some numerator) (some denominator))
        (divide (some middle) (some denominator)))) :
    Equivalent
      (divide (some numerator) (some middle))
      (divide
        (divide (some numerator) (some denominator))
        (divide (some middle) (some denominator))) := by
  by_cases middlePositive : 0 < middle.num
  · by_cases denominatorPositive : 0 < denominator.num
    · have dividedMiddlePositive :
          0 < (QProb.div middle denominator denominatorPositive).num :=
        Nat.mul_pos middlePositive denominator.den_pos
      simp only [divide, dif_pos middlePositive,
        dif_pos denominatorPositive, dif_pos dividedMiddlePositive]
      apply Equivalent.value
      simp only [QProb.Equiv, QProb.div]
      ac_rfl
    · simp only [divide, dif_neg denominatorPositive] at rightSupported
      rcases rightSupported with ⟨_, impossible⟩
      cases impossible
  · simp only [divide, dif_neg middlePositive] at leftSupported
    rcases leftSupported with ⟨_, impossible⟩
    cases impossible

/-- The supported product of two adjacent conditional ratios is their chain. -/
noncomputable def divide_multiply_chain
    (numerator middle denominator : QProb)
    (leftSupported : Supported
      (divide (some numerator) (some denominator)))
    (rightSupported : Supported
      (multiply
        (divide (some numerator) (some middle))
        (divide (some middle) (some denominator)))) :
    Equivalent
      (divide (some numerator) (some denominator))
      (multiply
        (divide (some numerator) (some middle))
        (divide (some middle) (some denominator))) := by
  by_cases denominatorPositive : 0 < denominator.num
  · by_cases middlePositive : 0 < middle.num
    · simp only [divide, dif_pos denominatorPositive,
        dif_pos middlePositive, multiply]
      apply Equivalent.value
      simp only [QProb.Equiv, QProb.div, QProb.mul]
      ac_rfl
    · simp only [divide, dif_neg middlePositive, multiply] at rightSupported
      rcases rightSupported with ⟨_, impossible⟩
      cases impossible
  · simp only [divide, dif_neg denominatorPositive] at leftSupported
    rcases leftSupported with ⟨_, impossible⟩
    cases impossible

noncomputable def sum_map_congr (values : List X) (left right : X -> Result)
    (h : forall value, Equivalent (left value) (right value)) :
    Equivalent (sum (values.map left)) (sum (values.map right)) := by
  induction values with
  | nil => exact refl _
  | cons value values ih =>
      exact add_congr (h value) ih

noncomputable def sum_map_congr_mem (values : List X)
    (left right : X -> Result)
    (h : forall value, value ∈ values -> Equivalent (left value) (right value)) :
    Equivalent (sum (values.map left)) (sum (values.map right)) := by
  induction values with
  | nil => exact refl _
  | cons value values ih =>
      exact add_congr (h value (by simp))
        (ih (fun member memberIn => h member (by simp [memberIn])))

/--
Finite sums preserve merely inhabited pointwise equivalence without choosing
a global family of equivalence witnesses.  The list recursion opens one
`Nonempty` at a time while its result remains proposition-valued, so this is
the constructive bridge used by extensional kernel relations whose public
interface intentionally hides proof data behind `Nonempty`.
-/
theorem sum_map_congr_nonempty (values : List X) (left right : X -> Result)
    (h : forall value, Nonempty (Equivalent (left value) (right value))) :
    Nonempty (Equivalent (sum (values.map left)) (sum (values.map right))) := by
  induction values with
  | nil =>
      exact ⟨refl _⟩
  | cons value values ih =>
      rcases h value with ⟨head⟩
      rcases ih with ⟨tail⟩
      exact ⟨add_congr head tail⟩

theorem sum_some_map (values : List X) (value : X -> QProb) :
    sum (values.map (fun item => some (value item))) =
      some (QProb.listSum (values.map value)) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, sum, add, QProb.listSum]
      rw [ih]

/-- A finite sum of ratios with one supported denominator is their summed ratio. -/
noncomputable def divide_listSum_same_denominator
    (values : List QProb) (denominator : QProb)
    (supported : Supported
      (divide (some (QProb.listSum values)) (some denominator))) :
    Equivalent
      (divide (some (QProb.listSum values)) (some denominator))
      (sum (values.map (fun value => divide (some value) (some denominator)))) := by
  by_cases positive : 0 < denominator.num
  · simp only [divide, dif_pos positive]
    rw [sum_some_map values (fun value => QProb.div value denominator positive)]
    exact .value (QProb.div_listSum_same_denominator values denominator positive)
  · simp only [divide, dif_neg positive] at supported
    rcases supported with ⟨_, impossible⟩
    cases impossible

def add_supported {left right : Result}
    (leftSupported : Sigma fun value => Equivalent left (some value))
    (rightSupported : Sigma fun value => Equivalent right (some value)) :
    Sigma fun value => Equivalent (add left right) (some value) := by
  rcases leftSupported with ⟨leftValue, hleft⟩
  rcases rightSupported with ⟨rightValue, hright⟩
  exact ⟨QProb.add leftValue rightValue,
    add_congr hleft hright⟩

def multiply_supported {left right : Result}
    (leftSupported : Sigma fun value => Equivalent left (some value))
    (rightSupported : Sigma fun value => Equivalent right (some value)) :
    Sigma fun value => Equivalent (multiply left right) (some value) := by
  rcases leftSupported with ⟨leftValue, hleft⟩
  rcases rightSupported with ⟨rightValue, hright⟩
  exact ⟨QProb.mul leftValue rightValue,
    multiply_congr hleft hright⟩

noncomputable def sum_map_supported (values : List X) (term : X -> Result)
    (supported : forall value,
      Sigma fun result => Equivalent (term value) (some result)) :
    Sigma fun result => Equivalent (sum (values.map term)) (some result) := by
  induction values with
  | nil =>
      exact ⟨QProb.zero, refl _⟩
  | cons value values ih =>
      exact add_supported (supported value) ih

/--
A finite mapped sum is supported when every value that actually occurs in
the enumerated list is supported.  Unlike `sum_map_supported`, this sharper
form does not ask the caller to prove an irrelevant global statement about
values outside the finite enumeration.
-/
noncomputable def sum_map_supported_of_mem (values : List X)
    (term : X -> Result)
    (supported : forall value, value ∈ values ->
      Sigma fun result => Equivalent (term value) (some result)) :
    Sigma fun result => Equivalent (sum (values.map term)) (some result) := by
  induction values with
  | nil =>
      exact ⟨QProb.zero, refl _⟩
  | cons value values inductionHypothesis =>
      exact add_supported
        (supported value (List.mem_cons.mpr (Or.inl rfl)))
        (inductionHypothesis fun member memberIn =>
          supported member (List.mem_cons.mpr (Or.inr memberIn)))

/-! ## Positive support for recursive kernel expressions -/

/-- A supported partial quotient contains a supported denominator with a
positive numerator.  Inspecting the operands and the executable natural
positivity test yields data in `Type`; no witness is selected from a
propositional existence claim.  This basic support fact is independent of
the graph, the selected model class, and do-calculus soundness. -/
def positiveDenominatorOfSupportedDivide
    {numerator denominator : Result}
    (supported : Supported (divide numerator denominator)) :
    PositiveSupportedValue denominator := by
  cases numerator with
  | none =>
      rcases supported with ⟨value, equivalent⟩
      cases denominator <;> cases equivalent
  | some numeratorValue =>
      cases denominator with
      | none =>
          rcases supported with ⟨value, equivalent⟩
          cases equivalent
      | some denominatorValue =>
          by_cases positive : 0 < denominatorValue.num
          · exact {
              value := denominatorValue
              equivalent := .value (QProb.equiv_refl denominatorValue)
              positive := positive
            }
          · rw [divide, dif_neg positive] at supported
            rcases supported with ⟨value, equivalent⟩
            cases equivalent

/-- Transport a positive support value across extensional result equality.
Only the direction of the equality changes; the rational representative and
its positivity proof remain explicit data. -/
def PositiveSupportedValue.transport {left right : Result}
    (equivalent : Equivalent left right)
    (positive : PositiveSupportedValue left) :
    PositiveSupportedValue right :=
  ⟨positive.value, trans (symm equivalent) positive.equivalent,
    positive.positive⟩

/-- A product of positive supported results is positive and supported. -/
def PositiveSupportedValue.multiply {left right : Result}
    (leftPositive : PositiveSupportedValue left)
    (rightPositive : PositiveSupportedValue right) :
    PositiveSupportedValue (multiply left right) where
  value := QProb.mul leftPositive.value rightPositive.value
  equivalent := multiply_congr leftPositive.equivalent rightPositive.equivalent
  positive := Nat.mul_pos leftPositive.positive rightPositive.positive

/-- A positive denominator makes the quotient of two positive results
defined.  Its numerator is the old numerator times the denominator's
strictly positive rational denominator, so positivity is constructive too. -/
def PositiveSupportedValue.divide {numerator denominator : Result}
    (numeratorPositive : PositiveSupportedValue numerator)
    (denominatorPositive : PositiveSupportedValue denominator) :
    PositiveSupportedValue (divide numerator denominator) where
  value := QProb.div numeratorPositive.value denominatorPositive.value
    denominatorPositive.positive
  equivalent := by
    have operands := divide_congr numeratorPositive.equivalent
      denominatorPositive.equivalent
    simpa only [ProbabilityResult.divide, dif_pos denominatorPositive.positive]
      using operands
  positive := Nat.mul_pos numeratorPositive.positive
    denominatorPositive.value.den_pos

/-- A nonempty finite sum of positive supported terms remains positive.

Only the head contributes to the strict lower bound; the tail needs support
and has a nonnegative value.  Inspecting the list directly handles the empty
case without a classical characterization of `list = []`.  In particular,
this lemma is suitable for the enumerated marginals of recursive ID inputs. -/
noncomputable def PositiveSupportedValue.sum_map (values : List X)
    (term : X -> Result) (nonempty : values ≠ [])
    (positive : forall value, value ∈ values ->
      PositiveSupportedValue (term value)) :
    PositiveSupportedValue (sum (values.map term)) := by
  cases values with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      let headPositive := positive head (List.mem_cons.mpr (Or.inl rfl))
      let tailSupported := sum_map_supported_of_mem tail term
        (fun value member =>
          (positive value (List.mem_cons.mpr (Or.inr member))).toSupported)
      refine ⟨QProb.add headPositive.value tailSupported.1,
        add_congr headPositive.equivalent tailSupported.2, ?_⟩
      have leading := Nat.mul_pos headPositive.positive tailSupported.1.den_pos
      change 0 < headPositive.value.num * tailSupported.1.den +
        tailSupported.1.num * headPositive.value.den
      omega

end ProbabilityResult

end Causality
end Thesis
