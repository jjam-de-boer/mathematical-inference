import Thesis.Causality.DerivationEnumeration

namespace Thesis.Causality.ProbabilityCode

/-!
# Counting serialized search spaces without constructing them

The recurrences below count list entries, including every raw code that the
checker will later reject. They do not count only distinct printed formulas
or only successful certificates. In particular, filtering is not a way to
avoid the cost of constructing an enormous input list.

Exact arithmetic specifies the count. The executable preflight will use the
separate saturated recurrences: all intermediate counts are clipped at one
above the caller's limit. Their equality to the clipped exact counts is
proved, rather than inferred from a collection of numerical examples.
Depth limits still have to be checked before running a recurrence. Saturated
arithmetic bounds integer growth, not the number of recursive calls.
-/

namespace CodeEnumeration

theorem length_flatMap_constant (values : List A) (build : A → List B) (size : Nat)
    (same : ∀ value, (build value).length = size) :
    (values.flatMap build).length = values.length * size := by
  induction values with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, same, inductionHypothesis,
        List.length_cons, Nat.succ_mul]
      omega

theorem length_binary (constructor : A → B → C) (first : List A) (second : List B) :
    (binary constructor first second).length = first.length * second.length :=
  length_flatMap_constant first _ second.length (fun _ => List.length_map _)

theorem length_ternary (constructor : A → B → C → D)
    (first : List A) (second : List B) (third : List C) :
    (ternary constructor first second third).length = first.length * (second.length * third.length) :=
  length_flatMap_constant first _ _ (fun _ => length_binary _ second third)

end CodeEnumeration

namespace CodeCount

def kernel (dictionary : CodeDictionaries) : Nat :=
  dictionary.masks * (dictionary.masks * dictionary.masks)

def quad (dictionary : CodeDictionaries) : Nat :=
  dictionary.masks * kernel dictionary

def term (dictionary : CodeDictionaries) : Nat → Nat
  | 0 => 0
  | depth + 1 =>
      let smaller := term dictionary depth
      1 + kernel dictionary + dictionary.masks * smaller + dictionary.references * smaller +
        smaller * smaller + smaller * smaller + smaller * smaller + smaller * smaller

def derivation (dictionary : CodeDictionaries) (expressionDepth : Nat) : Nat → Nat
  | 0 => 0
  | depth + 1 =>
      let terms := term dictionary expressionDepth
      let smaller := derivation dictionary expressionDepth depth
      terms + smaller + smaller * smaller + 7 * quad dictionary + terms * terms +
        terms * (terms * terms) + dictionary.masks * smaller + dictionary.references * smaller +
        4 * (smaller * smaller) + terms * (terms * smaller)

/-- The native wrapper consumes one level. `actionOne` is a separate leaf;
its kernel indices do not require an explicit `TermCode` field. -/
def native (dictionary : CodeDictionaries) (expressionDepth : Nat) : Nat → Nat
  | 0 => 0
  | depth + 1 => derivation dictionary expressionDepth depth + kernel dictionary

theorem kernel_eq_length (dictionary : CodeDictionaries) :
    kernel dictionary = (KernelCode.enumerate dictionary).length := by
  simp only [kernel, KernelCode.enumerate, CodeEnumeration.length_ternary, List.length_range]

theorem quad_eq_length (dictionary : CodeDictionaries) :
    quad dictionary = (QuadCode.enumerate dictionary).length := by
  rw [QuadCode.enumerate, CodeEnumeration.length_flatMap_constant _ _ (kernel dictionary)]
  · simp only [List.length_range, quad]
  · intro value
    simp only [CodeEnumeration.length_ternary, List.length_range, kernel]

theorem term_eq_length (dictionary : CodeDictionaries) (depth : Nat) :
    term dictionary depth = (TermCode.enumerate dictionary depth).length := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [term, TermCode.enumerate, List.length_append, List.length_map,
        CodeEnumeration.length_binary, List.length_cons, List.length_nil, List.length_range,
        ← kernel_eq_length, ← inductionHypothesis, Nat.zero_add, Nat.add_assoc]

theorem derivation_eq_length (dictionary : CodeDictionaries) (expressionDepth proofDepth : Nat) :
    derivation dictionary expressionDepth proofDepth =
      (DerivationCode.enumerate dictionary expressionDepth proofDepth).length := by
  induction proofDepth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [derivation, DerivationCode.enumerate, List.length_append, List.length_map,
        CodeEnumeration.length_binary, CodeEnumeration.length_ternary, List.length_range,
        ← term_eq_length, ← quad_eq_length, ← inductionHypothesis,
        PrimitiveCode.enumerate, CongruenceCode.enumerate, List.length_cons, List.length_nil,
        Nat.add_assoc]

end CodeCount

namespace CappedCount

/-- `limit + 1` is an overflow sentinel, never a purported exact count. -/
def clip (limit value : Nat) : Nat := min value (limit + 1)

def add (limit left right : Nat) : Nat := clip limit (left + right)
def mul (limit left right : Nat) : Nat := clip limit (left * right)

@[simp] theorem clip_zero (limit : Nat) : clip limit 0 = 0 := by simp [clip]

theorem clip_le (limit value : Nat) : clip limit value ≤ limit + 1 := Nat.min_le_right _ _

theorem clip_le_iff (limit value : Nat) : clip limit value ≤ limit ↔ value ≤ limit := by
  unfold clip
  omega

theorem clip_add (limit left right : Nat) :
    add limit (clip limit left) (clip limit right) = clip limit (left + right) := by
  unfold add clip
  omega

private theorem clip_mul_left (limit left right : Nat) :
    clip limit (clip limit left * right) = clip limit (left * right) := by
  by_cases small : left ≤ limit + 1
  · simp only [clip, Nat.min_eq_left small]
  · have large : limit + 1 ≤ left := by omega
    by_cases zero : right = 0
    · simp [zero]
    · have positive : 1 ≤ right := by omega
      have cappedLarge : limit + 1 ≤ (limit + 1) * right := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (limit + 1) positive
      have actualLarge : limit + 1 ≤ left * right :=
        Nat.le_trans large (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left left positive)
      simp only [clip, Nat.min_eq_right large, Nat.min_eq_right cappedLarge, Nat.min_eq_right actualLarge]

theorem clip_mul (limit left right : Nat) :
    mul limit (clip limit left) (clip limit right) = clip limit (left * right) := by
  unfold mul
  rw [clip_mul_left, Nat.mul_comm left, clip_mul_left, Nat.mul_comm right]

def kernel (limit : Nat) (dictionary : CodeDictionaries) : Nat :=
  mul limit (clip limit dictionary.masks)
    (mul limit (clip limit dictionary.masks) (clip limit dictionary.masks))

def quad (limit : Nat) (dictionary : CodeDictionaries) : Nat :=
  mul limit (clip limit dictionary.masks) (kernel limit dictionary)

def term (limit : Nat) (dictionary : CodeDictionaries) : Nat → Nat
  | 0 => 0
  | depth + 1 =>
      let smaller := term limit dictionary depth
      let sum := add limit
      let product := mul limit
      sum (sum (sum (sum (sum (sum (sum (clip limit 1) (kernel limit dictionary))
        (product (clip limit dictionary.masks) smaller))
        (product (clip limit dictionary.references) smaller))
        (product smaller smaller)) (product smaller smaller))
        (product smaller smaller)) (product smaller smaller)

def derivation (limit : Nat) (dictionary : CodeDictionaries) (expressionDepth : Nat) : Nat → Nat
  | 0 => 0
  | depth + 1 =>
      let terms := term limit dictionary expressionDepth
      let smaller := derivation limit dictionary expressionDepth depth
      let sum := add limit
      let product := mul limit
      sum (sum (sum (sum (sum (sum (sum (sum (sum terms smaller) (product smaller smaller))
        (product (clip limit 7) (quad limit dictionary))) (product terms terms))
        (product terms (product terms terms))) (product (clip limit dictionary.masks) smaller))
        (product (clip limit dictionary.references) smaller))
        (product (clip limit 4) (product smaller smaller))) (product terms (product terms smaller))

def native (limit : Nat) (dictionary : CodeDictionaries) (expressionDepth : Nat) : Nat → Nat
  | 0 => 0
  | depth + 1 => add limit (derivation limit dictionary expressionDepth depth) (kernel limit dictionary)

theorem kernel_exact (limit : Nat) (dictionary : CodeDictionaries) :
    kernel limit dictionary = clip limit (CodeCount.kernel dictionary) := by
  simp only [kernel, CodeCount.kernel, clip_mul]

theorem quad_exact (limit : Nat) (dictionary : CodeDictionaries) :
    quad limit dictionary = clip limit (CodeCount.quad dictionary) := by
  simp only [quad, CodeCount.quad, kernel_exact, clip_mul]

theorem term_exact (limit : Nat) (dictionary : CodeDictionaries) (depth : Nat) :
    term limit dictionary depth = clip limit (CodeCount.term dictionary depth) := by
  induction depth with
  | zero => simp only [term, CodeCount.term, clip_zero]
  | succ depth inductionHypothesis =>
      simp only [term, CodeCount.term, inductionHypothesis, kernel_exact, clip_mul, clip_add]

theorem derivation_exact (limit : Nat) (dictionary : CodeDictionaries) (expressionDepth proofDepth : Nat) :
    derivation limit dictionary expressionDepth proofDepth =
      clip limit (CodeCount.derivation dictionary expressionDepth proofDepth) := by
  induction proofDepth with
  | zero => simp only [derivation, CodeCount.derivation, clip_zero]
  | succ depth inductionHypothesis =>
      simp only [derivation, CodeCount.derivation, term_exact, inductionHypothesis, quad_exact, clip_mul, clip_add]

theorem native_exact (limit : Nat) (dictionary : CodeDictionaries) (expressionDepth proofDepth : Nat) :
    native limit dictionary expressionDepth proofDepth =
      clip limit (CodeCount.native dictionary expressionDepth proofDepth) := by
  cases proofDepth <;>
    simp only [native, CodeCount.native, clip_zero, derivation_exact, kernel_exact, clip_add]

end CappedCount
end Thesis.Causality.ProbabilityCode
