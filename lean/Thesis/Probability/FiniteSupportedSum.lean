import Thesis.Probability.ConstructivePermutation

namespace Thesis
namespace Probability
namespace FiniteSupportedSum

/-!
# Exact elimination of zero terms from a finite integer sum

A complete expansion can contain many terms that integrate to zero.  A
shorter list of canonical terms gives the same literal sum only after its
membership, uniqueness and zero-outside facts are proved.  In particular,
dropping duplicates is not valid when the complete expansion counts them.

The reduction theorem retains those obligations explicitly.  An exact
permutation-sum lemma also compares complete enumerations before reduction.
Equality decisions are supplied for the finite labels; no proposition about
semantic nonzeroness is decided classically.  Integers are auxiliary
integrands, not signed probability weights or a change in the underlying
finite-record semantics.
-/

/-- Reordering a complete finite list of integer terms preserves its exact
sum.  Negative character contributions remain ordinary auxiliary integers;
the identity introduces no signed probability or cancellation hypothesis. -/
theorem sum_eq_of_perm {left right : List Int} (permutation : left.Perm right) : left.sum = right.sum := by
  induction permutation with
  | nil => rfl
  | cons value _ inductionHypothesis => simp only [List.sum_cons, inductionHypothesis]
  | swap left right rest => exact Int.add_left_comm _ _ _
  | trans _ _ leftEqual rightEqual => exact leftEqual.trans rightEqual

/-- Restrict a literal integer sum by a Boolean filter only after every
rejected occurrence is proved zero.  Duplicate occurrences are retained;
neither list uniqueness nor a semantic equality decision is needed. -/
theorem sum_eq_filter_of_zero (values : List α) (keep : α -> Bool) (term : α -> Int)
    (zero : forall value, value ∈ values -> keep value = false -> term value = 0) :
    (values.map term).sum = ((values.filter keep).map term).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      have tailZero : forall item, item ∈ rest -> keep item = false -> term item = 0 :=
        fun item member absent => zero item (List.mem_cons_of_mem value member) absent
      cases selected : keep value with
      | true => simp only [List.map_cons, List.sum_cons, List.filter_cons, selected, if_true,
          inductionHypothesis tailZero]
      | false => simp only [List.map_cons, List.sum_cons, List.filter_cons, selected, Bool.false_eq_true,
          if_false, zero value List.mem_cons_self selected, Int.zero_add, inductionHypothesis tailZero]

/-- Pull an actual constant scalar outside a complete integer sum.  This
does not replace varying forced indicators by their consistent value. -/
theorem sum_mul_left (values : List α) (term : α -> Int) (factor : Int) :
    (values.map (fun value => factor * term value)).sum = factor * (values.map term).sum := by
  induction values with
  | nil => exact (Int.mul_zero factor).symm
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis, Int.mul_add]

/-- Distribute one literal finite sum over two integrands on its same
support.  All occurrences and both signs remain present. -/
theorem sum_add (values : List α) (left right : α -> Int) :
    (values.map (fun value => left value + right value)).sum =
      (values.map left).sum + (values.map right).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis]
      ac_rfl

/-- Interchange two explicitly supplied finite sums, without integrating
against a replacement probability record or choosing an enumeration. -/
theorem sum_swap (left : List α) (right : List β) (term : α -> β -> Int) :
    (left.map (fun first => (right.map (term first)).sum)).sum =
      (right.map (fun second => (left.map (fun first => term first second)).sum)).sum := by
  induction left with
  | nil =>
      change 0 = (right.map (fun _ => (0 : Int))).sum
      induction right with
      | nil => rfl
      | cons value rest inductionHypothesis =>
          rw [List.map_cons, List.sum_cons, ← inductionHypothesis]
          rfl
  | cons first rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [sum_add, inductionHypothesis]

/-- Negate every actual summand without altering the supplied support or
its multiplicities.  This elementary identity is used after an explicitly
proved sign-reversing reindexing, not as an assumption of cancellation. -/
theorem sum_neg (values : List α) (term : α -> Int) :
    (values.map (fun value => -(term value))).sum = -((values.map term).sum) := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis, Int.neg_add]

/-- An explicit sign-reversing involution on a nonredundant finite support
makes its complete integer sum zero.  Closure and the displayed inverse
construct a permutation of the same support; no inverse or paired element
is selected from an existential proposition.  Fixed points are allowed only
when their summand satisfies the supplied sign reversal, hence is zero. -/
theorem sum_zero_of_involution {α : Type u} [DecidableEq α]
    (values : List α) (nodup : values.Nodup) (shift : α -> α)
    (inverse : forall value, shift (shift value) = value)
    (closed : forall value, value ∈ values -> shift value ∈ values)
    (term : α -> Int) (opposite : forall value, value ∈ values -> term (shift value) = -(term value)) :
    (values.map term).sum = 0 := by
  have injective : forall first, first ∈ values -> forall second, second ∈ values ->
      shift first = shift second -> first = second := by
    intro first _firstListed second _secondListed same
    exact (inverse first).symm.trans ((congrArg shift same).trans (inverse second))
  have sameMembers : forall value, value ∈ values.map shift ↔ value ∈ values := by
    intro value
    constructor
    · intro member
      rcases List.mem_map.mp member with ⟨old, listed, same⟩
      exact same ▸ closed old listed
    · intro member
      exact List.mem_map.mpr ⟨shift value, closed value member, inverse value⟩
  have permutation := ConstructivePermutation.perm_of_nodup_mem_iff (values.map shift) values
    (ConstructivePermutation.nodup_map_of_injective_on shift values injective nodup) nodup sameMembers
  have reordered := sum_eq_of_perm (permutation.map term)
  have negated := congrArg List.sum (List.map_congr_left (l := values) opposite)
  simp only [List.map_map, Function.comp_def] at reordered
  have oppositeSum := reordered.symm.trans (negated.trans (sum_neg values term))
  omega

/-- If every actual listed occurrence contributes zero, the complete sum
is zero.  The supplied list is retained verbatim, so duplicate labels do
not require a separate uniqueness or multiplicity argument. -/
theorem sum_eq_zero (values : List α) (term : α -> Int)
    (zero : forall value, value ∈ values -> term value = 0) : (values.map term).sum = 0 := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, zero value List.mem_cons_self,
        inductionHypothesis (fun other listed => zero other (List.mem_cons_of_mem value listed)), Int.zero_add]

/-- Nonnegative complete terms give a nonnegative sum.  Nonnegativity is
required at every listed occurrence, not inferred from one positive cell. -/
theorem sum_nonneg (values : List α) (term : α -> Int)
    (nonnegative : forall value, value ∈ values -> 0 <= term value) :
    0 <= (values.map term).sum := by
  induction values with
  | nil => exact Int.le_refl _
  | cons value rest inductionHypothesis =>
      exact Int.add_nonneg (nonnegative value List.mem_cons_self)
        (inductionHypothesis (fun other member => nonnegative other (List.mem_cons_of_mem value member)))

/-- One explicitly supplied positive listed term makes the complete sum
strictly positive when all the other listed terms are nonnegative.  No term
is selected from an existential proposition and no multiplicity is dropped. -/
theorem sum_pos_of_mem (values : List α) (term : α -> Int)
    (nonnegative : forall value, value ∈ values -> 0 <= term value)
    (chosen : α) (listed : chosen ∈ values) (positive : 0 < term chosen) :
    0 < (values.map term).sum := by
  induction values with
  | nil => exact False.elim (List.not_mem_nil listed)
  | cons value rest inductionHypothesis =>
      have tailNonnegative := fun other member => nonnegative other (List.mem_cons_of_mem value member)
      have headNonnegative := nonnegative value List.mem_cons_self
      have tailSum := sum_nonneg rest term tailNonnegative
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp listed with same | inTail
      · have headPositive : 0 < term value := same ▸ positive
        omega
      · have tailPositive := inductionHypothesis tailNonnegative inTail
        omega

/-- A repetition-free sublist of canonical terms has the same exact sum
as a repetition-free complete list when every omitted term is proved zero.
Only membership in the supplied finite canonical list is tested. -/
theorem sum_eq_of_zero_outside {α : Type u} [DecidableEq α] (complete canonical : List α)
    (completeNodup : complete.Nodup) (canonicalNodup : canonical.Nodup)
    (included : forall value, value ∈ canonical -> value ∈ complete) (term : α -> Int)
    (zero : forall value, value ∈ complete -> value ∉ canonical -> term value = 0) :
    (complete.map term).sum = (canonical.map term).sum := by
  let keep := fun value => decide (value ∈ canonical)
  have filteredNodup := List.Pairwise.filter keep completeNodup
  have same : forall value, value ∈ complete.filter keep ↔ value ∈ canonical := by
    intro value
    constructor
    · intro member
      exact of_decide_eq_true (List.mem_filter.mp member).2
    · intro member
      exact List.mem_filter.mpr ⟨included value member, decide_eq_true member⟩
  have permutation := ConstructivePermutation.perm_of_nodup_mem_iff
    (complete.filter keep) canonical filteredNodup canonicalNodup same
  refine (sum_eq_filter_of_zero complete keep term ?_).trans (sum_eq_of_perm (permutation.map term))
  intro value member absent
  exact zero value member (of_decide_eq_false absent)

end FiniteSupportedSum
end Probability
end Thesis
