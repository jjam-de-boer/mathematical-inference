import Thesis.Probability.Distros.RationalLinearHomogenization
import Thesis.Probability.Distros.RationalSimplex
import Thesis.Probability.RationalReciprocal

/-!
# Rational row-space certificates for finite measurements

The rational row span of integer measurement rows is represented by
clearing a common positive denominator. The elimination trace for a
hypothetical separating direction supplies a positive integer multiplier
of the query. Every projection row in that trace is made by adding and
positively scaling existing rows. No real-valued choice or rational
denominator bound is used.
-/

namespace Thesis.Probability.Distros.RationalLinear

/-- Integer combinations, kept as a finite derivation so that generators
with duplicate presentations can be used or omitted independently. -/
inductive IntegerSpan (rows : List (Fin n → Int)) : (Fin n → Int) → Prop
  | zero : IntegerSpan rows (fun _ => 0)
  | member (row : Fin n → Int) (listed : row ∈ rows) : IntegerSpan rows row
  | add {left right} : IntegerSpan rows left → IntegerSpan rows right →
      IntegerSpan rows (fun i => left i + right i)
  | scale (factor : Int) {row} : IntegerSpan rows row → IntegerSpan rows (fun i => factor * row i)

/-- The standard common-denominator presentation of the rational row span.
Dividing the integer combination by its positive denominator gives
rational row coefficients. Conversely any finite rational combination
has a positive common denominator. -/
def RationalSpan (rows : List (Fin n → Int)) (query : Fin n → Int) : Prop :=
  ∃ denominator : Nat, 0 < denominator ∧ IntegerSpan rows (fun i => (denominator : Int) * query i)

private def addRows (left right : Inequality n) : Inequality n :=
  ⟨fun i => left.coefficients i + right.coefficients i, SignedRatio.add left.bound right.bound⟩

private def scaleRow (factor : Int) (row : Inequality n) : Inequality n :=
  ⟨fun i => factor * row.coefficients i, SignedRatio.scaleInt factor row.bound⟩

/-- A full-dimensional nonnegative combination of supplied inequalities. -/
private inductive Derived (rows : List (Inequality n)) : Inequality n → Prop
  | member (row : Inequality n) (listed : row ∈ rows) : Derived rows row
  | add {left right} : Derived rows left → Derived rows right → Derived rows (addRows left right)
  | scale (factor : Int) (positive : 0 ≤ factor) {row} : Derived rows row → Derived rows (scaleRow factor row)

private theorem Inequality.same {left right : Inequality n}
    (coefficients : ∀ i, left.coefficients i = right.coefficients i) (bound : left.bound = right.bound) :
    left = right := by
  cases left
  cases right
  cases funext coefficients
  cases bound
  rfl

private theorem extendZero_earlier (row : Inequality n) (i : Fin n) :
    row.extendZero.coefficients i.castSucc = row.coefficients i := by
  change (if earlier : i.val < n then row.coefficients ⟨i.val, earlier⟩ else 0) = _
  rw [dif_pos i.isLt]

private theorem extendZero_final (row : Inequality n) :
    row.extendZero.coefficients (Fin.last n) = 0 := by
  change (if earlier : n < n then row.coefficients ⟨n, earlier⟩ else 0) = _
  rw [dif_neg (Nat.lt_irrefl n)]

private theorem extendZero_add (left right : Inequality n) :
    (addRows left right).extendZero = addRows left.extendZero right.extendZero := by
  refine Inequality.same ?_ rfl
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [addRows, extendZero_final, Int.add_zero]
  · simp only [addRows, extendZero_earlier]

private theorem extendZero_scale (factor : Int) (row : Inequality n) :
    (scaleRow factor row).extendZero = scaleRow factor row.extendZero := by
  refine Inequality.same ?_ rfl
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [scaleRow, extendZero_final, Int.mul_zero]
  · simp only [scaleRow, extendZero_earlier]

private theorem projected_derived (rows : List (Inequality (n + 1))) (row : Inequality n)
    (listed : row ∈ project rows) : Derived rows row.extendZero := by
  rcases List.mem_append.mp listed with kept | paired
  · obtain ⟨source, sourceListed, same⟩ := List.mem_map.mp kept
    subst row
    have zero : source.pivot = 0 := of_decide_eq_true (List.mem_filter.mp sourceListed).2
    have lifted : source.trim.extendZero = source := by
      refine Inequality.same ?_ rfl
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [extendZero_final]
        exact zero.symm
      · exact extendZero_earlier _ _
    rw [lifted]
    exact .member _ (List.mem_filter.mp sourceListed).1
  · obtain ⟨upper, upperListed, lowerRows⟩ := List.mem_flatMap.mp paired
    obtain ⟨lower, lowerListed, same⟩ := List.mem_map.mp lowerRows
    subst row
    have up : 0 < upper.pivot := of_decide_eq_true (List.mem_filter.mp upperListed).2
    have low : lower.pivot < 0 := of_decide_eq_true (List.mem_filter.mp lowerListed).2
    have lifted : (combine upper lower).extendZero =
        addRows (scaleRow (-lower.pivot) upper) (scaleRow upper.pivot lower) := by
      refine Inequality.same ?_ rfl
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [extendZero_final]
        change 0 = -lower.pivot * upper.pivot + upper.pivot * lower.pivot
        rw [Int.neg_mul, Int.mul_comm lower.pivot upper.pivot]
        omega
      · exact extendZero_earlier _ _
    rw [lifted]
    exact .add
      (.scale _ (by omega) (.member _ (List.mem_filter.mp upperListed).1))
      (.scale _ (by omega) (.member _ (List.mem_filter.mp lowerListed).1))

private theorem Derived.liftProjection {rows : List (Inequality (n + 1))} {row : Inequality n}
    (derived : Derived (project rows) row) : Derived rows row.extendZero := by
  induction derived with
  | member row listed => exact projected_derived rows row listed
  | add _ _ left right => rw [extendZero_add]; exact .add left right
  | scale factor positive _ ih => rw [extendZero_scale]; exact .scale factor positive ih

private theorem Derived.liftSubsystem {rows smaller : List (Inequality n)} {row : Inequality n}
    (derived : Derived smaller row) (included : ∀ source ∈ smaller, source ∈ rows) : Derived rows row := by
  induction derived with
  | member source listed => exact .member source (included source listed)
  | add _ _ left right => exact .add left right
  | scale factor positive _ ih => exact .scale factor positive ih

private theorem negative_constant (certificate : Infeasibility n rows) :
    ∃ bound : SignedRatio, bound.num < 0 ∧ Derived rows ⟨fun _ => 0, bound⟩ := by
  induction certificate with
  | constant rows row listed negative =>
    refine ⟨row.bound, negative, ?_⟩
    have equal : row = ⟨fun _ => 0, row.bound⟩ := Inequality.same (fun i => Fin.elim0 i) rfl
    rw [← equal]
    exact .member row listed
  | @projected dim rows before ih =>
    obtain ⟨bound, negative, derivation⟩ := ih
    refine ⟨bound, negative, ?_⟩
    have zero : (Inequality.mk (variables := dim) (fun _ => 0) bound).extendZero =
        ⟨fun _ => 0, bound⟩ := by
      refine Inequality.same ?_ rfl
      intro i
      exact Fin.lastCases (extendZero_final _) (fun j => extendZero_earlier _ j) i
    rw [← zero]
    exact derivation.liftProjection
  | subsystem rows smaller included before ih =>
    obtain ⟨bound, negative, derivation⟩ := ih
    exact ⟨bound, negative, derivation.liftSubsystem included⟩

private def homogeneousRows (rows : List (Fin n → Int)) : List (Inequality n) :=
  rows.flatMap fun row => [⟨row, SignedRatio.zero⟩, ⟨fun i => -row i, SignedRatio.zero⟩]

private def separationRows (rows : List (Fin n → Int)) (query : Fin n → Int) :
    List (Inequality n) :=
  ⟨fun i => -query i, SignedRatio.neg SignedRatio.one⟩ :: homogeneousRows rows

/-- Track the nonnegative multiplicity of the separating query row. The
remaining coefficients are in the integer span of the measurement rows. -/
private theorem derived_separation {rows : List (Fin n → Int)} {query : Fin n → Int}
    {row : Inequality n} (d : Derived (separationRows rows query) row) :
    ∃ count : Int, 0 ≤ count ∧ row.bound.num = -count * (row.bound.den : Int) ∧
      IntegerSpan rows (fun i => row.coefficients i + count * query i) := by
  induction d with
  | member row listed =>
    rcases List.mem_cons.mp listed with queryRow | fromMeasurements
    · subst row
      refine ⟨1, by decide, rfl, ?_⟩
      have zero : (fun i => -query i + (1 : Int) * query i) = (fun _ => 0) := by
        funext i
        omega
      change IntegerSpan rows (fun i => -query i + (1 : Int) * query i)
      rw [zero]
      exact .zero
    · obtain ⟨source, sourceListed, signs⟩ := List.mem_flatMap.mp fromMeasurements
      rcases List.mem_cons.mp signs with unnegated | negated <;>
        refine ⟨0, by decide, ?_, ?_⟩
      · subst row; rfl
      · subst row
        simpa using IntegerSpan.member source sourceListed
      · have equal := List.mem_singleton.mp negated
        subst row
        rfl
      · have equal := List.mem_singleton.mp negated
        subst row
        simpa only [Int.zero_mul, Int.add_zero, Int.neg_mul, Int.one_mul] using
          IntegerSpan.scale (-1) (IntegerSpan.member source sourceListed)
  | @add left right _ _ leftIH rightIH =>
    obtain ⟨k, kPos, kBound, kSpan⟩ := leftIH
    obtain ⟨j, jPos, jBound, jSpan⟩ := rightIH
    refine ⟨k + j, Int.add_nonneg kPos jPos, ?_, ?_⟩
    · simp only [addRows, SignedRatio.add, kBound, jBound, Int.natCast_mul, Int.neg_add, Int.add_mul]
      ac_rfl
    · have equal : (fun i => (addRows left right).coefficients i + (k + j) * query i) =
          (fun i => (left.coefficients i + k * query i) + (right.coefficients i + j * query i)) := by
        funext i
        simp only [addRows, Int.add_mul]
        ac_rfl
      rw [equal]
      exact .add kSpan jSpan
  | @scale factor positive row _ ih =>
    obtain ⟨count, countPos, countBound, countSpan⟩ := ih
    refine ⟨factor * count, Int.mul_nonneg positive countPos, ?_, ?_⟩
    · simp only [scaleRow, SignedRatio.scaleInt, SignedRatio.mul, countBound, Nat.one_mul,
        Int.neg_mul, Int.mul_neg]
      ac_rfl
    · have equal : (fun i => (scaleRow factor row).coefficients i + (factor * count) * query i) =
          (fun i => factor * (row.coefficients i + count * query i)) := by
        funext i
        simp only [scaleRow, Int.mul_add, Int.mul_assoc]
      rw [equal]
      exact .scale factor countSpan

private theorem span_of_infeasible {rows : List (Fin n → Int)} {query : Fin n → Int}
    (certificate : Infeasibility n (separationRows rows query)) : RationalSpan rows query := by
  obtain ⟨bound, negative, derived⟩ := negative_constant certificate
  obtain ⟨count, nonnegative, equality, span⟩ := derived_separation derived
  change bound.num = _ at equality
  rw [equality] at negative
  have positive : 0 < count := by
    by_cases zero : count = 0
    · subst count
      simp only [Int.neg_zero, Int.zero_mul, Int.lt_irrefl] at negative
    · omega
  refine ⟨count.toNat, by omega, ?_⟩
  simpa only [Int.zero_add, Int.toNat_of_nonneg nonnegative] using span

private theorem IntegerSpan.sameDot {rows : List (Fin n → Int)} {row : Fin n → Int}
    (span : IntegerSpan rows row) {left right : Fin n → SignedRatio}
    (same : ∀ r ∈ rows, SignedRatio.Equiv (dot n r left) (dot n r right)) :
    SignedRatio.Equiv (dot n row left) (dot n row right) := by
  induction span with
  | zero => exact SignedRatio.equiv_trans (dot_zero n left) (SignedRatio.equiv_symm (dot_zero n right))
  | member r listed => exact same r listed
  | @add first second _ _ sameFirst sameSecond =>
    exact SignedRatio.equiv_trans (dot_add_coefficients n first second left)
      (SignedRatio.equiv_trans (SignedRatio.add_congr sameFirst sameSecond)
        (SignedRatio.equiv_symm (dot_add_coefficients n first second right)))
  | @scale factor source _ ih =>
    exact SignedRatio.equiv_trans (dot_scale_coefficients n factor source left)
      (SignedRatio.equiv_trans (SignedRatio.scaleInt_congr _ ih)
        (SignedRatio.equiv_symm (dot_scale_coefficients n factor source right)))

private theorem mul_left_cancel_pos {factor left right : SignedRatio} (positive : 0 < factor.num)
    (equal : SignedRatio.Equiv (SignedRatio.mul factor left) (SignedRatio.mul factor right)) :
    SignedRatio.Equiv left right := by
  have cleared : (factor.num * (factor.den : Int)) * (left.num * (right.den : Int)) =
      (factor.num * (factor.den : Int)) * (right.num * (left.den : Int)) := by
    unfold SignedRatio.Equiv SignedRatio.mul at equal
    simp only [Int.natCast_mul] at equal
    calc
      _ = (factor.num * left.num) * ((factor.den : Int) * (right.den : Int)) := by ac_rfl
      _ = (factor.num * right.num) * ((factor.den : Int) * (left.den : Int)) := equal
      _ = _ := by ac_rfl
  exact Int.eq_of_mul_eq_mul_left (Int.ne_of_gt (Int.mul_pos positive (by have h := factor.den_pos; omega))) cleared

theorem RationalSpan.sameDot {rows : List (Fin n → Int)} {query : Fin n → Int}
    (span : RationalSpan rows query) {left right : Fin n → SignedRatio}
    (same : ∀ row ∈ rows, SignedRatio.Equiv (dot n row left) (dot n row right)) :
    SignedRatio.Equiv (dot n query left) (dot n query right) := by
  obtain ⟨den, positive, combination⟩ := span
  have equality := combination.sameDot same
  have scaled := SignedRatio.equiv_trans
    (SignedRatio.equiv_symm (dot_scale_coefficients n (den : Int) query left))
    (SignedRatio.equiv_trans equality (dot_scale_coefficients n (den : Int) query right))
  exact mul_left_cancel_pos (factor := ⟨den, 1, by decide⟩) (by change 0 < (den : Int); omega) scaled

private theorem equality_of_separation {rows : List (Fin n → Int)} {query : Fin n → Int}
    {values : Fin n → SignedRatio} (satisfied : Satisfies (separationRows rows query) values)
    (r : Fin n → Int) (listed : r ∈ rows) :
    SignedRatio.Equiv (dot n r values) SignedRatio.zero := by
  have upper : (Inequality.mk r SignedRatio.zero).Holds values :=
    satisfied _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r, listed, List.mem_cons_self ..⟩))
  have lower : (Inequality.mk (fun i => -r i) SignedRatio.zero).Holds values :=
    satisfied _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r, listed,
      List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩))
  apply SignedRatio.equiv_of_le_of_le upper
  apply (SignedRatio.neg_le_neg_iff _ _).mp
  exact (SignedRatio.le_congr (dot_neg_coefficients n r values)
    (SignedRatio.equiv_refl SignedRatio.zero)).mp lower

private theorem separating_query {rows : List (Fin n → Int)} {query : Fin n → Int}
    {values : Fin n → SignedRatio} (satisfied : Satisfies (separationRows rows query) values) :
    SignedRatio.LE SignedRatio.one (dot n query values) := by
  have lower : (Inequality.mk (fun i => -query i) (SignedRatio.neg SignedRatio.one)).Holds values :=
    satisfied _ (List.mem_cons_self ..)
  apply (SignedRatio.neg_le_neg_iff _ _).mp
  exact (SignedRatio.le_congr (dot_neg_coefficients n query values)
    (SignedRatio.equiv_refl _)).mp lower

private theorem dot_add_values (n : Nat) (row : Fin n → Int) (left right : Fin n → SignedRatio) :
    SignedRatio.Equiv (dot n row (fun i => SignedRatio.add (left i) (right i)))
      (SignedRatio.add (dot n row left) (dot n row right)) := by
  induction n with
  | zero => exact SignedRatio.equiv_symm (SignedRatio.add_zero _)
  | succ n ih =>
    exact SignedRatio.equiv_trans (SignedRatio.add_congr (SignedRatio.scaleInt_add _ _ _)
      (ih (fun i => row i.castSucc) (fun i => left i.castSucc) (fun i => right i.castSucc)))
        (SignedRatio.add_interchange _ _ _ _)

private def positiveHalf (value : SignedRatio) : SignedRatio :=
  ⟨max value.num 0 + (value.den : Int), value.den, value.den_pos⟩

private theorem half_positive (value : SignedRatio) : 0 < (positiveHalf value).num := by
  have d := value.den_pos
  change 0 < max value.num 0 + (value.den : Int)
  omega

private theorem half_split (value : SignedRatio) :
    SignedRatio.Equiv (positiveHalf value) (SignedRatio.add (positiveHalf (SignedRatio.neg value)) value) := by
  have decomposition : max value.num 0 = max (-value.num) 0 + value.num := by omega
  simp only [SignedRatio.Equiv, SignedRatio.add, positiveHalf, SignedRatio.neg, Int.natCast_mul,
    decomposition, Int.add_mul]
  ac_rfl

private theorem dot_ones_nonnegative (n : Nat) (values : Fin n → SignedRatio)
    (positive : ∀ i, 0 ≤ (values i).num) :
    SignedRatio.Nonnegative (dot n (fun _ => 1) values) := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih =>
    exact SignedRatio.nonnegative_add
      (SignedRatio.scaleInt_nonnegative (by decide : 0 ≤ (1 : Int)) (positive (Fin.last n)))
      (ih (fun i => values i.castSucc) (fun i => positive i.castSucc))

private theorem dot_ones_positive (n : Nat) (values : Fin (n + 1) → SignedRatio)
    (positive : ∀ i, 0 < (values i).num) : 0 < (dot (n + 1) (fun _ => 1) values).num := by
  let tail := dot n (fun _ => 1) (fun i => values i.castSucc)
  have tailNonnegative : 0 ≤ tail.num :=
    dot_ones_nonnegative n _ (fun i => Int.le_of_lt (positive i.castSucc))
  have headPositive := positive (Fin.last n)
  have tailDenPositive : 0 < (tail.den : Int) := Int.natCast_pos.mpr tail.den_pos
  have headDenNonnegative : 0 ≤ (((values (Fin.last n)).den : Nat) : Int) := Int.natCast_nonneg _
  change 0 < 1 * (values (Fin.last n)).num * (tail.den : Int) +
    tail.num * ((1 * (values (Fin.last n)).den : Nat) : Int)
  simp only [Int.one_mul, Nat.one_mul]
  have first := Int.mul_pos headPositive tailDenPositive
  have second := Int.mul_nonneg tailNonnegative headDenNonnegative
  omega

/-- Every rational direction preserving normalization is proportional to a
difference of two laws. Add the same positive entry to both halves before
normalizing so there is a positive common mass on a nonempty alphabet. -/
private theorem separation_violates_uniform {rows : List (Fin n → Int)} {query : Fin n → Int}
    (normalization : (fun _ => 1) ∈ rows) {values : Fin n → SignedRatio}
    (satisfied : Satisfies (separationRows rows query) values)
    (uniform : ∀ left right : Fin n → SignedRatio, Simplex left → Simplex right →
      (∀ row ∈ rows, SignedRatio.Equiv (dot n row left) (dot n row right)) →
      SignedRatio.Equiv (dot n query left) (dot n query right)) : False := by
  have responds := separating_query satisfied
  have positiveQuery := SignedRatio.positive_of_lower PositiveRatio.one _ responds
  cases n with
  | zero => exact Int.lt_irrefl 0 positiveQuery
  | succ n =>
    let up := fun i : Fin (n + 1) => positiveHalf (values i)
    let down := fun i : Fin (n + 1) => positiveHalf (SignedRatio.neg (values i))
    have differ (row : Fin (n + 1) → Int) :
        SignedRatio.Equiv (dot (n + 1) row up)
          (SignedRatio.add (dot (n + 1) row down) (dot (n + 1) row values)) :=
      SignedRatio.equiv_trans (dot_congr _ row _ _ (fun i => half_split (values i)))
        (dot_add_values _ row down values)
    have same (row : Fin (n + 1) → Int) (listed : row ∈ rows) :
        SignedRatio.Equiv (dot (n + 1) row up) (dot (n + 1) row down) :=
      SignedRatio.equiv_trans (differ row) (SignedRatio.equiv_trans
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) (equality_of_separation satisfied row listed))
        (SignedRatio.add_zero _))
    let mass := dot (n + 1) (fun _ => 1) up
    let mean := PositiveRatio.ofSignedPositive mass (dot_ones_positive n up (fun i => half_positive (values i)))
    let scale := mean.inv.toSignedRatio
    have scalePositive : 0 < scale.num := Int.natCast_pos.mpr mean.inv.num_pos
    have normalized : SignedRatio.Equiv (SignedRatio.mul scale mass) SignedRatio.one :=
      SignedRatio.equiv_trans
        (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
          (SignedRatio.equiv_symm (PositiveRatio.ofSignedPositive_value _ _)))
        (SignedRatio.equiv_trans (SignedRatio.mul_comm _ _) (PositiveRatio.signed_mul_inv mean))
    let left := fun i => SignedRatio.mul scale (up i)
    let right := fun i => SignedRatio.mul scale (down i)
    have leftLaw : Simplex left :=
      ⟨fun i => SignedRatio.nonnegative_mul (Int.le_of_lt scalePositive) (Int.le_of_lt (half_positive _)),
        SignedRatio.equiv_trans (dot_mul_values _ _ _ scale) normalized⟩
    have rightLaw : Simplex right :=
      ⟨fun i => SignedRatio.nonnegative_mul (Int.le_of_lt scalePositive) (Int.le_of_lt (half_positive _)),
        SignedRatio.equiv_trans (dot_mul_values _ _ _ scale) (SignedRatio.equiv_trans
          (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (same _ normalization)))
          normalized)⟩
    have queryMatched := uniform left right leftLaw rightLaw (fun row listed =>
      SignedRatio.equiv_trans (dot_mul_values _ _ _ scale)
        (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (same row listed))
          (SignedRatio.equiv_symm (dot_mul_values _ _ _ scale))))
    have unscaled : SignedRatio.Equiv (dot (n + 1) query up) (dot (n + 1) query down) :=
      mul_left_cancel_pos scalePositive (SignedRatio.equiv_trans
        (SignedRatio.equiv_symm (dot_mul_values _ _ _ scale))
        (SignedRatio.equiv_trans queryMatched (dot_mul_values _ _ _ scale)))
    let base := dot (n + 1) query down
    let changeValue := dot (n + 1) query values
    have unchanged : SignedRatio.Equiv (SignedRatio.add changeValue base) base :=
      SignedRatio.equiv_trans (SignedRatio.add_comm _ _) (SignedRatio.equiv_trans
        (SignedRatio.equiv_symm (differ query)) unscaled)
    have nonpositive : SignedRatio.LE changeValue SignedRatio.zero :=
      (SignedRatio.le_congr (SignedRatio.equiv_refl _)
        ((SignedRatio.sub_equiv_zero_iff _ _).mpr (SignedRatio.equiv_refl base))).mp
        ((SignedRatio.add_le_iff_le_sub changeValue base base).mp
          ((SignedRatio.le_congr unchanged (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl base)))
    have impossible := SignedRatio.le_trans responds nonpositive
    exact (by decide : ¬ SignedRatio.LE SignedRatio.one SignedRatio.zero) impossible

/-- Uniform identification over the full rational simplex is equivalent
to row-span membership when normalization is retained in the measurements.
Identification on one boundary face can hold with fewer rows. -/
theorem uniform_simplex_iff_rationalSpan (rows : List (Fin n → Int)) (query : Fin n → Int)
    (normalization : (fun _ => 1) ∈ rows) :
    (∀ left right : Fin n → SignedRatio, Simplex left → Simplex right →
      (∀ row ∈ rows, SignedRatio.Equiv (dot n row left) (dot n row right)) →
      SignedRatio.Equiv (dot n query left) (dot n query right)) ↔ RationalSpan rows query := by
  constructor
  · intro uniform
    cases solve n (separationRows rows query) with
    | feasible values valid => exact False.elim (separation_violates_uniform normalization valid uniform)
    | infeasible certificate => exact span_of_infeasible certificate
  · intro span left right _ _ same
    exact span.sameDot same

end Thesis.Probability.Distros.RationalLinear
