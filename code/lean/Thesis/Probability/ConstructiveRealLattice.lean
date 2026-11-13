import Thesis.Probability.ConstructiveRealAdditive

namespace Thesis.Probability.SignedRatio

/-- Rational endpoint maximum. Only explicit rational order is decided. -/
def maximum (first second : SignedRatio) : SignedRatio := if LE first second then second else first

theorem le_maximum_left (first second : SignedRatio) : LE first (maximum first second) := by
  by_cases compared : LE first second
  · simpa only [maximum, if_pos compared] using compared
  · simpa only [maximum, if_neg compared] using le_refl first

theorem le_maximum_right (first second : SignedRatio) : LE second (maximum first second) := by
  by_cases compared : LE first second
  · simpa only [maximum, if_pos compared] using le_refl second
  · simpa only [maximum, if_neg compared] using (le_total first second).resolve_left compared

theorem maximum_le (first second upper : SignedRatio) (firstBound : LE first upper) (secondBound : LE second upper) :
    LE (maximum first second) upper := by
  by_cases compared : LE first second
  · simpa only [maximum, if_pos compared] using secondBound
  · simpa only [maximum, if_neg compared] using firstBound

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.ConstructiveReal

/-- Maximum of analytic values through certified rational endpoints. This
computes a value, not a Boolean ordering or a selected maximizing argument. -/
def maximum (first second : ConstructiveReal) : ConstructiveReal where
  enclose precision := {
    lower := SignedRatio.maximum (first.enclose precision).lower (second.enclose precision).lower
    upper := SignedRatio.maximum (first.enclose precision).upper (second.enclose precision).upper
    ordered := SignedRatio.maximum_le _ _ _
      (SignedRatio.le_trans (first.enclose precision).ordered (SignedRatio.le_maximum_left _ _))
      (SignedRatio.le_trans (second.enclose precision).ordered (SignedRatio.le_maximum_right _ _))
    width := SignedRatio.maximum_le _ _ _
      (SignedRatio.le_trans (first.enclose precision).width
        (SignedRatio.add_le_add (SignedRatio.le_maximum_left _ _) (SignedRatio.le_refl _)))
      (SignedRatio.le_trans (second.enclose precision).width
        (SignedRatio.add_le_add (SignedRatio.le_maximum_right _ _) (SignedRatio.le_refl _))) }
  coherent left right := SignedRatio.maximum_le _ _ _
    (SignedRatio.le_trans (first.coherent left right) (SignedRatio.le_maximum_left _ _))
    (SignedRatio.le_trans (second.coherent left right) (SignedRatio.le_maximum_right _ _))

theorem le_maximum_left (first second : ConstructiveReal) : LE first (maximum first second) := fun left right =>
  SignedRatio.le_trans (first.coherent left right) (SignedRatio.le_maximum_left _ _)

theorem le_maximum_right (first second : ConstructiveReal) : LE second (maximum first second) := fun left right =>
  SignedRatio.le_trans (second.coherent left right) (SignedRatio.le_maximum_right _ _)

theorem maximum_le (first second upper : ConstructiveReal) (firstBound : LE first upper) (secondBound : LE second upper) :
    LE (maximum first second) upper := fun left right => SignedRatio.maximum_le _ _ _ (firstBound left right) (secondBound left right)

theorem maximum_mono {first second first' second' : ConstructiveReal} (firstBound : LE first first') (secondBound : LE second second') :
    LE (maximum first second) (maximum first' second') :=
  maximum_le _ _ _ (le_trans firstBound (le_maximum_left _ _)) (le_trans secondBound (le_maximum_right _ _))

theorem maximum_congr {first second first' second' : ConstructiveReal} (firstSame : Equiv first first') (secondSame : Equiv second second') :
    Equiv (maximum first second) (maximum first' second') :=
  ⟨maximum_mono firstSame.1 secondSame.1, maximum_mono firstSame.2 secondSame.2⟩

theorem maximum_comm (first second : ConstructiveReal) : Equiv (maximum first second) (maximum second first) :=
  ⟨maximum_le _ _ _ (le_maximum_right _ _) (le_maximum_left _ _),
    maximum_le _ _ _ (le_maximum_right _ _) (le_maximum_left _ _)⟩

theorem maximum_of_le {first second : ConstructiveReal} (compared : LE first second) : Equiv (maximum first second) second :=
  ⟨maximum_le _ _ _ compared (le_refl _), le_maximum_right _ _⟩

theorem maximum_self (value : ConstructiveReal) : Equiv (maximum value value) value := maximum_of_le (le_refl value)

theorem maximum_ofSignedRatio (first second : SignedRatio) :
    Equiv (maximum (ofSignedRatio first) (ofSignedRatio second)) (ofSignedRatio (SignedRatio.maximum first second)) :=
  ⟨fun _ _ => SignedRatio.le_refl _, fun _ _ => SignedRatio.le_refl _⟩

/-- Minimum is the reflected computed maximum, with the same certified
precision and no analytic comparison procedure. -/
def minimum (first second : ConstructiveReal) : ConstructiveReal := neg (maximum (neg first) (neg second))

theorem minimum_le_left (first second : ConstructiveReal) : LE (minimum first second) first :=
  (le_congr (equiv_refl _) (neg_neg first)).mp ((neg_le_neg_iff _ _).mpr (le_maximum_left (neg first) (neg second)))

theorem minimum_le_right (first second : ConstructiveReal) : LE (minimum first second) second :=
  (le_congr (equiv_refl _) (neg_neg second)).mp ((neg_le_neg_iff _ _).mpr (le_maximum_right (neg first) (neg second)))

theorem le_minimum (first second lower : ConstructiveReal) (firstBound : LE lower first) (secondBound : LE lower second) :
    LE lower (minimum first second) :=
  (le_congr (neg_neg lower) (equiv_refl _)).mp ((neg_le_neg_iff _ _).mpr
    (maximum_le _ _ _ ((neg_le_neg_iff _ _).mpr firstBound) ((neg_le_neg_iff _ _).mpr secondBound)))

theorem minimum_congr {first second first' second' : ConstructiveReal} (firstSame : Equiv first first') (secondSame : Equiv second second') :
    Equiv (minimum first second) (minimum first' second') := neg_congr (maximum_congr (neg_congr firstSame) (neg_congr secondSame))

/-- Finite extrema compute endpoint values. They do not return an index or
claim a decidable argmax on an analytic list. -/
def listMaximum (initial : ConstructiveReal) : List ConstructiveReal → ConstructiveReal
  | [] => initial
  | value :: values => maximum value (listMaximum initial values)

theorem listMaximum_le (initial : ConstructiveReal) (values : List ConstructiveReal) (upper : ConstructiveReal)
    (initialBound : LE initial upper) (bounded : ∀ value ∈ values, LE value upper) : LE (listMaximum initial values) upper := by
  induction values with
  | nil => exact initialBound
  | cons value values ih =>
      exact maximum_le _ _ _ (bounded value (List.mem_cons_self ..))
        (ih (fun other member => bounded other (List.mem_cons_of_mem _ member)))

theorem le_listMaximum_of_mem (initial : ConstructiveReal) (values : List ConstructiveReal) (value : ConstructiveReal)
    (member : value ∈ initial :: values) : LE value (listMaximum initial values) := by
  induction values with
  | nil =>
      have same := List.mem_singleton.mp member
      cases same
      exact le_refl _
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · exact le_trans (ih (List.mem_cons.mpr (Or.inl same))) (le_maximum_right _ _)
      · rcases List.mem_cons.mp later with same | listed
        · cases same; exact le_maximum_left _ _
        · exact le_trans (ih (List.mem_cons_of_mem _ listed)) (le_maximum_right _ _)

def listMinimum (initial : ConstructiveReal) (values : List ConstructiveReal) : ConstructiveReal :=
  neg (listMaximum (neg initial) (values.map neg))

theorem listMinimum_le_of_mem (initial : ConstructiveReal) (values : List ConstructiveReal) (value : ConstructiveReal)
    (member : value ∈ initial :: values) : LE (listMinimum initial values) value :=
  (le_congr (equiv_refl _) (neg_neg value)).mp ((neg_le_neg_iff _ _).mpr
    (le_listMaximum_of_mem (neg initial) (values.map neg) (neg value)
      (by simpa only [List.map_cons] using List.mem_map.mpr ⟨value, member, rfl⟩)))

/-- A point in every supplied compatible finite real interval is constructed
by finite extrema. Only list shape is inspected; no real inequality is
turned into a decision. This is the lifting step needed by dual elimination. -/
def compatibleInterval (lower upper : List ConstructiveReal)
    (compatible : ∀ below ∈ lower, ∀ above ∈ upper, LE below above) :
    {value : ConstructiveReal // (∀ below ∈ lower, LE below value) ∧ (∀ above ∈ upper, LE value above)} := by
  cases lower with
  | nil =>
      cases upper with
      | nil => exact ⟨zero, (fun _ member => False.elim (List.not_mem_nil member)), (fun _ member => False.elim (List.not_mem_nil member))⟩
      | cons above rest => exact ⟨listMinimum above rest,
          (fun _ member => False.elim (List.not_mem_nil member)), listMinimum_le_of_mem above rest⟩
  | cons below rest =>
      exact ⟨listMaximum below rest, le_listMaximum_of_mem below rest,
        fun above member => listMaximum_le below rest above (compatible below (List.mem_cons_self ..) above member)
          (fun value listed => compatible value (List.mem_cons_of_mem _ listed) above member)⟩

end Thesis.Probability.ConstructiveReal
