import Thesis.Probability.Distros.FiniteGridMoments

namespace Thesis.Probability.Distros.RationalVector

abbrev Vector (dimension : Nat) := Fin dimension → SignedRatio

def Equiv (first second : Vector n) : Prop := ∀ i, SignedRatio.Equiv (first i) (second i)
def zero : Vector n := fun _ => SignedRatio.zero
def add (first second : Vector n) : Vector n := fun i => SignedRatio.add (first i) (second i)
def scale (factor : SignedRatio) (value : Vector n) : Vector n := fun i => SignedRatio.mul factor (value i)
def sub (first second : Vector n) : Vector n := fun i => SignedRatio.sub (first i) (second i)

def unit (index : Fin n) : Vector n := fun i => if index = i then SignedRatio.one else SignedRatio.zero

def combine (indices : List I) (vectors : I → Vector n) (coefficients : I → SignedRatio) : Vector n :=
  fun i => SignedRatio.listSum (indices.map (fun index => SignedRatio.mul (coefficients index) (vectors index i)))

theorem equiv_refl (value : Vector n) : Equiv value value := fun _ => SignedRatio.equiv_refl _
theorem equiv_symm {first second : Vector n} (same : Equiv first second) : Equiv second first := fun i => SignedRatio.equiv_symm (same i)
theorem equiv_trans {first second third : Vector n} (a : Equiv first second) (b : Equiv second third) : Equiv first third :=
  fun i => SignedRatio.equiv_trans (a i) (b i)

theorem combine_congr (indices : List I) (vectors other : I → Vector n) (coefficients : I → SignedRatio)
    (same : ∀ index ∈ indices, Equiv (vectors index) (other index)) :
    Equiv (combine indices vectors coefficients) (combine indices other coefficients) := by
  intro i
  exact SignedRatio.listSum_map_congr_on_mem indices _ _ (fun index member =>
    SignedRatio.mul_congr (SignedRatio.equiv_refl _) (same index member i))

/-- A coordinate of a sum of distinct unit vectors is the corresponding
coefficient when listed, and is zero outside the supplied index list. -/
theorem combine_units [DecidableEq (Fin n)] (indices : List (Fin n)) (distinct : indices.Nodup)
    (coefficients : Fin n → SignedRatio) (i : Fin n) :
    SignedRatio.Equiv (combine indices unit coefficients i) (if i ∈ indices then coefficients i else SignedRatio.zero) := by
  have terms : SignedRatio.Equiv (combine indices unit coefficients i)
      (SignedRatio.listSum (indices.map (fun j => if j = i then coefficients i else SignedRatio.zero))) := by
    apply SignedRatio.listSum_map_congr
    intro j
    by_cases same : j = i
    · subst j; simp only [unit, if_true]; exact SignedRatio.mul_one _
    · simp only [unit, if_neg same]; exact SignedRatio.mul_zero _
  by_cases listed : i ∈ indices
  · rw [if_pos listed]
    exact SignedRatio.equiv_trans terms (SignedRatio.listSum_list_select indices i coefficients distinct listed)
  · rw [if_neg listed]
    refine SignedRatio.equiv_trans terms (SignedRatio.equiv_trans
      (SignedRatio.listSum_map_congr_on_mem indices _ (fun _ => SignedRatio.zero) ?_) (SignedRatio.listSum_map_zero indices))
    intro j member
    have different : j ≠ i := by intro same; subst j; exact listed member
    rw [if_neg different]
    exact SignedRatio.equiv_refl _

/-- Finite rational linear maps respect rational equivalence. The explicit
subtraction law is retained for clients using unreduced presentations. -/
structure Operator (domain codomain : Nat) where
  apply : Vector domain → Vector codomain
  congr : ∀ first second, Equiv first second → Equiv (apply first) (apply second)
  zero : Equiv (apply zero) zero
  add : ∀ first second, Equiv (apply (add first second)) (add (apply first) (apply second))
  scale : ∀ factor value, Equiv (apply (scale factor value)) (scale factor (apply value))
  sub : ∀ first second, Equiv (apply (sub first second)) (sub (apply first) (apply second))

namespace Operator

def Image (operator : Operator n m) (value : Vector m) : Prop := ∃ source, Equiv (operator.apply source) value
def Kernel (operator : Operator n m) (value : Vector n) : Prop := Equiv (operator.apply value) zero

theorem map_combine (operator : Operator n m) (indices : List I) (vectors : I → Vector n) (coefficients : I → SignedRatio) :
    Equiv (operator.apply (combine indices vectors coefficients)) (combine indices (fun i => operator.apply (vectors i)) coefficients) := by
  induction indices with
  | nil => exact operator.zero
  | cons index indices ih =>
      exact equiv_trans (operator.add (scale (coefficients index) (vectors index)) (combine indices vectors coefficients))
        (fun i => SignedRatio.add_congr (operator.scale (coefficients index) (vectors index) i) (ih i))

end Operator

/-- A finite indexed basis includes membership, independence and spanning.
Only listed coefficients matter; no enumeration of an ambient scalar type is
assumed. The index list is explicitly duplicate-free. -/
structure Basis (dimension : Nat) (space : Vector dimension → Prop) (I : Type) where
  indices : List I
  distinct : indices.Nodup
  vectors : I → Vector dimension
  belongs : ∀ i ∈ indices, space (vectors i)
  independent : ∀ coefficients, Equiv (combine indices vectors coefficients) zero →
    ∀ i ∈ indices, SignedRatio.Equiv (coefficients i) SignedRatio.zero
  spanning : ∀ value, space value → ∃ coefficients, Equiv (combine indices vectors coefficients) value

/-- A rank certificate exhibits an independent spanning basis of the image
with the stated cardinality, rather than recording a proposed integer rank. -/
structure RankCertificate (operator : Operator n m) (rank : Nat) where
  Index : Type
  basis : Basis m operator.Image Index
  cardinality : basis.indices.length = rank

/-- The complete coordinate basis is constructive, including dimension zero. -/
def standardBasis (n : Nat) : Basis n (fun _ => True) (Fin n) where
  indices := List.finRange n
  distinct := finRange_nodup n
  vectors := unit
  belongs := by intro _ _; trivial
  independent := by
    intro coefficients vanished i _
    have selected := combine_units (List.finRange n) (finRange_nodup n) coefficients i
    rw [if_pos (List.mem_finRange i)] at selected
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm selected) (vanished i)
  spanning := by
    intro value _
    refine ⟨value, ?_⟩
    intro i
    have selected := combine_units (List.finRange n) (finRange_nodup n) value i
    simpa only [if_pos (List.mem_finRange i)] using selected

/-- Every zero operator has the empty image basis and rank zero. -/
def zeroRank (operator : Operator n m) (vanished : ∀ value, Equiv (operator.apply value) zero) : RankCertificate operator 0 :=
  ⟨Fin 0, {
    indices := []
    distinct := List.nodup_nil
    vectors := fun i => Fin.elim0 i
    belongs := by intro i _; exact Fin.elim0 i
    independent := by intro _ _ i _; exact Fin.elim0 i
    spanning := by
      rintro value ⟨source, same⟩
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      exact equiv_trans (equiv_symm (vanished source)) same
  }, rfl⟩

/-- For a zero operator, every coordinate direction is a kernel basis vector. -/
def zeroKernelBasis (operator : Operator n m) (vanished : ∀ value, Equiv (operator.apply value) zero) :
    Basis n operator.Kernel (Fin n) :=
  { standardBasis n with
    belongs := by intro i _; exact vanished (unit i)
    spanning := by intro value _; exact (standardBasis n).spanning value True.intro }

end Thesis.Probability.Distros.RationalVector
