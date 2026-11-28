import Thesis.Probability.IntegerPolynomialSolvability

namespace Thesis.Probability

/-!
# A finite system for the intermediate values of an integer polynomial

Each syntax occurrence has an explicit location in the finite subexpression
list. Identical subexpressions may use the same first occurrence. An equation
relates its output to the input values or the immediate children's outputs.
Integer constants are expanded to zero, one, addition and negation before
this step. This translation is computable and uses an explicit syntax tree.
The representation theorem concerns exact rational solutions.
-/

/-- Elementary equations whose variables range over all signed rationals. -/
inductive RationalEquation (V : Type) where
  | equal (left right : V)
  | zero (value : V)
  | one (value : V)
  | negative (input result : V)
  | add (left right result : V)
  | multiply (left right result : V)

namespace RationalEquation

/-- Each equation checks an equality in the fraction presentation. -/
def holds (values : V → SignedRatio) : RationalEquation V → Prop
  | .equal a b => (values a).Equiv (values b)
  | .zero a => (values a).Equiv .zero
  | .one a => (values a).Equiv .one
  | .negative a b => (values b).Equiv (values a).neg
  | .add a b r => (values r).Equiv ((values a).add (values b))
  | .multiply a b r => (values r).Equiv ((values a).mul (values b))

end RationalEquation

/-- Finite conjunction, with the variable count carried by the instance. -/
structure RationalEquationSystem where
  count : Nat
  equations : List (RationalEquation (Fin count))

def RationalEquationSystem.Solvable (system : RationalEquationSystem) : Prop :=
  ∃ values : Fin system.count → SignedRatio, ∀ equation ∈ system.equations, equation.holds values

namespace ElementaryRationalEquations
open IntegerPolynomial

private def numeral {V : Type} : Nat → IntegerPolynomial V
  | 0 => .constant 0
  | n + 1 => .add (numeral n) (.constant 1)

private def unitLeaves : IntegerPolynomial V → Prop
  | .constant n => n = 0 ∨ n = 1
  | .variable _ => True
  | .add p q | .mul p q => unitLeaves p ∧ unitLeaves q
  | .neg p => unitLeaves p

private theorem numeral_unit (n : Nat) : unitLeaves (numeral (V := V) n) := by
  induction n with
  | zero => exact .inl rfl
  | succ n ih => exact ⟨ih, .inr rfl⟩

private def normalize : IntegerPolynomial V → IntegerPolynomial V
  | .constant (.ofNat n) => numeral n
  | .constant (.negSucc n) => .neg (numeral (n + 1))
  | .variable i => .variable i
  | .add p q => .add (normalize p) (normalize q)
  | .mul p q => .mul (normalize p) (normalize q)
  | .neg p => .neg (normalize p)

private theorem normalize_unit (polynomial : IntegerPolynomial V) : unitLeaves (normalize polynomial) := by
  induction polynomial with
  | constant n => cases n <;> exact numeral_unit _
  | «variable» i => exact True.intro
  | add p q left right => exact ⟨left, right⟩
  | mul p q left right => exact ⟨left, right⟩
  | neg p ih => exact ih

private theorem evaluate_numeral (values : V → SignedRatio) (n : Nat) :
    (numeral (V := V) n).evaluate values = ⟨(n : Int), 1, by decide⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, IntegerPolynomial.evaluate, ih, SignedRatio.add, Int.natCast_succ]

private theorem evaluate_normalize (polynomial : IntegerPolynomial V) (values : V → SignedRatio) :
    (normalize polynomial).evaluate values = polynomial.evaluate values := by
  induction polynomial with
  | constant n =>
    cases n with
    | ofNat n => exact evaluate_numeral _ _
    | negSucc n => simp only [normalize, IntegerPolynomial.evaluate, evaluate_numeral, SignedRatio.neg]; rfl
  | «variable» i => rfl
  | add p q left right => simp only [normalize, IntegerPolynomial.evaluate, left, right]
  | mul p q left right => simp only [normalize, IntegerPolynomial.evaluate, left, right]
  | neg p ih => simp only [normalize, IntegerPolynomial.evaluate, ih]

private def children : IntegerPolynomial V → List (IntegerPolynomial V)
  | .constant _ | .variable _ => []
  | .add p q | .mul p q => [p, q]
  | .neg p => [p]

private def nodes : IntegerPolynomial V → List (IntegerPolynomial V)
  | .constant n => [.constant n]
  | .variable i => [.variable i]
  | .add p q => .add p q :: (nodes p ++ nodes q)
  | .mul p q => .mul p q :: (nodes p ++ nodes q)
  | .neg p => .neg p :: nodes p

private theorem root_member (p : IntegerPolynomial V) : p ∈ nodes p := by
  cases p <;> exact List.mem_cons_self

private theorem closed_children (top expression : IntegerPolynomial V) (inside : expression ∈ nodes top) :
    ∀ child ∈ children expression, child ∈ nodes top := by
  induction top with
  | constant n =>
    rcases List.mem_cons.mp inside with same | absent
    · subst expression
      exact List.forall_mem_nil _
    · cases absent
  | «variable» i =>
    rcases List.mem_cons.mp inside with same | absent
    · subst expression
      exact List.forall_mem_nil _
    · cases absent
  | add p q left right =>
    rcases List.mem_cons.mp inside with same | rest
    · subst expression
      intro child listed
      rcases List.mem_cons.mp listed with first | tail
      · subst child
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (root_member _))
      · rcases List.mem_cons.mp tail with second | impossible
        · subst child
          exact List.mem_cons_of_mem _ (List.mem_append_right _ (root_member _))
        · cases impossible
    · intro child listed
      rcases List.mem_append.mp rest with first | second
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (left first child listed))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (right second child listed))
  | mul p q left right =>
    rcases List.mem_cons.mp inside with same | rest
    · subst expression
      intro child listed
      rcases List.mem_cons.mp listed with first | tail
      · subst child
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (root_member _))
      · rcases List.mem_cons.mp tail with second | impossible
        · subst child
          exact List.mem_cons_of_mem _ (List.mem_append_right _ (root_member _))
        · cases impossible
    · intro child listed
      rcases List.mem_append.mp rest with first | second
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (left first child listed))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (right second child listed))
  | neg p ih =>
    rcases List.mem_cons.mp inside with same | rest
    · subst expression
      intro child listed
      rcases List.mem_cons.mp listed with same | absent
      · subst child
        exact List.mem_cons_of_mem _ (root_member _)
      · cases absent
    · exact fun child listed => List.mem_cons_of_mem _ (ih rest child listed)

private theorem unit_of_member (top expression : IntegerPolynomial V) (inside : expression ∈ nodes top)
    (unit : unitLeaves top) : unitLeaves expression := by
  induction top with
  | constant n =>
    rcases List.mem_cons.mp inside with same | absent
    · exact same.symm ▸ unit
    · cases absent
  | «variable» i =>
    rcases List.mem_cons.mp inside with same | absent
    · exact same.symm ▸ unit
    · cases absent
  | add p q left right =>
    rcases List.mem_cons.mp inside with same | rest
    · exact same.symm ▸ unit
    · rcases List.mem_append.mp rest with first | second
      · exact left first unit.1
      · exact right second unit.2
  | mul p q left right =>
    rcases List.mem_cons.mp inside with same | rest
    · exact same.symm ▸ unit
    · rcases List.mem_append.mp rest with first | second
      · exact left first unit.1
      · exact right second unit.2
  | neg p ih =>
    rcases List.mem_cons.mp inside with same | rest
    · exact same.symm ▸ unit
    · exact ih rest unit

variable {n : Nat}
private abbrev Poly (n : Nat) := IntegerPolynomial (Fin n)
private def total (top : Poly n) : Nat := n + (nodes top).length

private def input (top : Poly n) (index : Fin n) : Fin (total top) :=
  ⟨index.val, by have h := index.isLt; unfold total; omega⟩

private def result (top expression : Poly n) (inside : expression ∈ nodes top) : Fin (total top) :=
  ⟨n + (nodes top).idxOf expression, by
    have bound := List.idxOf_lt_length_of_mem inside
    unfold total
    omega⟩

private def clause (top : Poly n) : (expression : Poly n) → expression ∈ nodes top →
    RationalEquation (Fin (total top))
  | .constant coefficient, inside =>
    let res := result top (.constant coefficient) inside
    if coefficient = 0 then .zero res else .one res
  | .variable index, inside => .equal (result top (.variable index) inside) (input top index)
  | .neg p, inside => .negative (result top p (closed_children _ _ inside p List.mem_cons_self))
      (result top (.neg p) inside)
  | .add p q, inside => .add (result top p (closed_children _ _ inside p List.mem_cons_self))
      (result top q (closed_children _ _ inside q (List.mem_cons_of_mem _ List.mem_cons_self)))
      (result top (.add p q) inside)
  | .mul p q, inside => .multiply (result top p (closed_children _ _ inside p List.mem_cons_self))
      (result top q (closed_children _ _ inside q (List.mem_cons_of_mem _ List.mem_cons_self)))
      (result top (.mul p q) inside)

private def equations (top : Poly n) : List (RationalEquation (Fin (total top))) :=
  (nodes top).attach.map (fun item => clause top item.val item.property)

private theorem clause_member (top expression : Poly n) (inside : expression ∈ nodes top) :
    clause top expression inside ∈ equations top :=
  List.mem_map.mpr ⟨⟨expression, inside⟩, List.mem_attach _ _, rfl⟩

private def extend (top : Poly n) (values : Fin n → SignedRatio) (index : Fin (total top)) : SignedRatio :=
  if external : index.val < n then values ⟨index.val, external⟩
  else
    let internal := index.val - n
    ((nodes top)[internal]'(by have bound := index.isLt; unfold total at bound; dsimp [internal]; omega)).evaluate values

private theorem extend_input (top : Poly n) (values : Fin n → SignedRatio) (index : Fin n) :
    extend top values (input top index) = values index := by
  unfold extend
  have within : (input top index).val < n := index.isLt
  rw [dif_pos within]
  rfl

private theorem extend_result (top expression : Poly n) (values : Fin n → SignedRatio) (inside : expression ∈ nodes top) :
    extend top values (result top expression inside) = expression.evaluate values := by
  unfold extend
  rw [dif_neg (by unfold result; dsimp; omega)]
  have address : (result top expression inside).val - n = (nodes top).idxOf expression := by
    unfold result
    dsimp
    omega
  have bound := List.idxOf_lt_length_of_mem inside
  have namely : (nodes top)[(nodes top).idxOf expression]'bound = expression := by
    apply eq_of_beq
    exact (List.findIdx_getElem (p := fun item => item == expression) (w := bound))
  simp only [address, namely]

private theorem extend_satisfies (top expression : Poly n) (values : Fin n → SignedRatio)
    (inside : expression ∈ nodes top) (unit : unitLeaves top) :
    (clause top expression inside).holds (extend top values) := by
  cases expression with
  | constant coefficient =>
    have choices := unit_of_member top (.constant coefficient) inside unit
    change coefficient = 0 ∨ coefficient = 1 at choices
    rcases choices with rfl | rfl
    · simp only [clause, if_true, RationalEquation.holds, extend_result, IntegerPolynomial.evaluate]
      exact SignedRatio.equiv_refl _
    · simp only [clause, if_neg (show (1 : Int) ≠ 0 by decide), RationalEquation.holds, extend_result, IntegerPolynomial.evaluate]
      exact SignedRatio.equiv_refl _
  | «variable» i =>
    simp only [clause, RationalEquation.holds, extend_result, extend_input, IntegerPolynomial.evaluate]
    exact SignedRatio.equiv_refl _
  | add p q | mul p q =>
    simp only [clause, RationalEquation.holds, extend_result, IntegerPolynomial.evaluate]
    exact SignedRatio.equiv_refl _
  | neg p =>
    simp only [clause, RationalEquation.holds, extend_result, IntegerPolynomial.evaluate]
    exact SignedRatio.equiv_refl _

private theorem value_of_solution (top expression : Poly n) (values : Fin (total top) → SignedRatio)
    (inside : expression ∈ nodes top) (unit : unitLeaves top)
    (solution : ∀ equation ∈ equations top, equation.holds values) :
    (values (result top expression inside)).Equiv (expression.evaluate (fun i => values (input top i))) := by
  have localEq (e : Poly n) (member : e ∈ nodes top) := solution _ (clause_member top e member)
  induction expression with
  | constant coefficient =>
    have choices := unit_of_member top (.constant coefficient) inside unit
    change coefficient = 0 ∨ coefficient = 1 at choices
    rcases choices with rfl | rfl <;> exact localEq _ inside
  | «variable» index => exact localEq _ inside
  | add left right leftIH rightIH =>
    exact SignedRatio.equiv_trans (localEq _ inside) (SignedRatio.add_congr (leftIH _) (rightIH _))
  | mul left right leftIH rightIH =>
    exact SignedRatio.equiv_trans (localEq _ inside) (SignedRatio.mul_congr (leftIH _) (rightIH _))
  | neg below ih =>
    exact SignedRatio.equiv_trans (localEq _ inside) (SignedRatio.neg_congr (ih _))

/-- Name every intermediate value and ask that the polynomial's output is
zero. Generated equations contain only the bounded list of operation kinds. -/
def compile (problem : RationalZeroProblem) : RationalEquationSystem :=
  let top := normalize problem.polynomial
  ⟨total top, .zero (result top top (root_member _)) :: equations top⟩

/-- Exact witnesses in both directions for introducing intermediate rational values. -/
theorem compile_correct (problem : RationalZeroProblem) :
    (compile problem).Solvable ↔ problem.Solvable := by
  let top := normalize problem.polynomial
  constructor
  · rintro ⟨values, solution⟩
    refine ⟨fun i => values (input top i), ?_⟩
    have evaluated := value_of_solution top top values (root_member _) (normalize_unit _) (fun equation member =>
      solution equation (List.mem_cons_of_mem _ member))
    have vanishes := solution (.zero (result top top (root_member _))) List.mem_cons_self
    have agrees := SignedRatio.equiv_trans (SignedRatio.equiv_symm evaluated) vanishes
    simpa only [top, evaluate_normalize] using agrees
  · rintro ⟨values, vanishes⟩
    refine ⟨extend top values, ?_⟩
    intro equation member
    rcases List.mem_cons.mp member with root | inside
    · subst equation
      change ((extend top values) (result top top (root_member _))).Equiv .zero
      rw [extend_result]
      simpa only [top, evaluate_normalize] using vanishes
    · obtain ⟨item, _, rfl⟩ := List.mem_map.mp inside
      exact extend_satisfies top item.val values item.property (normalize_unit _)

end ElementaryRationalEquations
end Thesis.Probability
