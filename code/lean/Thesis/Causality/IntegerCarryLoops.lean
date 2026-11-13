import Thesis.Causality.BinaryIntegerCarry

namespace Thesis.Causality.IntegerEquations

/-!
# From supplied carry loops to nonnegative homogeneous directions

Concatenating least-significant-first digit words shifts the second word
by a power of two. The corresponding signed row identity also retains the
final carry, so it applies to loops rather than only accepting words.

Suppose a word q returns to a carry c, and a suffix r takes c to zero.
Write Q and R for their decoded natural vectors. Then

  c = A*Q + 2^length(q)*c,     c = A*R.

Consequently h = Q + (2^length(q)-1)*R is a natural vector with A*h = 0.
If q is nonempty and R has a positive selected coordinate, h has a positive
coordinate there too. All witnesses are computed from the supplied words.

Both positivity conditions matter: a zero-length loop yields zero, and a
zero-only loop followed by an empty suffix does too. Arbitrarily many high
zero digits give infinitely many words for one bounded value, so merely
finding a cycle is not a coordinate-unboundedness proof.

This module neither finds loops nor proves that every unbounded coordinate
provides one. It supplies no boundedness classifier or Petri pumping test.
Adding a homogeneous direction preserves equations; actual Petri executions
still require all intermediate firing guards.
-/

variable {rows variables : Nat}

/-- The second word contains the higher digits, including when either
word is empty. This identity concerns actual natural values, not only rows. -/
theorem decodeWord_append (first second : List (Digit variables)) (index : Fin variables) :
    decodeWord (first ++ second) index =
      decodeWord first index + 2 ^ first.length * decodeWord second index := by
  induction first with
  | nil => simp only [List.nil_append, decodeWord, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons digit rest ih =>
      simp only [List.cons_append, decodeWord, List.length_cons]
      rw [ih, Nat.mul_add, Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

/-- A partial word retains its terminal carry exactly. Parity was checked
by each transition, so no rounded division enters this identity. -/
theorem System.run_row_identity (system : System rows variables) {before after : system.Carry}
    {word : List (Digit variables)}
    (accepted : FiniteLabelledReachability.run system.advance before word = some after) (row : Fin rows) :
    system.carryValue before row = rowValue (system.coefficients row) (decodeWord word) +
      ((2 ^ word.length : Nat) : Int) * system.carryValue after row := by
  induction word generalizing before with
  | nil =>
      cases Option.some.inj accepted
      simp only [decodeWord, rowValue_zero, List.length_nil, Nat.pow_zero, Int.natCast_one,
        Int.one_mul, Int.zero_add]
  | cons digit rest ih =>
      rcases Option.bind_eq_some_iff.mp accepted with ⟨next, advanced, remaining⟩
      have first := system.advance_sound advanced row
      have tail := ih remaining
      simp only [decodeWord, rowValue_add, rowValue_scale, List.length_cons, Nat.pow_succ, Int.natCast_mul]
      change system.carryValue before row =
        (rowValue (system.coefficients row) (digitValues digit) +
          2 * rowValue (system.coefficients row) (decodeWord rest)) +
        (((2 ^ rest.length : Nat) : Int) * 2) * system.carryValue after row
      rw [first, tail]
      simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.add_assoc]

def System.homogeneous (system : System rows variables) : System rows variables where
  coefficients := system.coefficients
  rhs := fun _ => 0

/-- Natural data by construction. The subtraction is only in the scalar
2^length-1, which is nonnegative even for an empty loop. -/
def loopDirection (cycle suffix : List (Digit variables)) : Fin variables → Nat :=
  fun index => decodeWord cycle index + (2 ^ cycle.length - 1) * decodeWord suffix index

theorem loopDirection_nil (suffix : List (Digit variables)) :
    loopDirection [] suffix = (fun _ => 0) := by
  funext index
  simp only [loopDirection, decodeWord, List.length_nil, Nat.pow_zero, Nat.sub_self, Nat.zero_mul, Nat.zero_add]

/-- A supplied loop and accepting suffix compute a homogeneous solution.
Reachability of the loop from the original right-hand side is unnecessary
for this algebraic claim; a base solution is separate data below. -/
theorem System.loopDirection_satisfies (system : System rows variables) {carry : system.Carry}
    {cycle suffix : List (Digit variables)}
    (loop : FiniteLabelledReachability.run system.advance carry cycle = some carry)
    (ending : FiniteLabelledReachability.run system.advance carry suffix = some system.zeroCarry) :
    system.homogeneous.Satisfies (loopDirection cycle suffix) := by
  intro row
  have closed := system.run_row_identity loop row
  have tail := system.run_to_zero_sound ending row
  have positive := Nat.two_pow_pos cycle.length
  have scalar : ((2 ^ cycle.length - 1 : Nat) : Int) = ((2 ^ cycle.length : Nat) : Int) - 1 := by omega
  change rowValue (system.coefficients row) (loopDirection cycle suffix) = 0
  unfold loopDirection
  rw [rowValue_add, rowValue_scale, scalar, tail, Int.sub_mul, Int.one_mul]
  omega

/-- A nonempty loop and a positive suffix coordinate force positive
growth. An arbitrary cycle, or an infinite family of zero-padded words,
does not supply the suffix premise. -/
theorem loopDirection_pos {cycle suffix : List (Digit variables)} (nonempty : cycle ≠ [])
    (index : Fin variables) (suffixPositive : 0 < decodeWord suffix index) :
    0 < loopDirection cycle suffix index := by
  cases cycle with
  | nil => exact False.elim (nonempty rfl)
  | cons digit rest =>
      have positive := Nat.two_pow_pos rest.length
      have scalarPositive : 0 < 2 ^ (digit :: rest).length - 1 := by
        simp only [List.length_cons, Nat.pow_succ]
        omega
      have productPositive := Nat.mul_pos scalarPositive suffixPositive
      unfold loopDirection
      omega

/-- A homogeneous direction can be reused at every supplied base solution.
This is an equation-preservation theorem, not an execution-order theorem. -/
theorem System.satisfies_add_homogeneous (system : System rows variables)
    {base direction : Fin variables → Nat} (valid : system.Satisfies base)
    (null : system.homogeneous.Satisfies direction) (multiple : Nat) :
    system.Satisfies (fun index => base index + multiple * direction index) := by
  intro row
  have zero : rowValue (system.coefficients row) direction = 0 := null row
  rw [rowValue_add, rowValue_scale, zero, Int.mul_zero, Int.add_zero]
  exact valid row

end Thesis.Causality.IntegerEquations
