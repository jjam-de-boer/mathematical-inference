import Thesis.Probability.Distros.RationalLinearProjection
import Thesis.Probability.ExactLogLinear
import Thesis.Causality.SelectedEntropy
import Thesis.CausalTransport.GraphQueryUncertainty

namespace Thesis
namespace Causality

open Probability Probability.Distros RationalLinear

/-!
# Hidden-variable elimination of elemental Shannon inequalities

Coordinates are subset masks on `n` bits, with the high bits reserved for
hidden nodes.  Elemental monotonicity and submodularity, together with
supplied CI equalities, form an integer-coefficient cone.  Fourier–Motzkin
`project` eliminates the last coordinates (hidden-touching subsets).

This is Chaves-style *attempted* elimination: sound for the symbolic cone,
incomplete as a compatibility test, and not a replacement for the existing
binary-bow and instrumental classifications.  Entropy values themselves are
`ExactLog`, so Distro checking instantiates the same integer rows at selected
entropies rather than embedding logarithms into `SignedRatio`.
-/

def scaleInt (coefficient : Int) (value : ExactLog) : ExactLog :=
  match coefficient with
  | Int.ofNat n => ExactLog.scaleNat n value
  | Int.negSucc n => ExactLog.neg (ExactLog.scaleNat (n + 1) value)

def intDot : (variables : Nat) → (Fin variables → Int) → (Fin variables → ExactLog) → ExactLog
  | 0, _, _ => ExactLog.zero
  | variables + 1, coefficients, values =>
      ExactLog.add (scaleInt (coefficients (Fin.last variables)) (values (Fin.last variables)))
        (intDot variables (fun i => coefficients i.castSucc) (fun i => values i.castSucc))

def holdsEntropy (row : Inequality variables) (values : Fin variables → ExactLog) : Prop :=
  ExactLog.LE (intDot variables row.coefficients values) ExactLog.zero

instance (row : Inequality variables) (values : Fin variables → ExactLog) :
    Decidable (holdsEntropy row values) :=
  inferInstanceAs (Decidable (ExactLog.LE _ _))

def ShannonCone.satisfiesEntropy (rows : List (Inequality variables))
    (values : Fin variables → ExactLog) : Prop :=
  ∀ row ∈ rows, holdsEntropy row values

instance (rows : List (Inequality variables)) (values : Fin variables → ExactLog) :
    Decidable (ShannonCone.satisfiesEntropy rows values) :=
  inferInstanceAs (Decidable (∀ row ∈ rows, holdsEntropy row values))

/-- Bitwise union of subset masks.  The `n`-bit bound holds for every pair of
masks; the `dite` keeps the constructor total without a separate bitwise lemma. -/
def maskUnion (n : Nat) (left right : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if h : left.val ||| right.val < 2 ^ n then
    ⟨left.val ||| right.val, h⟩
  else
    left

def maskInter (n : Nat) (left right : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if h : left.val &&& right.val < 2 ^ n then
    ⟨left.val &&& right.val, h⟩
  else
    right

def maskSubset (n : Nat) (small large : Fin (2 ^ n)) : Bool :=
  decide (small.val &&& large.val = small.val)

def allMasks (n : Nat) : List (Fin (2 ^ n)) :=
  List.ofFn (fun index : Fin (2 ^ n) => index)

def unitRow (variables : Nat) (index : Fin variables) (coefficient : Int) : Fin variables → Int :=
  fun i => if i = index then coefficient else 0

def addRows (variables : Nat) (first second : Fin variables → Int) : Fin variables → Int :=
  fun i => first i + second i

def monotonicityRow (n : Nat) (small large : Fin (2 ^ n)) : Inequality (2 ^ n) :=
  ⟨addRows _ (unitRow _ small 1) (unitRow _ large (-1)), SignedRatio.zero⟩

def submodularityRow (n : Nat) (left right : Fin (2 ^ n)) : Inequality (2 ^ n) :=
  ⟨fun i =>
      (if i = maskUnion n left right then 1 else 0) +
      (if i = maskInter n left right then 1 else 0) +
      (if i = left then -1 else 0) +
      (if i = right then -1 else 0),
    SignedRatio.zero⟩

def elementalRows (n : Nat) : List (Inequality (2 ^ n)) :=
  (allMasks n).flatMap fun small =>
    (allMasks n).flatMap fun large =>
      let mono :=
        if small ≠ large && maskSubset n small large then [monotonicityRow n small large] else []
      let sub :=
        if decide (small.val ≤ large.val) then [submodularityRow n small large] else []
      mono ++ sub

/-- Two opposing inequalities encode a CI identity `I(X;Y|Z)=0` on mask indices. -/
def ciEqualityRows (n : Nat) (xz yz xyz z : Fin (2 ^ n)) : List (Inequality (2 ^ n)) :=
  let coeffs : Fin (2 ^ n) → Int := fun i =>
    (if i = xz then 1 else 0) + (if i = yz then 1 else 0) +
      (if i = xyz then -1 else 0) + (if i = z then -1 else 0)
  [⟨coeffs, SignedRatio.zero⟩, ⟨fun i => -coeffs i, SignedRatio.zero⟩]

def eliminateLast : (dropped kept : Nat) → List (Inequality (kept + dropped)) →
    List (Inequality kept)
  | 0, _, rows => rows
  | dropped + 1, kept, rows =>
      eliminateLast dropped kept (project (variables := kept + dropped) rows)

def prefixValues : (dropped kept : Nat) → (Fin (kept + dropped) → SignedRatio) →
    Fin kept → SignedRatio
  | 0, _, values => values
  | dropped + 1, kept, values =>
      prefixValues dropped kept (fun i => values i.castSucc)

theorem values_eq_extend (n : Nat) (values : Fin (n + 1) → SignedRatio) :
    extend (fun i => values i.castSucc) (values (Fin.last n)) = values := by
  funext i
  by_cases earlier : i.val < n
  · let j : Fin n := ⟨i.val, earlier⟩
    have same : i = j.castSucc := Fin.ext rfl
    rw [same, extend_castSucc]
  · simp only [extend, earlier, ↓reduceDIte]
    apply congrArg values
    apply Fin.ext
    have hle : n ≤ i.val := Nat.le_of_not_lt earlier
    have hlt : i.val < n + 1 := i.isLt
    have lastVal : (Fin.last n).val = n := rfl
    omega

theorem eliminateLast_sound (dropped kept : Nat)
    (rows : List (Inequality (kept + dropped)))
    (values : Fin (kept + dropped) → SignedRatio)
    (valid : Satisfies rows values) :
    Satisfies (eliminateLast dropped kept rows) (prefixValues dropped kept values) := by
  induction dropped with
  | zero => exact valid
  | succ dropped ih =>
      unfold eliminateLast prefixValues
      refine ih (project (variables := kept + dropped) rows)
        (fun i => values i.castSucc) ?_
      exact project_sound rows (fun i => values i.castSucc) (values (Fin.last _))
        (by
          simpa only [values_eq_extend] using valid)

/-- Hidden high-bits occupy the last `2^observed * (2^hidden - 1)` coordinates
when masks are ordinary binary.  For a single hidden high bit this is the
upper half. -/
def eliminateHighBit (observed : Nat) (rows : List (Inequality (2 ^ (observed + 1)))) :
    List (Inequality (2 ^ observed)) :=
  let eq : 2 ^ (observed + 1) = 2 ^ observed + 2 ^ observed := by
    rw [Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
  eliminateLast (2 ^ observed) (2 ^ observed) (eq ▸ rows)

/-- Observational evaluation of a remaining cone on selected-coordinate entropy. -/
def observedEntropyVector (S : ObservedSignature) (μ : Distro S.Assignment)
    (index : Fin (2 ^ S.count)) : ExactLog :=
  selectedEntropy μ fun node => decide ((index.val / (2 ^ node.val)) % 2 = 1)

def ShannonCone.holdsOnDistro (S : ObservedSignature)
    (rows : List (Inequality (2 ^ S.count))) (μ : Distro S.Assignment) : Prop :=
  ShannonCone.satisfiesEntropy rows (observedEntropyVector S μ)

instance (S : ObservedSignature) (rows : List (Inequality (2 ^ S.count)))
    (μ : Distro S.Assignment) : Decidable (ShannonCone.holdsOnDistro S rows μ) :=
  inferInstanceAs (Decidable (ShannonCone.satisfiesEntropy _ _))

/-- Fourier–Motzkin hidden-variable elimination is not a complete
compatibility test for this development. -/
def hiddenVariableEliminationComplete : Bool := false

theorem hiddenVariableEliminationComplete_false :
    hiddenVariableEliminationComplete = false := rfl

end Causality
end Thesis
