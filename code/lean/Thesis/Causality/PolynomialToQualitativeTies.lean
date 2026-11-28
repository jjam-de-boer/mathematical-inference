import Thesis.Causality.RationalEquationClearing
import Thesis.Causality.QualitativeTiesToPolynomial

namespace Thesis.Causality.QualitativeTies
open Probability

/-!
# Rational polynomial solvability and causal tie realizability

The two translations are computable on finite input. Each returns a
single new instance, and satisfiability of that instance is equivalent to
satisfiability of its source. In the causal language the graph is supplied
and consists of directed edges and isolated vertices. All vertices are
recorded bits. The only judgments are equal-plausibility comparisons of
two unary events in the same experiment, where an experiment is observation
or one hard setting. A realization uses one common finite rational urn game.

The arithmetic-to-causal translation names the rational values of
subexpressions, then uses one common positive denominator to present all
of them by bounded rates. Pell pairs certify that a finite witness can
use an arbitrarily small positive denominator rate. Fresh selector edges
implement all operations without joining components of the causal graph.
The reverse translation uses four-square witnesses for the rate bounds
and combines the equations into one polynomial by summing squares.
-/

namespace PolynomialToTies

/-- Compute the single causal instance from an integer polynomial. The
output type enforces the graph and syntax restrictions by construction. -/
def compile (problem : RationalZeroProblem) : Instance :=
  let elementary := ElementaryRationalEquations.compile problem
  let monomials := RationalEquationClearing.compile elementary
  BoundedArithmeticTies.compile (BoundedMonomialEquations.compile monomials)

/-- The compiled ties have a common finite rational realization exactly
when the supplied polynomial has a rational zero. -/
theorem compile_correct (problem : RationalZeroProblem) : (compile problem).Realizable ↔ problem.Solvable :=
  (BoundedArithmeticTies.compile_correct _).trans
    ((BoundedMonomialEquations.compile_correct _).trans
      ((RationalEquationClearing.compile_correct _).trans (ElementaryRationalEquations.compile_correct _)))

end PolynomialToTies

/-- Both explicit reductions preserve and reflect the corresponding
existential witness. This states the boundary for ties alone. -/
theorem computable_reductions :
    (∀ instanceₛ, (TiesToPolynomial.compile instanceₛ).Solvable ↔ instanceₛ.Realizable) ∧
    (∀ polynomial, (PolynomialToTies.compile polynomial).Realizable ↔ polynomial.Solvable) :=
  ⟨TiesToPolynomial.compile_correct, PolynomialToTies.compile_correct⟩

end Thesis.Causality.QualitativeTies
