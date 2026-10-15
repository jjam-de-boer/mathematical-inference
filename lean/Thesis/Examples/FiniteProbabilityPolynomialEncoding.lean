import Thesis.Probability.FiniteProbabilityPolynomialEncoding
import Thesis.Examples.FiniteProbabilityPolynomial

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteProbabilityPolynomialEncoding

open Probability.FiniteProbabilityPolynomial Examples.FiniteProbabilityPolynomial

/-!
# Automatic variable allocation, probability binding and normalization

Reuse the duplicate-enumeration, biased-bit fixture.  Its six listed cells
contain only four distinct coordinate/state pairs.  The encoding constructs
four variables with a proved decoder, then binds every one to its actual
singleton probability.  No manual cell-code table or probability-binding
proof is supplied to this interface.

The coordinate normalization polynomials vanish, and a zero-containing source
law uses exactly the same encoding.  The compiled mixed event still has its
seven-twelfths value.  These are probability semantics, not optimizer output.
-/

def witness := encoding enumeration complete (fun _ => inferInstance)
def coded := sourceCode witness
def actual := sourceParameters law (fun _ => inferInstance) witness
def program := compile enumeration (fun _ => inferInstance) coded event
theorem four_variables : witness.card = 4 := by decide +kernel
theorem binding_constructed (index : Fin 2) (value : Bool) : SignedRatio.Equiv (actual (coded index value))
    (cellProbability law (fun _ => inferInstance) index value).toSignedRatio :=
  sourceParameters_binding law (fun _ => inferInstance) witness index value
theorem all_parameters_nonnegative (index : Fin witness.card) : SignedRatio.Nonnegative (actual index) :=
  sourceParameters_nonnegative law (fun _ => inferInstance) witness index
theorem coordinate_normalized (index : Fin 2) : SignedRatio.Equiv
    (RationalPolynomial.evaluate (normalization enumeration (fun _ => inferInstance) coded index) actual) SignedRatio.zero :=
  normalization_sound law enumeration complete (fun _ => inferInstance) coded actual binding_constructed index
theorem compiled_value : SignedRatio.Equiv (RationalPolynomial.evaluate program actual) ⟨7, 12, by decide⟩ := by decide +kernel

def actualZero := sourceParameters zeroLaw (fun _ => inferInstance) witness
theorem zero_cell_retained : (actualZero (coded first false)).num = 0 := by decide +kernel
theorem zero_law_normalized (index : Fin 2) : SignedRatio.Equiv
    (RationalPolynomial.evaluate (normalization enumeration (fun _ => inferInstance) coded index) actualZero) SignedRatio.zero :=
  normalization_sound zeroLaw enumeration complete (fun _ => inferInstance) coded actualZero
    (sourceParameters_binding zeroLaw (fun _ => inferInstance) witness) index

end FiniteProbabilityPolynomialEncoding
end Examples
end Probability
end Thesis
