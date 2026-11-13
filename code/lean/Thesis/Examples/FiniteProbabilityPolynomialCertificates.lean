import Thesis.Probability.FiniteProbabilityPolynomialCertificates
import Thesis.Examples.FiniteProbabilityPolynomial

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteProbabilityPolynomialCertificates

open RationalPolynomial Probability.FiniteProbabilityPolynomial Examples.FiniteProbabilityPolynomial

/-!
# End-to-end upper and lower bounds from checked polynomial data

Compile the actual biased-bit xor probability with automatic variable encoding.
Nonnegativity is certified by its two disjoint source-state products.  The
upper bound one uses the two complementary products and source normalization:

`1 - (a*d + b*c) = a*c + b*d - (a+b-1)*(c+d) - (c+d-1)`.

The negative equality multipliers are legal because those source equations
are proved zero for the actual parameter assignment.  No probability-binding
proof, normalization assertion or optimizer result is supplied by this test.
-/

def compiled := compileEncoded law enumeration complete (fun _ => inferInstance) event
def a := compiled.code first false
def b := compiled.code first true
def c := compiled.code second false
def d := compiled.code second true
def root : Polynomial compiled.variableCount := constant SignedRatio.one
def lowerCertificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount 2 :=
  ⟨[⟨SignedRatio.one, root, [a, d]⟩, ⟨SignedRatio.one, root, [b, c]⟩], []⟩
def upperCertificate : PolynomialBoundCertificate.Certificate compiled.variableCount compiled.variableCount 2 :=
  ⟨[⟨SignedRatio.one, root, [a, c]⟩, ⟨SignedRatio.one, root, [b, d]⟩],
    [⟨first, neg (add (coordinate c) (coordinate d))⟩, ⟨second, constant ⟨-1, 1, by decide⟩⟩]⟩

theorem lower_checked : compiled.checkLower SignedRatio.zero lowerCertificate = true := by decide +kernel
theorem upper_checked : compiled.checkUpper SignedRatio.one upperCertificate = true := by decide +kernel
theorem actual_lower : SignedRatio.LE SignedRatio.zero (law.prior.probVal event).toSignedRatio :=
  compiled.checkLower_sound _ _ lower_checked
theorem actual_upper : SignedRatio.LE (law.prior.probVal event).toSignedRatio SignedRatio.one :=
  compiled.checkUpper_sound _ _ upper_checked
theorem original_probability_order : QProb.LE (law.prior.probVal event) QProb.one :=
  (SignedRatio.toSignedRatio_le_iff _ _).mp actual_upper

end FiniteProbabilityPolynomialCertificates
end Examples
end Probability
end Thesis
