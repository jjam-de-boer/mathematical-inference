import Thesis.Probability.Core

namespace Thesis
namespace Probability
namespace ConstructiveInteger

/-!
# Explicit integer-to-natural conversions for nonnegative weights

The conversion is justified directly by the two integer constructors.  These
small proofs avoid transitive classical dependencies in more general standard
conversion lemmas.  They neither truncate a negative atom weight nor assume
that an arbitrary integer is nonnegative: callers supply the relevant bound.
-/

theorem toNat_positive (value : Int) (positive : 0 < value) : 0 < value.toNat := by
  cases value with
  | ofNat number => exact Int.ofNat_lt.mp positive
  | negSucc number =>
      exact False.elim (Int.lt_irrefl 0 (Int.lt_trans positive (Int.negSucc_lt_zero number)))

theorem toNat_cast (value : Int) (nonnegative : 0 ≤ value) : (value.toNat : Int) = value := by
  cases value with
  | ofNat number => rfl
  | negSucc number =>
      exact False.elim (Int.not_lt_of_ge nonnegative (Int.negSucc_lt_zero number))

end ConstructiveInteger
end Probability
end Thesis
