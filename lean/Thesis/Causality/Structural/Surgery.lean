import Thesis.Causality.Structural.SurgeryEquivalence

/-!
Compatibility facade for compact surgery and atomic-compilation agreement.

The compact construction itself lives in `SurgeryCore`; the comparison theorem
now lives in `SurgeryEquivalence`, whose dependency on `Atomic` makes the
layering explicit. Existing imports of `Thesis.Causality.Structural.Surgery`
continue to expose the same theorem.
-/
