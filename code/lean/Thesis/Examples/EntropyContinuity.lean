import Thesis.Probability.Distros.EntropyContinuity

/-!
# A single entropy modulus covers zero, one and interior masses

Scalar examples compare both unit-interval endpoints and the midpoint
with nearby rational masses of denominator 4096, obtaining entropy error
at most `1/4`. The endpoint cases require no positive observed mass and
do not depend on equal fraction presentations.

The finite-law fixture moves one part in 4194304 away from a point mass,
keeps a shared zero cell and null outliers, and bounds entropy change by
`1/8`. Both coordinatewise directions of the computed threshold are checked
explicitly before applying the law theorem. The threshold has a positive
numerator; the stated entropy estimate still retains its required tolerance
and support premises.
-/

namespace Thesis.Examples.EntropyContinuity
open Probability Probability.Distros

/-- The same modulus applies at both endpoints with unrelated denominator
presentations and at an interior probability. -/
example : EntropyWithin QProb.zero ⟨1, 4096, by decide⟩
    (ExactLog.ofSignedRatio ⟨1, 4, by decide⟩) :=
  entropyTerm_continuity _ _ (by decide) (by decide) 2 (by decide +kernel) (by decide +kernel)

example : EntropyWithin QProb.one ⟨4095, 4096, by decide⟩
    (ExactLog.ofSignedRatio ⟨1, 4, by decide⟩) :=
  entropyTerm_continuity _ _ (by decide) (by decide) 2 (by decide +kernel) (by decide +kernel)

example : EntropyWithin ⟨1, 2, by decide⟩ ⟨2049, 4096, by decide⟩
    (ExactLog.ofSignedRatio ⟨1, 4, by decide⟩) :=
  entropyTerm_continuity _ _ (by decide) (by decide) 2 (by decide +kernel) (by decide +kernel)

private def grid : EntropyGrid Nat := ⟨[0, 1, 2], by decide⟩
private def point : Distro Nat := ⟨⟨[(0, 1), (99, 0)], 1, by decide, by decide⟩⟩
private def nearby : Distro Nat := ⟨⟨[(0, 4194303), (1, 1), (2, 0), (88, 0)], 4194304, by decide, by decide⟩⟩
private def tolerance : QProb := ⟨1, 8, by decide⟩
private theorem pointSupport : point.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ point.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem nearbySupport : nearby.AlmostSurely (fun value => value ∈ grid.cells) := by
  change ∀ atom ∈ nearby.record.atoms, 0 < atom.2 → atom.1 ∈ grid.cells
  decide +kernel
private theorem leftClose : ∀ value ∈ grid.cells,
    QProb.LE (point.pmf value) (QProb.add (nearby.pmf value) (grid.continuityThreshold tolerance)) := by decide +kernel
private theorem rightClose : ∀ value ∈ grid.cells,
    QProb.LE (nearby.pmf value) (QProb.add (point.pmf value) (grid.continuityThreshold tolerance)) := by decide +kernel

/-- Zero observed cells may gain positive mass. A shared null grid cell and
null outliers remain present, with no equality of atom records required. -/
example : ExactLog.LE (nearby.entropy grid nearbySupport)
    (ExactLog.add (point.entropy grid pointSupport) (ExactLog.ofSignedRatio tolerance.toSignedRatio)) :=
  (point.entropy_uniform_continuity nearby grid pointSupport nearbySupport tolerance (by decide) leftClose rightClose).2

example (tolerance : QProb) :
    0 < (grid.continuityThreshold tolerance).num := Nat.zero_lt_one

end Thesis.Examples.EntropyContinuity
