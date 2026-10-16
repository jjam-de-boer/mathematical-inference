import Thesis.Probability.Combinatorics

namespace Thesis.Probability.Distros
open Combinatorics

/-- Reindex a finite triangular sum by its total index. No infinite sum or
subtraction of signed indices is involved. -/
theorem natSum_triangle (n : Nat) (f : Nat → Nat → Nat) :
    natSum (n + 1) (fun i => natSum (n - i + 1) (fun j => f i j)) =
      natSum (n + 1) (fun total => natSum (total + 1) (fun i => f i (total - i))) := by
  induction n generalizing f with
  | zero => simp only [natSum, Nat.sub_zero, Nat.zero_add]
  | succ n ih =>
      have left : natSum (n + 1 + 1) (fun i => natSum (n + 1 - i + 1) (fun j => f i j)) =
          natSum (n + 1 + 1) (fun j => f 0 j) +
            natSum (n + 1) (fun i => natSum (n - i + 1) (fun j => f (i + 1) j)) := by
        rw [natSum_head]
        simp only [Nat.sub_zero, Nat.succ_sub_succ]
      have split : natSum (n + 1 + 1) (fun total => natSum (total + 1) (fun i => f i (total - i))) =
          natSum (n + 1 + 1) (fun total => f 0 total) +
            natSum (n + 1 + 1) (fun total => natSum total (fun i => f (i + 1) (total - (i + 1)))) := by
        rw [← natSum_add]
        apply natSum_congr
        intro total _
        simpa only [Nat.sub_zero] using natSum_head total (fun i => f i (total - i))
      have tail : natSum (n + 1 + 1) (fun total => natSum total (fun i => f (i + 1) (total - (i + 1)))) =
          natSum (n + 1) (fun total => natSum (total + 1) (fun i => f (i + 1) (total - i))) := by
        rw [natSum_head]
        simp only [natSum_zero, Nat.zero_add, Nat.succ_sub_succ]
      rw [left, split, tail, ih]

end Thesis.Probability.Distros
