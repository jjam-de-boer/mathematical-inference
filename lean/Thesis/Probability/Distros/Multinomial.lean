import Thesis.Probability.Distros.Basic

namespace Thesis
namespace Probability
namespace Distros

/-!
Multinomial distro: occupancy counts of independent categorical draws.

The construction is recursive in the number of categories.  Splitting off one
category reduces the remaining occupancy problem to a binomial choice, after
which the binomial theorem reconstitutes the normaliser `(∑ weights)^trials`.
-/

open Combinatorics

/-- Recursive occupancy atoms: each list is a composition of `trials` into
`weights.length` parts, weighted by the corresponding multinomial term. -/
def multinomialAtoms (trials : Nat) : List Nat → List (List Nat × Nat)
  | [] => if trials = 0 then [([], 1)] else []
  | weight :: rest =>
      (List.range (trials + 1)).flatMap fun used =>
        (multinomialAtoms (trials - used) rest).map fun atom =>
          (used :: atom.1, binom trials used * weight ^ used * atom.2)

theorem totalMass_flatMap (xs : List α) (f : α → List (Ω × Nat)) :
    FiniteProbRecord.totalMass (xs.flatMap f) =
      (xs.map (fun x => FiniteProbRecord.totalMass (f x))).sum := by
  induction xs with
  | nil => simp [FiniteProbRecord.totalMass]
  | cons x xs ih =>
      have hdef : (x :: xs).flatMap f = f x ++ xs.flatMap f := by
        simp [List.flatMap]
      rw [hdef, FiniteProbRecord.totalMass_append, ih]
      simp

theorem totalMass_range (n : Nat) (f : Nat → List (Ω × Nat)) :
    FiniteProbRecord.totalMass ((List.range n).flatMap f) =
      natSum n (fun i => FiniteProbRecord.totalMass (f i)) := by
  induction n with
  | zero =>
      simp [List.range_zero, List.flatMap, FiniteProbRecord.totalMass, natSum]
  | succ n ih =>
      have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      have hdef : (List.range n ++ [n]).flatMap f =
          (List.range n).flatMap f ++ f n := by
        simp [List.flatMap]
      rw [hrange, hdef, FiniteProbRecord.totalMass_append, ih]
      rfl

theorem totalMass_multinomialAtoms :
    forall weights : List Nat, forall trials : Nat,
      FiniteProbRecord.totalMass (multinomialAtoms trials weights) =
        weights.sum ^ trials := by
  intro weights
  induction weights with
  | nil =>
      intro trials
      cases trials with
      | zero => simp [multinomialAtoms, FiniteProbRecord.totalMass]
      | succ trials => simp [multinomialAtoms, FiniteProbRecord.totalMass]
  | cons weight rest ih =>
      intro trials
      unfold multinomialAtoms
      rw [totalMass_range]
      have hterm :
          natSum (trials + 1) (fun used =>
            FiniteProbRecord.totalMass
              ((multinomialAtoms (trials - used) rest).map fun atom =>
                (used :: atom.1,
                  binom trials used * weight ^ used * atom.2))) =
            natSum (trials + 1) (fun used =>
              binomTerm trials weight rest.sum used) := by
        apply natSum_congr
        intro used hused
        have hmap :
            FiniteProbRecord.totalMass
                ((multinomialAtoms (trials - used) rest).map fun atom =>
                  (used :: atom.1,
                    binom trials used * weight ^ used * atom.2)) =
              binom trials used * weight ^ used *
                FiniteProbRecord.totalMass
                  (multinomialAtoms (trials - used) rest) :=
          FiniteProbRecord.totalMass_map_weight
            (multinomialAtoms (trials - used) rest)
            (fun counts => used :: counts)
            (binom trials used * weight ^ used)
        rw [hmap, ih (trials - used)]
        simp [binomTerm]
      rw [hterm, binomial_theorem]
      simp [List.sum_cons]

theorem eventMass_flatMap (xs : List α) (f : α → List (Ω × Nat))
    (event : Event Ω) :
    FiniteProbRecord.eventMass (xs.flatMap f) event =
      (xs.map (fun x => FiniteProbRecord.eventMass (f x) event)).sum := by
  induction xs with
  | nil => simp [FiniteProbRecord.eventMass]
  | cons x xs ih =>
      have hdef : (x :: xs).flatMap f = f x ++ xs.flatMap f := by
        simp [List.flatMap]
      rw [hdef, FiniteProbRecord.eventMass_append, ih]
      simp

theorem eventMass_range (n : Nat) (f : Nat → List (Ω × Nat))
    (event : Event Ω) :
    FiniteProbRecord.eventMass ((List.range n).flatMap f) event =
      natSum n (fun i => FiniteProbRecord.eventMass (f i) event) := by
  induction n with
  | zero =>
      simp [List.range_zero, List.flatMap, FiniteProbRecord.eventMass, natSum]
  | succ n ih =>
      have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
      have hdef : (List.range n ++ [n]).flatMap f =
          (List.range n).flatMap f ++ f n := by
        simp [List.flatMap]
      rw [hrange, hdef, FiniteProbRecord.eventMass_append, ih]
      rfl

/-- Closed multinomial term of a weight list against an occupancy list.
Length mismatch is zero.  When the occupancy sums to `trials`, this is the
atom weight produced by `multinomialAtoms`. -/
def multinomialWeight : List Nat → List Nat → Nat
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | w :: ws, c :: cs =>
      binom (c + cs.sum) c * w ^ c * multinomialWeight ws cs

/-- Prefixing every occupancy list with `used` cannot hit the empty
singleton. -/
theorem eventMass_map_cons_nil (used factor : Nat)
    (atoms : List (List Nat × Nat)) :
    FiniteProbRecord.eventMass
        (atoms.map fun atom => (used :: atom.1, factor * atom.2))
        (FiniteProbRecord.singletonEvent []) = 0 := by
  induction atoms with
  | nil => simp [FiniteProbRecord.eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨rest, weight⟩
      simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent, ih]

/-- Prefixing occupancy lists with `used` hits `{c :: cs}` only on the
matching first coordinate. -/
theorem eventMass_map_cons_singleton (used factor c : Nat) (cs : List Nat)
    (atoms : List (List Nat × Nat)) :
    FiniteProbRecord.eventMass
        (atoms.map fun atom => (used :: atom.1, factor * atom.2))
        (FiniteProbRecord.singletonEvent (c :: cs)) =
      if used = c then
        factor * FiniteProbRecord.eventMass atoms
          (FiniteProbRecord.singletonEvent cs)
      else 0 := by
  induction atoms with
  | nil =>
      simp [FiniteProbRecord.eventMass]
  | cons atom atoms ih =>
      rcases atom with ⟨rest, weight⟩
      simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
      by_cases heq : used = c
      · simp [heq] at ih ⊢
        by_cases hrest : rest = cs
        · simp [hrest, ih, Nat.mul_add]
        · simp [hrest, ih]
      · simp [heq] at ih ⊢
        exact ih

/-- The singleton occupancy `{counts}` on the multinomial atom list has mass
equal to the closed multinomial term when `counts.sum = trials`, and mass
zero otherwise. -/
theorem eventMass_multinomialAtoms (trials : Nat)
    (weights counts : List Nat) :
    FiniteProbRecord.eventMass (multinomialAtoms trials weights)
        (FiniteProbRecord.singletonEvent counts) =
      if counts.sum = trials then multinomialWeight weights counts else 0 := by
  induction weights generalizing trials counts with
  | nil =>
      cases trials with
      | zero =>
          cases counts with
          | nil => simp [multinomialAtoms, multinomialWeight,
              FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
          | cons c cs =>
              simp [multinomialAtoms, multinomialWeight,
                FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
      | succ trials =>
          cases counts with
          | nil =>
              simp [multinomialAtoms, FiniteProbRecord.eventMass]
          | cons c cs =>
              simp [multinomialAtoms, multinomialWeight, FiniteProbRecord.eventMass]
  | cons weight rest ih =>
      unfold multinomialAtoms
      rw [eventMass_range]
      cases counts with
      | nil =>
          have hterm :
              natSum (trials + 1) (fun used =>
                  FiniteProbRecord.eventMass
                    ((multinomialAtoms (trials - used) rest).map fun atom =>
                      (used :: atom.1,
                        binom trials used * weight ^ used * atom.2))
                    (FiniteProbRecord.singletonEvent [])) =
                natSum (trials + 1) (fun _ => 0) := by
            apply natSum_congr
            intro used _
            have hmap :=
              eventMass_map_cons_nil used
                (binom trials used * weight ^ used)
                (multinomialAtoms (trials - used) rest)
            simpa using hmap
          rw [hterm, natSum_zero_fun]
          simp [multinomialWeight]
      | cons c cs =>
          have hterm :
              natSum (trials + 1) (fun used =>
                  FiniteProbRecord.eventMass
                    ((multinomialAtoms (trials - used) rest).map fun atom =>
                      (used :: atom.1,
                        binom trials used * weight ^ used * atom.2))
                    (FiniteProbRecord.singletonEvent (c :: cs))) =
                natSum (trials + 1) (fun used =>
                  if used = c then
                    binom trials used * weight ^ used *
                      FiniteProbRecord.eventMass
                        (multinomialAtoms (trials - used) rest)
                        (FiniteProbRecord.singletonEvent cs)
                  else 0) := by
            apply natSum_congr
            intro used _
            have hmap :=
              eventMass_map_cons_singleton used
                (binom trials used * weight ^ used) c cs
                (multinomialAtoms (trials - used) rest)
            simpa using hmap
          rw [hterm]
          by_cases hlt : c < trials + 1
          · have hspike :
                natSum (trials + 1) (fun used =>
                    if used = c then
                      binom trials used * weight ^ used *
                        FiniteProbRecord.eventMass
                          (multinomialAtoms (trials - used) rest)
                          (FiniteProbRecord.singletonEvent cs)
                    else 0) =
                  binom trials c * weight ^ c *
                    FiniteProbRecord.eventMass
                      (multinomialAtoms (trials - c) rest)
                      (FiniteProbRecord.singletonEvent cs) := by
              have hsp :=
                natSum_spike (trials + 1) c
                  (binom trials c * weight ^ c *
                    FiniteProbRecord.eventMass
                      (multinomialAtoms (trials - c) rest)
                      (FiniteProbRecord.singletonEvent cs))
                  (fun _ => 1)
              have hcongr :
                  natSum (trials + 1) (fun used =>
                      if used = c then
                        binom trials used * weight ^ used *
                          FiniteProbRecord.eventMass
                            (multinomialAtoms (trials - used) rest)
                            (FiniteProbRecord.singletonEvent cs)
                      else 0) =
                    natSum (trials + 1) (fun used =>
                      (if used = c then
                        binom trials c * weight ^ c *
                          FiniteProbRecord.eventMass
                            (multinomialAtoms (trials - c) rest)
                            (FiniteProbRecord.singletonEvent cs)
                      else 0) * 1) := by
                apply natSum_congr
                intro used _
                by_cases heq : used = c
                · simp [heq]
                · simp [heq]
              have hlt' : c < trials + 1 := hlt
              simpa [hcongr, hlt'] using hsp
            rw [hspike, ih (trials - c) cs]
            simp [multinomialWeight, List.sum_cons]
            by_cases hsum : cs.sum = trials - c
            · have hcancel : c + (trials - c) = trials :=
                Nat.add_sub_of_le (Nat.le_of_lt_succ hlt)
              simp [hsum, hcancel]
            · have htot : c + cs.sum ≠ trials := fun heq =>
                hsum (by
                  rw [← heq, Nat.add_comm, Nat.add_sub_cancel])
              simp [hsum, htot]
          · have hspike :
                natSum (trials + 1) (fun used =>
                    if used = c then
                      binom trials used * weight ^ used *
                        FiniteProbRecord.eventMass
                          (multinomialAtoms (trials - used) rest)
                          (FiniteProbRecord.singletonEvent cs)
                    else 0) =
                  0 := by
              have hsp :=
                natSum_spike (trials + 1) c 1 (fun used =>
                  binom trials used * weight ^ used *
                    FiniteProbRecord.eventMass
                      (multinomialAtoms (trials - used) rest)
                      (FiniteProbRecord.singletonEvent cs))
              have hcongr :
                  natSum (trials + 1) (fun used =>
                      if used = c then
                        binom trials used * weight ^ used *
                          FiniteProbRecord.eventMass
                            (multinomialAtoms (trials - used) rest)
                            (FiniteProbRecord.singletonEvent cs)
                      else 0) =
                    natSum (trials + 1) (fun used =>
                      (if used = c then 1 else 0) *
                        (binom trials used * weight ^ used *
                          FiniteProbRecord.eventMass
                            (multinomialAtoms (trials - used) rest)
                            (FiniteProbRecord.singletonEvent cs))) := by
                apply natSum_congr
                intro used _
                by_cases heq : used = c
                · simp [heq]
                · simp [heq]
              simpa [hcongr, hlt] using hsp
            rw [hspike]
            simp [multinomialWeight, List.sum_cons]
            have htot : c + cs.sum ≠ trials := by omega
            simp [htot]

/-- Multinomial distro on occupancy lists. -/
def multinomialDistro (trials : Nat) (weights : List Nat)
    (positive : 0 < weights.sum) : Distro (List Nat) where
  record :=
    let atoms := multinomialAtoms trials weights
    have hpos : 0 < FiniteProbRecord.totalMass atoms := by
      rw [totalMass_multinomialAtoms]
      exact Nat.pow_pos positive
    {
      atoms := atoms
      den := FiniteProbRecord.totalMass atoms
      den_pos := hpos
      total_mass := rfl
    }

theorem multinomial_den (trials : Nat) (weights : List Nat)
    (positive : 0 < weights.sum) :
    (multinomialDistro trials weights positive).record.den =
      weights.sum ^ trials := by
  simp [multinomialDistro, totalMass_multinomialAtoms]

theorem multinomial_pmf (trials : Nat) (weights counts : List Nat)
    (positive : 0 < weights.sum) :
    QProb.Equiv
      ((multinomialDistro trials weights positive).pmf counts)
      ⟨(if counts.sum = trials then multinomialWeight weights counts else 0),
        (multinomialDistro trials weights positive).record.den,
        (multinomialDistro trials weights positive).record.den_pos⟩ := by
  simp [Distro.pmf, multinomialDistro, FiniteProbRecord.probVal, QProb.Equiv,
    eventMass_multinomialAtoms]

end Distros
end Probability
end Thesis
