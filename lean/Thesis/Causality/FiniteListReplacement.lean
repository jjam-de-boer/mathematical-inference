import Std

namespace Thesis.Causality.FiniteListReplacement

/-!
# Constructive termination of finite list replacement

One item may be replaced by any finite list of items strictly smaller
under a supplied relation. List length and the sum of item ranks may
increase. The replacement relation is nevertheless well-founded whenever
the item relation is well-founded.

The proof uses nested accessibility induction: first on the head item,
then on the remaining list. Smaller children can be prepended one at a
time to an accessible tail. This proves the inductive `Acc` property
directly; no infinite bad sequence, choice principle, ordinal notation,
or equality decision on items is assumed.

The list order remains literal. A step replaces one item in its existing
context; arbitrary permutations are not reduction steps. Children may be
repeated or absent. This supplies a termination foundation, without a
search algorithm or an assumed bound on the number of replacements.
-/

variable {α : Type u} {smaller : α → α → Prop}

/-- The first list is the reduced list, matching the orientation expected
by `Acc` and `WellFounded`. The unchanged suffix is part of the constructor. -/
inductive Step (smaller : α → α → Prop) : List α → List α → Prop where
  | replace {parent : α} {children tail : List α}
      (each : ∀ child ∈ children, smaller child parent) :
      Step smaller (children ++ tail) (parent :: tail)
  | cons {head : α} {before after : List α} (step : Step smaller before after) :
      Step smaller (head :: before) (head :: after)

/-- Accessibility of a head item lifts to any already accessible tail.
Neither induction needs a decidability instance for the supplied relation. -/
theorem accessible_cons {head : α} (headAccessible : Acc smaller head) :
    ∀ tail, Acc (Step smaller) tail → Acc (Step smaller) (head :: tail) := by
  induction headAccessible with
  | intro head nextHeads headIH =>
      intro tail tailAccessible
      induction tailAccessible with
      | intro tail nextTails tailIH =>
          refine Acc.intro _ ?_
          intro reduced step
          cases step with
          | replace each =>
              have prepend : ∀ children : List α,
                  (∀ child ∈ children, smaller child head) → Acc (Step smaller) (children ++ tail) := by
                intro children
                induction children with
                | nil =>
                    intro _
                    exact Acc.intro tail nextTails
                | cons child rest ih =>
                    intro all
                    apply headIH child (all child List.mem_cons_self)
                    exact ih (fun item listed => all item (List.mem_cons_of_mem child listed))
              exact prepend _ each
          | cons inside => exact tailIH _ inside

/-- A finite list of accessible items is itself accessible for replacement. -/
theorem accessible (items : List α) (each : ∀ item ∈ items, Acc smaller item) :
    Acc (Step smaller) items := by
  induction items with
  | nil =>
      refine Acc.intro _ ?_
      intro reduced step
      cases step
  | cons head tail ih =>
      exact accessible_cons (each head List.mem_cons_self) tail
        (ih (fun item listed => each item (List.mem_cons_of_mem head listed)))

theorem wellFounded (base : WellFounded smaller) : WellFounded (Step smaller) :=
  ⟨fun items => accessible items (fun item _ => base.apply item)⟩

/-- A literal prefix and suffix can remain around the selected item.
This is the form needed by an update of one entry in a finite work list. -/
theorem replace_in_context (before after children : List α) (parent : α)
    (each : ∀ child ∈ children, smaller child parent) :
    Step smaller (before ++ children ++ after) (before ++ parent :: after) := by
  induction before with
  | nil => exact .replace each
  | cons head tail ih => exact .cons ih

end Thesis.Causality.FiniteListReplacement
