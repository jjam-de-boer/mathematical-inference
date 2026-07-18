import Thesis.Probability

namespace Thesis

open Probability

/-!
This file formalizes the small correspondence core used in the thesis.

It does not reprove Pearl's identification theorems.  It represents the
finite recursive fragment in which a classical SCM and the MLTT-style SCM
have the same computational data, and proves that the encoding preserves the
operations needed before invoking the published completeness results.
-/

/--
Finite recursive SCM data with homogeneous endogenous value type `A`.

The natural-language proof in the thesis allows a finite family of value
types.  This Lean core keeps all endogenous variables in one finite value
type so that the recursion and intervention lemmas stay small and checkable.
The structural function for variable `i` receives the already computed prefix
of endogenous values, the exogenous assignment, and returns the next value.
-/
structure RecursiveSCMData (A : Type u) (U : Type v) where
  n : Nat
  noise : FiniteProbRecord U
  fn : (i : Fin n) → List A → U → A

abbrev ClassicSCM (A : Type u) (U : Type v) := RecursiveSCMData A U

abbrev MLTTSCM (A : Type u) (U : Type v) := RecursiveSCMData A U

namespace RecursiveSCMData

def evalPrefix (M : RecursiveSCMData A U) (u : U) :
    (k : Nat) → k ≤ M.n → List A
  | 0, _ => []
  | k + 1, h =>
      let prev := evalPrefix M u k (Nat.le_of_succ_le h)
      prev ++ [M.fn ⟨k, Nat.lt_of_succ_le h⟩ prev u]

def eval (M : RecursiveSCMData A U) (u : U) : List A :=
  evalPrefix M u M.n (Nat.le_refl M.n)

def intervene (M : RecursiveSCMData A U)
    (target : Fin M.n → Option A) : RecursiveSCMData A U where
  n := M.n
  noise := M.noise
  fn := fun i pref u =>
    match target i with
    | some x => x
    | none => M.fn i pref u

def observationalDist (M : RecursiveSCMData A U) : FiniteProbRecord (List A) :=
  M.noise.map M.eval

def observationalProb (M : RecursiveSCMData A U)
    (event : List A → Bool) : Rat :=
  M.observationalDist.probRat event

def interventionalProb (M : RecursiveSCMData A U)
    (target : Fin M.n → Option A) (event : List A → Bool) : Rat :=
  (M.intervene target).observationalProb event

def counterfactualProb (M : RecursiveSCMData A U)
    (evidence : List A → Bool) (_hEvidence : 0 < M.observationalProb evidence)
    (target : Fin M.n → Option A) (event : List A → Bool) : Rat :=
  let posterior := M.noise.condition (fun u => evidence (M.eval u)) (by
    simpa [observationalProb, observationalDist,
      FiniteProbRecord.map_probRat] using _hEvidence)
  posterior.probRat (fun u => event ((M.intervene target).eval u))

theorem counterfactualProb_eq (M : RecursiveSCMData A U)
    (evidence : List A → Bool) (hEvidence : 0 < M.observationalProb evidence)
    (target : Fin M.n → Option A) (event : List A → Bool) :
    M.counterfactualProb evidence hEvidence target event =
      M.noise.probRat
        (fun u => evidence (M.eval u) && event ((M.intervene target).eval u)) /
      M.noise.probRat (fun u => evidence (M.eval u)) := by
  simp [counterfactualProb, FiniteProbRecord.condition_probRat]

end RecursiveSCMData

namespace FiniteFunctionalisation

/-!
A small checked core of the finite CBN-to-SCM functionalisation argument.

The mathematical appendix treats arbitrary finite rational conditional
probability tables.  Here we check the local binary row construction: a finite
uniform tagged seed type with `trueCells` cells mapped to `true` and
`falseCells` cells mapped to `false` realizes the rational row
`trueCells / (trueCells + falseCells)`.
-/

structure BinaryCPTRow where
  trueCells : Nat
  falseCells : Nat
  positive : 0 < trueCells + falseCells

namespace BinaryCPTRow

abbrev Seed (row : BinaryCPTRow) : Type :=
  Fin row.trueCells ⊕ Fin row.falseCells

def seedSupport (row : BinaryCPTRow) : List row.Seed :=
  (List.ofFn (fun i : Fin row.trueCells => (Sum.inl i : row.Seed))) ++
    (List.ofFn (fun i : Fin row.falseCells => (Sum.inr i : row.Seed)))

def rowFn (row : BinaryCPTRow) : row.Seed → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

def probTrue (row : BinaryCPTRow) : Rat :=
  (row.seedSupport.countP (fun seedCell => row.rowFn seedCell) : Rat) /
    (row.seedSupport.length : Rat)

def probFalse (row : BinaryCPTRow) : Rat :=
  (row.seedSupport.countP (fun seedCell => !row.rowFn seedCell) : Rat) /
    (row.seedSupport.length : Rat)

theorem seedSupport_length (row : BinaryCPTRow) :
    row.seedSupport.length = row.trueCells + row.falseCells := by
  simp [seedSupport]

theorem seedSupport_nonempty (row : BinaryCPTRow) :
    0 < row.seedSupport.length := by
  simpa [seedSupport_length] using row.positive

theorem true_seed_count (row : BinaryCPTRow) :
    row.seedSupport.countP (fun seedCell => row.rowFn seedCell) =
      row.trueCells := by
  let trueSupport : List row.Seed :=
    List.ofFn (fun i : Fin row.trueCells => (Sum.inl i : row.Seed))
  let falseSupport : List row.Seed :=
    List.ofFn (fun i : Fin row.falseCells => (Sum.inr i : row.Seed))
  have hTrue :
      trueSupport.countP (fun seedCell => row.rowFn seedCell) =
        row.trueCells := by
    calc
      trueSupport.countP (fun seedCell => row.rowFn seedCell) =
          trueSupport.length := by
            exact (List.countP_eq_length).2 (by
              intro seedCell hmem
              simp [trueSupport] at hmem
              rcases hmem with ⟨_, rfl⟩
              rfl)
      _ = row.trueCells := by
            simp [trueSupport]
  have hFalse :
      falseSupport.countP (fun seedCell => row.rowFn seedCell) = 0 := by
    exact (List.countP_eq_zero).2 (by
      intro seedCell hmem
      simp [falseSupport] at hmem
      rcases hmem with ⟨_, rfl⟩
      simp [rowFn])
  simp [seedSupport, trueSupport, falseSupport, hTrue, hFalse]

theorem false_seed_count (row : BinaryCPTRow) :
    row.seedSupport.countP (fun seedCell => !row.rowFn seedCell) =
      row.falseCells := by
  let trueSupport : List row.Seed :=
    List.ofFn (fun i : Fin row.trueCells => (Sum.inl i : row.Seed))
  let falseSupport : List row.Seed :=
    List.ofFn (fun i : Fin row.falseCells => (Sum.inr i : row.Seed))
  have hTrue :
      trueSupport.countP (fun seedCell => !row.rowFn seedCell) = 0 := by
    exact (List.countP_eq_zero).2 (by
      intro seedCell hmem
      simp [trueSupport] at hmem
      rcases hmem with ⟨_, rfl⟩
      simp [rowFn])
  have hFalse :
      falseSupport.countP (fun seedCell => !row.rowFn seedCell) =
        row.falseCells := by
    calc
      falseSupport.countP (fun seedCell => !row.rowFn seedCell) =
          falseSupport.length := by
            exact (List.countP_eq_length).2 (by
              intro seedCell hmem
              simp [falseSupport] at hmem
              rcases hmem with ⟨_, rfl⟩
              rfl)
      _ = row.falseCells := by
            simp [falseSupport]
  simp [seedSupport, trueSupport, falseSupport, hTrue, hFalse]

theorem probTrue_eq (row : BinaryCPTRow) :
    row.probTrue =
      (row.trueCells : Rat) / ((row.trueCells + row.falseCells : Nat) : Rat) := by
  simp [probTrue, true_seed_count, seedSupport_length]

theorem probFalse_eq (row : BinaryCPTRow) :
    row.probFalse =
      (row.falseCells : Rat) / ((row.trueCells + row.falseCells : Nat) : Rat) := by
  simp [probFalse, false_seed_count, seedSupport_length]

def oneVariableSCM (row : BinaryCPTRow) : RecursiveSCMData Bool row.Seed where
  n := 1
  noise := FiniteProbRecord.ofUrn
    (UrnProb.ofList row.seedSupport row.seedSupport_nonempty)
  fn := fun _ _ seedCell => row.rowFn seedCell

theorem oneVariableSCM_eval (row : BinaryCPTRow) (seedCell : row.Seed) :
    (row.oneVariableSCM.eval seedCell) = [row.rowFn seedCell] := by
  rfl

end BinaryCPTRow

end FiniteFunctionalisation

namespace TenureTrack

/-!
A checked version of the running tenure-track SCM calculation from the thesis.

The example is intentionally small and concrete: all endogenous variables are
Boolean and appear in the order
`Pr, Qu, Top, Com, Fit, Short, Fund, Off`.
-/

structure Noise where
  background : Bool
  prestige : Bool
  quality : Bool
  topic : Bool
  committee : Bool
  funding : Bool
  deriving DecidableEq, Repr

def bools : List Bool := [false, true]

def support : List Noise :=
  bools.flatMap fun background =>
  bools.flatMap fun prestige =>
  bools.flatMap fun quality =>
  bools.flatMap fun topic =>
  bools.flatMap fun committee =>
  bools.map fun funding =>
    { background, prestige, quality, topic, committee, funding }

def bernoulliWeight (trueWeight falseWeight : Nat) : Bool → Nat
  | true => trueWeight
  | false => falseWeight

def weight (u : Noise) : Nat :=
  bernoulliWeight 1 2 u.background *
  bernoulliWeight 1 3 u.prestige *
  bernoulliWeight 1 3 u.quality *
  bernoulliWeight 1 1 u.topic *
  bernoulliWeight 1 1 u.committee *
  bernoulliWeight 1 3 u.funding

def noiseDist : FiniteProbRecord Noise where
  atoms := support.map (fun u => (u, weight u))
  den := 768
  den_pos := by native_decide
  total_mass := by native_decide

def prior (xs : List Bool) (i : Nat) : Bool :=
  xs.getD i false

def model : RecursiveSCMData Bool Noise where
  n := 8
  noise := noiseDist
  fn := fun i xs u =>
    match i.val with
    | 0 => u.background || u.prestige
    | 1 => u.background || u.quality
    | 2 => u.topic
    | 3 => u.committee
    | 4 => prior xs 2 && prior xs 3
    | 5 => prior xs 1 && (prior xs 0 || prior xs 4)
    | 6 => prior xs 2 || u.funding
    | _ => prior xs 5 && prior xs 6

def prEvent : List Bool → Bool :=
  fun xs => prior xs 0

def quEvent : List Bool → Bool :=
  fun xs => prior xs 1

def fitEvent : List Bool → Bool :=
  fun xs => prior xs 4

def offEvent : List Bool → Bool :=
  fun xs => prior xs 7

def prAndQuEvent : List Bool → Bool :=
  fun xs => prEvent xs && quEvent xs

def fitAndOffEvent : List Bool → Bool :=
  fun xs => fitEvent xs && offEvent xs

def noPrestigeGoodNoOfferEvent : List Bool → Bool :=
  fun xs => (!prEvent xs) && quEvent xs && (!offEvent xs)

def setPrTrue (i : Fin model.n) : Option Bool :=
  if i.val = 0 then some true else none

def setFitTrue (i : Fin model.n) : Option Bool :=
  if i.val = 4 then some true else none

theorem prob_pr_true :
    model.observationalProb prEvent = (1 / 2 : Rat) := by
  native_decide

theorem prob_qu_true :
    model.observationalProb quEvent = (1 / 2 : Rat) := by
  native_decide

theorem prob_pr_and_qu_true :
    model.observationalProb prAndQuEvent = (3 / 8 : Rat) := by
  native_decide

theorem prob_qu_given_pr :
    model.observationalProb prAndQuEvent / model.observationalProb prEvent =
      (3 / 4 : Rat) := by
  native_decide

theorem prob_qu_do_pr_true :
    model.interventionalProb setPrTrue quEvent = (1 / 2 : Rat) := by
  native_decide

theorem prob_off_given_fit :
    model.observationalProb fitAndOffEvent / model.observationalProb fitEvent =
      (1 / 2 : Rat) := by
  native_decide

theorem prob_off_do_fit_true :
    model.interventionalProb setFitTrue offEvent = (5 / 16 : Rat) := by
  native_decide

theorem prob_noPrestigeGoodNoOffer :
    model.observationalProb noPrestigeGoodNoOfferEvent = (3 / 32 : Rat) := by
  native_decide

theorem prob_noPrestigeGoodNoOffer_positive :
    0 < model.observationalProb noPrestigeGoodNoOfferEvent := by
  native_decide

def posteriorNoPrestigeGoodNoOffer : FiniteProbRecord Noise :=
  model.noise.condition
    (fun u => noPrestigeGoodNoOfferEvent (model.eval u))
    (by
      simpa [RecursiveSCMData.observationalProb,
        RecursiveSCMData.observationalDist,
        FiniteProbRecord.map_probRat] using
        prob_noPrestigeGoodNoOffer_positive)

theorem posterior_noPrestigeGoodNoOffer_normalized :
    QProb.Equiv
      (posteriorNoPrestigeGoodNoOffer.probVal topEvent) QProb.one := by
  exact posteriorNoPrestigeGoodNoOffer.normalization

theorem prob_counterfactual_offer_do_pr_given_noPrestigeGoodNoOffer :
    model.counterfactualProb noPrestigeGoodNoOfferEvent
      prob_noPrestigeGoodNoOffer_positive setPrTrue offEvent =
      (1 / 2 : Rat) := by
  native_decide

theorem prob_counterfactual_offer_do_fit_given_noPrestigeGoodNoOffer :
    model.counterfactualProb noPrestigeGoodNoOfferEvent
      prob_noPrestigeGoodNoOffer_positive setFitTrue offEvent =
      (1 / 2 : Rat) := by
  native_decide

end TenureTrack

namespace SCMCorrespondence

def encode (M : ClassicSCM A U) : MLTTSCM A U := M

def decode (M : MLTTSCM A U) : ClassicSCM A U := M

theorem decode_encode (M : ClassicSCM A U) :
    decode (encode M) = M := by
  rfl

theorem encode_decode (M : MLTTSCM A U) :
    encode (decode M) = M := by
  rfl

theorem encode_eval (M : ClassicSCM A U) (u : U) :
    (encode M).eval u = M.eval u := by
  rfl

theorem encode_intervene (M : ClassicSCM A U)
    (target : Fin M.n → Option A) :
    encode (M.intervene target) = (encode M).intervene target := by
  rfl

theorem encode_observationalProb (M : ClassicSCM A U)
    (event : List A → Bool) :
    (encode M).observationalProb event = M.observationalProb event := by
  rfl

theorem encode_interventionalProb (M : ClassicSCM A U)
    (target : Fin M.n → Option A) (event : List A → Bool) :
    (encode M).interventionalProb target event =
      M.interventionalProb target event := by
  rfl

/--
Abstract transport of a published classical completeness theorem.

The thesis uses this shape with:
* `classIdent` = classical identifiability,
* `classDeriv` = classical do-calculus derivability,
* `mlttIdent` = identifiability in the encoded MLTT fragment,
* `mlttDeriv` = MLTT derivability.

The published theorem supplies `classicalComplete`; the correspondence proof
supplies `reflectIdent` and `transportDeriv`.
-/
theorem completeness_transport
    {ClassicalQuery : Type u} {MLTTQuery : Type v}
    (encQ : ClassicalQuery → MLTTQuery)
    (classIdent : ClassicalQuery → Prop)
    (classDeriv : ClassicalQuery → Prop)
    (mlttIdent : MLTTQuery → Prop)
    (mlttDeriv : MLTTQuery → Prop)
    (reflectIdent :
      ∀ q, mlttIdent (encQ q) → classIdent q)
    (transportDeriv :
      ∀ q, classDeriv q → mlttDeriv (encQ q))
    (classicalComplete :
      ∀ q, classIdent q → classDeriv q) :
    ∀ q, mlttIdent (encQ q) → mlttDeriv (encQ q) := by
  intro q h
  exact transportDeriv q (classicalComplete q (reflectIdent q h))

end SCMCorrespondence

end Thesis
