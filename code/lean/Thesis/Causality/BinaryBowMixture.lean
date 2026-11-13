import Thesis.Causality.BinaryBowEndpoints

namespace Thesis
namespace Causality
namespace BinaryBow

open Probability

/-!
# A graph-compatible rational mixture of the bow endpoints

The endpoint switch is now an independently sampled Boolean component of
the *same shared root*.  This retains the bow incidence: no new observed
parent, correlated private source, or enlarged graphical model class is
introduced.  The factual pair is still distributed according to the supplied
law and the switch is used only when the current treatment differs from its
factual value.  It therefore cannot change any observed event probability.

The actual intervention probability is `lower + outside * P(switch=true)`.
This affine identity follows from disjoint-event additivity and the real
independent product record.  It is not inferred by averaging two unrelated
SCM outputs.  Rational arithmetic will subsequently choose the switch law
to realize any supplied rational value between the sharp endpoints.
-/

/-- The factual pair and off-factual switch share one finite hidden root. -/
def mixtureLatent : LatentExtension signature where
  count := 1
  Value := fun _ => signature.Assignment × Bool
  valueEnumeration := fun _ => signature.assignmentEnumeration.flatMap
    (fun factual => [(factual, false), (factual, true)])
  value_complete := by
    intro _ seed
    rcases seed with ⟨factual, switch⟩
    apply List.mem_flatMap_of_mem (signature.assignmentEnumeration_complete factual)
    cases switch <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun _ _ => true

def mixtureRoot : Fin mixtureLatent.count := ⟨0, by decide⟩

def mixturePrior (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) :
    FiniteProbRecord mixtureLatent.Assignment :=
  (law.product switch).map (fun seed _ => seed)

/-- An actual finite SCM; source normalization and independence are proved
for the product of the supplied records, including biased or degenerate coins. -/
def mixtureModel (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) :
    ExactModel signature where
  latent := mixtureLatent
  factor := fun _ => law.product switch
  prior := mixturePrior law switch
  product_law := by
    intro events
    simpa [mixturePrior, mixtureLatent, LatentExtension.rectangularEvent,
      FiniteProduct.rectangularEvent, FiniteProduct.qProduct,
      QProb.mul, QProb.one, QProb.Equiv] using
      ((law.product switch).map_probVal (fun seed _ => seed) (mixtureLatent.rectangularEvent events))
  mechanism := fun child parents inputs =>
    let seed := inputs mixtureRoot rfl
    if atX : child.val = 0 then seed.1 x
    else
      let atY : child.val = 1 := by
        have bounded : child.val < 2 := child.isLt
        omega
      if parents x (by simp [signature, x, atY]) = seed.1 x then seed.1 y else seed.2

theorem mixture_isCanonical (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) :
    (mixtureModel law switch).IsCanonicalSemiMarkovian := by
  change mixtureLatent.CanonicalSemiMarkovian
  intro _source first second third _firstIncident _secondIncident _thirdIncident
  rcases node_cases first with same | same <;> subst first <;>
    rcases node_cases second with same | same <;> subst second <;>
    rcases node_cases third with same | same <;> subst third <;> simp

theorem mixture_hasProjectedGraph (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool) :
    HasProjectedGraph (mixtureModel law switch) graph := by
  intro first second
  simp only [FiniteLatentSCM.observedGraph, mixtureModel,
    LatentExtension.observedGraph, LatentExtension.projectedBidirected,
    mixtureLatent, graph, finAny, Bool.and_self, Bool.false_or, Bool.and_true]

theorem mixture_eval_x (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool)
    (target : (node : Fin signature.count) → Option (signature.Value node))
    (unit : mixtureLatent.Assignment) :
    (mixtureModel law switch).evalUnder target unit x = (target x).getD ((unit mixtureRoot).1 x) := by
  change (mixtureModel law switch).evalNodeUnder target unit x = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases target x <;> rfl

theorem mixture_eval_y (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool)
    (target : (node : Fin signature.count) → Option (signature.Value node))
    (unit : mixtureLatent.Assignment) :
    (mixtureModel law switch).evalUnder target unit y =
      match target y with
      | some value => value
      | none => if (mixtureModel law switch).evalUnder target unit x = (unit mixtureRoot).1 x
          then (unit mixtureRoot).1 y else (unit mixtureRoot).2 := by
  change (mixtureModel law switch).evalNodeUnder target unit y = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  cases target y <;> rfl

/-- Factual output is the stored pair for every switch label, even labels
with zero weight.  Thus the switch cannot alter the observed law. -/
theorem mixture_eval_factual (law : FiniteProbRecord signature.Assignment) (switch : FiniteProbRecord Bool)
    (unit : mixtureLatent.Assignment) :
    (mixtureModel law switch).eval unit = (unit mixtureRoot).1 := by
  funext node
  rcases node_cases node with same | same
  · subst node
    simp only [FiniteLatentSCM.eval, mixture_eval_x, FiniteLatentSCM.noIntervention, Option.getD_none]
  · subst node
    simp [FiniteLatentSCM.eval, mixture_eval_y, mixture_eval_x, FiniteLatentSCM.noIntervention]

private theorem product_factual_probVal (law : FiniteProbRecord signature.Assignment)
    (switch : FiniteProbRecord Bool) (event : Event signature.Assignment) :
    QProb.Equiv ((law.product switch).probVal (fun seed => event seed.1)) (law.probVal event) := by
  have rectangle := law.product_probVal switch event topEvent
  simp only [topEvent, Bool.and_true] at rectangle
  exact QProb.equiv_trans rectangle
    (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) switch.normalization) (QProb.mul_one _))

/-- Whole observed-law preservation integrates out the actual independent
switch record; its support or denominator need not match the factual law. -/
theorem mixture_observationalValue_preserved (law : FiniteProbRecord signature.Assignment)
    (switch : FiniteProbRecord Bool) (event : Event signature.Assignment) :
    QProb.Equiv ((mixtureModel law switch).observationalValue event) (law.probVal event) :=
  QProb.equiv_trans ((mixtureModel law switch).observationalValue_eq event)
    (QProb.equiv_trans
      ((law.product switch).map_probVal (fun seed _ => seed)
        (fun unit => event ((mixtureModel law switch).eval unit)))
      (QProb.equiv_trans
        ((law.product switch).probVal_congr _ _ (fun seed =>
          congrArg event (mixture_eval_factual law switch (fun _ => seed))))
        (product_factual_probVal law switch event)))

theorem mixture_eval_intervened_y (law : FiniteProbRecord signature.Assignment)
    (switch : FiniteProbRecord Bool) (action : Bool) (unit : mixtureLatent.Assignment) :
    (mixtureModel law switch).evalUnder (intervention action).value unit y =
      if action = (unit mixtureRoot).1 x then (unit mixtureRoot).1 y else (unit mixtureRoot).2 := by
  rw [mixture_eval_y, mixture_eval_x]
  simp [intervention, x, y] <;> rfl

private theorem switch_outcome (action factualX factualY switch : Bool) :
    (if action = factualX then factualY else switch) =
      ((decide (factualX = action) && factualY) || (!decide (factualX = action) && switch)) := by
  cases action <;> cases factualX <;> cases factualY <;> cases switch <;> rfl

/-- The exact affine response law.  Factual and off-factual contributions
are disjoint; the latter is a rectangle in the supplied independent product. -/
theorem mixture_interventionalValue (law : FiniteProbRecord signature.Assignment)
    (switch : FiniteProbRecord Bool) (action : Bool) :
    QProb.Equiv
      ((mixtureModel law switch).interventionalValue (intervention action).value (fun sample => sample y))
      (QProb.add (lower law action) (QProb.mul (outside law action) (switch.probVal id))) := by
  let first : Event (signature.Assignment × Bool) := fun seed => lowerEvent action seed.1
  let second : Event (signature.Assignment × Bool) := fun seed => outsideEvent action seed.1 && seed.2
  have units : QProb.Equiv
      ((mixtureModel law switch).interventionalValue (intervention action).value (fun sample => sample y))
      ((law.product switch).probVal (union first second)) :=
    QProb.equiv_trans ((mixtureModel law switch).interventionalValue_eq (intervention action).value _)
      (QProb.equiv_trans
        ((law.product switch).map_probVal (fun seed _ => seed)
          (fun unit => (mixtureModel law switch).evalUnder (intervention action).value unit y))
        ((law.product switch).probVal_congr _ _ (fun seed =>
          (mixture_eval_intervened_y law switch action (fun _ => seed)).trans
            (switch_outcome action (seed.1 x) (seed.1 y) seed.2))))
  have disjointParts : disjoint first second := by
    intro seed selected excluded
    have inside := (Bool.and_eq_true_iff.mp selected).1
    have outsideTrue := (Bool.and_eq_true_iff.mp excluded).1
    simp only [outsideEvent, inside, Bool.not_true, Bool.false_eq_true] at outsideTrue
  exact QProb.equiv_trans units
    (QProb.equiv_trans ((law.product switch).probVal_union_disjoint first second disjointParts)
      (QProb.add_congr (product_factual_probVal law switch (lowerEvent action))
        (law.product_probVal switch (outsideEvent action) id)))

end BinaryBow
end Causality
end Thesis
