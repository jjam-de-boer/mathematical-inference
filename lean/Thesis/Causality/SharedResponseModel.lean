import Thesis.Causality.SharedResponseTables

namespace Thesis.Causality.SharedResponse

open Probability

/-!
# Realizing response-table laws with one actual shared root

Every rational law on the complete response-table carrier is allowed: there
is only one source factor, so no additional source-independence equations are
being discarded. The root may have arbitrarily many observed children. This
construction deliberately does not claim two-child semi-Markovian incidence.

Its observed projection has every bidirected edge between distinct nodes,
with the original directed signature unchanged. Consequently the response
law is a legitimate model for that projection, not for an arbitrary sparser
graph. Together with `lawOf`, the construction preserves all hard-intervention
events in both directions, including observational zeros and null actions.
-/

variable (S : ObservedSignature.{0})

def graph : ObservedGraph S where
  bidirected := fun first second => !(Nat.beq first.val second.val)
  bidirected_symmetric := by
    intro first second present
    simpa only [natBeq_comm second.val first.val] using present
  bidirected_irreflexive := by intro node; simp only [natBeq_refl, Bool.not_true]

def latent : LatentExtension S where
  count := 1
  Value := fun _ => Table S
  valueEnumeration := fun _ => enumeration S
  value_complete := fun _ => enumeration_complete S
  valueDecidableEq := fun _ => tableDecidableEq S
  incident := fun _ _ => true

def root : Fin (latent S).count := ⟨0, Nat.zero_lt_one⟩

/-- The input record is lifted literally, retaining its rational denominator
and all repeated or zero-weight occurrences. -/
def prior (law : FiniteProbRecord (Table S)) : FiniteProbRecord (latent S).Assignment :=
  law.map (fun table _ => table)

def model (law : FiniteProbRecord (Table S)) : ExactModel S where
  latent := latent S
  factor := fun _ => law
  prior := prior S law
  product_law := by
    intro events
    simpa [prior, latent, LatentExtension.rectangularEvent,
      FiniteProduct.rectangularEvent, FiniteProduct.qProduct,
      QProb.mul, QProb.one, QProb.Equiv] using
      (law.map_probVal (fun table _ => table) ((latent S).rectangularEvent events))
  mechanism := fun child parents inputs => lookup S (inputs (root S) rfl) child parents

theorem model_projectedGraph (law : FiniteProbRecord (Table S)) (first second : Fin S.count) :
    (model S law).observedGraph.bidirected first second = (graph S).bidirected first second := by
  simp only [FiniteLatentSCM.observedGraph, model, LatentExtension.observedGraph,
    LatentExtension.projectedBidirected, latent, graph, finAny,
    Bool.and_self, Bool.false_or, Bool.and_true]

/-- The native structural recursion reads the same stored response rows as
the finite table evaluator, at every root value and every parent configuration. -/
theorem model_evalNode (law : FiniteProbRecord (Table S))
    (target : (child : Fin S.count) → Option (S.Value child))
    (unit : (latent S).Assignment) (child : Fin S.count) :
    (model S law).evalNodeUnder target unit child = evalNode S target (unit (root S)) child := by
  rw [FiniteLatentSCM.evalNodeUnder, evalNode]
  unfold FiniteLatentSCM.equationUnder
  cases selected : target child with
  | some value => rfl
  | none =>
      change lookup S (unit (root S)) child _ = lookup S (unit (root S)) child _
      congr 1
      funext parent edge
      exact model_evalNode law target unit parent
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem model_eval (law : FiniteProbRecord (Table S))
    (target : (child : Fin S.count) → Option (S.Value child)) (unit : (latent S).Assignment) :
    (model S law).evalUnder target unit = eval S target (unit (root S)) := by
  funext child
  exact model_evalNode S law target unit child

theorem model_interventionalValue (law : FiniteProbRecord (Table S))
    (target : (child : Fin S.count) → Option (S.Value child)) (event : Event S.Assignment) :
    QProb.Equiv ((model S law).interventionalValue target event)
      (law.probVal (fun table => event (eval S target table))) :=
  QProb.equiv_trans ((model S law).interventionalValue_eq target event)
    (QProb.equiv_trans ((prior S law).probVal_congr _ _ (fun unit =>
      congrArg event (model_eval S law target unit))) (law.map_probVal _ _))

/-- This law-to-model-to-event bridge preserves every original causal query.
The reconstructed model has the complete bidirected projection above; do not
use this theorem to assert membership in the original model's sparser graph. -/
theorem model_lawOf_interventionalValue (original : ExactModel S)
    (target : (child : Fin S.count) → Option (S.Value child)) (event : Event S.Assignment) :
    QProb.Equiv ((model S (lawOf S original)).interventionalValue target event)
      (original.interventionalValue target event) :=
  QProb.equiv_trans (model_interventionalValue S _ target event)
    (lawOf_interventionalValue S original target event)

end Thesis.Causality.SharedResponse
