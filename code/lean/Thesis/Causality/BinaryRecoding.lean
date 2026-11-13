import Thesis.Causality.BinaryEncoding
import Thesis.Probability.FiniteBooleanTranslation

namespace Thesis
namespace Causality
namespace BinaryRecoding

open Probability

/-!
# Explicit coordinate recodings of an ordinary Boolean SCM

A separating conditional cell may use either Boolean value at each observed
coordinate.  Before embedding it in a larger alphabet, flip the coordinates
explicitly so that this cell uses bit one.  Bit one can then be represented
by a single distinguished label, which the private label refinement always
keeps.  The larger bit-zero fibres need not be conditioned on or averaged.

Recoding is an actual mechanism transformation.  Each declared parent is
decoded with its own supplied coordinate flip before the old mechanism is
called, and the child's result is encoded with the child's flip.  Latent
coordinates, incidence, factors and the independent prior are unchanged.
Hard interventions are decoded by the same explicit involution, including
all additional action nodes.  The evaluation proof covers responding
descendants; it does not assume that mechanisms ignore the flipped bits.

The mask is Type-level data, not a chosen permutation.  Whole observational
equality and full Boolean positivity are transported through the same
invertible assignment map.  These are algebraic SCM transports, independent
of do-calculus soundness and of any hedge countermodel construction.
-/

variable {S : ObservedSignature.{0}}

/-- Flip the supplied coordinates of a complete Boolean assignment. -/
def assignment (mask sample : S.binary.Assignment) : S.binary.Assignment :=
  FiniteProduct.xorAssignment S.count sample mask

theorem assignment_involutive (mask sample : S.binary.Assignment) :
    assignment mask (assignment mask sample) = sample :=
  FiniteProduct.xorAssignment_involutive S.count mask sample

/-- Decode every actually forced Boolean value with its coordinate flip. -/
def intervention (mask : S.binary.Assignment) (target : Fin S.count -> Option Bool) :
    Fin S.count -> Option Bool :=
  fun node => (target node).map (fun value => Bool.xor value (mask node))

/-- Change only the observed label presentation of the supplied SCM.
The same declared parents and incident latent inputs feed the old response. -/
def model (mask : S.binary.Assignment) (base : ExactModel S.binary) : ExactModel S.binary where
  latent := base.latent
  factor := base.factor
  prior := base.prior
  product_law := base.product_law
  mechanism := fun child parents inputs => Bool.xor
    (base.mechanism child (fun parent edge => Bool.xor (parents parent edge) (mask parent)) inputs)
    (mask child)

/-- Recoding does not alter canonical latent incidence or the projected
graph.  Neither an observed nor a bidirected edge is added by a label flip. -/
theorem compatible (mask : S.binary.Assignment) (base : ExactModel S.binary)
    {graph : ObservedGraph S} (member : Compatible base graph.binary) :
    Compatible (model mask base) graph.binary :=
  ⟨member.1, member.2⟩

/-- Every actual response under the supplied intervention is the recoding
of the old response under its decoded intervention.  At a forced row the
two flips cancel; at a free row the recursive parent identities discharge
the old mechanism's actual declared inputs. -/
theorem evalNodeUnder (mask : S.binary.Assignment) (base : ExactModel S.binary)
    (target : Fin S.count -> Option Bool) (unit : base.latent.Assignment) (child : Fin S.count) :
    (model mask base).evalNodeUnder target unit child =
      Bool.xor (base.evalNodeUnder (intervention mask target) unit child) (mask child) := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  cases forced : target child with
  | some value =>
      simp only [FiniteLatentSCM.equationUnder, intervention, forced, Option.map_some]
      cases value <;> cases mask child <;> rfl
  | none =>
      simp only [FiniteLatentSCM.equationUnder, intervention, forced, Option.map_none, model]
      apply congrArg (fun parents => Bool.xor (base.mechanism child parents (fun root _incident => unit root))
        (mask child))
      funext parent edge
      change Bool.xor ((model mask base).evalNodeUnder target unit parent) (mask parent) = _
      rw [evalNodeUnder mask base target unit parent]
      cases base.evalNodeUnder (intervention mask target) unit parent <;> cases mask parent <;> rfl
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem evalUnder (mask : S.binary.Assignment) (base : ExactModel S.binary)
    (target : Fin S.count -> Option Bool) (unit : base.latent.Assignment) :
    (model mask base).evalUnder target unit = assignment mask (base.evalUnder (intervention mask target) unit) :=
  funext (evalNodeUnder mask base target unit)

/-- Whole interventional events, not only one-coordinate probabilities,
are transported through the literal recoding map on the unchanged prior. -/
theorem interventionalValue (mask : S.binary.Assignment) (base : ExactModel S.binary)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) :
    QProb.Equiv ((model mask base).interventionalValue target event)
      (base.interventionalValue (intervention mask target) (fun sample => event (assignment mask sample))) :=
  QProb.equiv_trans ((model mask base).interventionalValue_eq target event)
    (QProb.equiv_trans (base.prior.probVal_congr _ _
      (fun unit => congrArg event (evalUnder mask base target unit)))
      (QProb.equiv_symm (base.interventionalValue_eq _ _)))

/-- No-intervention specialization.  Every empty target remains empty
after decoding, so the factual branch is the same literal SCM evaluation. -/
theorem observationalValue (mask : S.binary.Assignment) (base : ExactModel S.binary)
    (event : Event S.binary.Assignment) :
    QProb.Equiv ((model mask base).observationalValue event)
      (base.observationalValue (fun sample => event (assignment mask sample))) := by
  have empty : intervention mask (FiniteLatentSCM.noIntervention S.binary) =
      FiniteLatentSCM.noIntervention S.binary := by
    funext node
    rfl
  simpa only [empty] using interventionalValue mask base (FiniteLatentSCM.noIntervention S.binary) event

theorem observationally_equivalent (mask : S.binary.Assignment) (left right : ExactModel S.binary)
    (equivalent : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (model mask left) (model mask right) := by
  intro event
  exact QProb.equiv_trans (observationalValue mask left event)
    (QProb.equiv_trans (equivalent (fun sample => event (assignment mask sample)))
      (QProb.equiv_symm (observationalValue mask right event)))

/-- Every recoded Boolean cell is positive because its explicit inverse
cell was positive in the original model.  The inverse is supplied by the
same mask, rather than extracted from propositional surjectivity. -/
theorem positive (mask : S.binary.Assignment) (base : ExactModel S.binary)
    (supported : ObservationallyPositive base) : ObservationallyPositive (model mask base) := by
  intro reference
  have inverse (sample : S.binary.Assignment) :
      assignment mask sample = reference ↔ sample = assignment mask reference := by
    constructor
    · intro same
      exact (assignment_involutive mask sample).symm.trans (congrArg (assignment mask) same)
    · intro same
      exact (congrArg (assignment mask) same).trans (assignment_involutive mask reference)
  have events := base.observationalDist.probVal_congr
    (fun sample => FiniteProbRecord.singletonEvent reference (assignment mask sample))
    (FiniteProbRecord.singletonEvent (assignment mask reference))
    (fun sample => by
      apply Bool.eq_iff_iff.mpr
      simpa only [FiniteProbRecord.singletonEvent, decide_eq_true_eq] using inverse sample)
  exact (QProb.equiv_num_pos_iff (QProb.equiv_trans
    (observationalValue mask base (FiniteProbRecord.singletonEvent reference)) events)).mpr
      (supported (assignment mask reference))

end BinaryRecoding
end Causality
end Thesis
