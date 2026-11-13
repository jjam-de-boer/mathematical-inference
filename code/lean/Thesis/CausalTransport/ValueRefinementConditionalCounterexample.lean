import Thesis.Causality.ValueRefinementConditional
import Thesis.Causality.ConditionalCounterexampleWitness

namespace Thesis
namespace Causality
namespace ObservedValueRefinement

open Probability

/-!
# Full-alphabet positive conditional countermodels from Boolean ones

`ValueRefinementConditional` preserves the actual numerator, denominator,
support and value of an arbitrary supplied Boolean source cell in its own
recoded, encoded and label-refined SCM.  This module builds both final models
first, then uses that same per-model transport to retain the conditional
gap.  The two conditioning masses may differ throughout.

The cell-level constructor accepts an actual source reference and its kernel
gap, which is useful when a channel expansion has already proved the gap at
that reference.  The general constructor accepts any positive Boolean
conditional counterexample and derives such a cell by the existing finite
search.  No source assignment or positive noise parameter is selected from
a propositional existence statement.

Compatibility, full-original-alphabet positivity, complete observational
equality and original-query conditional separation all concern the same two
final SCMs.  Original value domains, node sets, interventions and projected
edges are unchanged.  The private label sweep restores every original label;
it does not append observed nodes or share a new latent switch.  These are
general countermodel transports, not assumptions that a separating Boolean
countermodel exists at every irreducible conditional terminal.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}

/-- Lift a genuinely separated supported Boolean cell to the unchanged
full-alphabet positive class.  The explicit reference fixes the coordinate
recoding and recovers the same source intervention.  Denominator equality
between the two source models is neither required nor manufactured. -/
noncomputable def positiveConditionalCounterexampleOfBinaryCell
    (query : ConditionalKernelQuery S) (rich : ObservedSignature.ValueRich S)
    (left right : ExactModel S.binary)
    (leftCompatible : Compatible left graph.binary) (rightCompatible : Compatible right graph.binary)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (equivalent : ObservationallyEquivalent left right) (reference : S.binary.Assignment)
    (separated : Not (Nonempty (ProbabilityResult.Equivalent
      (query.binary.sourceTerm.denote left reference) (query.binary.sourceTerm.denote right reference)))) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  let mask := cellMask reference
  let recodedLeft := BinaryRecoding.model mask left
  let recodedRight := BinaryRecoding.model mask right
  have leftMember : (GraphModelClass.positive graph).Mem (cellModel rich left reference) := ⟨
    refine_compatible rich (BinaryEncoding.model rich recodedLeft)
      (BinaryEncoding.compatible rich recodedLeft (BinaryRecoding.compatible mask left leftCompatible)),
    refine_positive rich (BinaryEncoding.model rich recodedLeft)
      (BinaryEncoding.respectsParentBits rich recodedLeft)
      (BinaryEncoding.bitsPositive rich recodedLeft (BinaryRecoding.positive mask left leftPositive))⟩
  have rightMember : (GraphModelClass.positive graph).Mem (cellModel rich right reference) := ⟨
    refine_compatible rich (BinaryEncoding.model rich recodedRight)
      (BinaryEncoding.compatible rich recodedRight (BinaryRecoding.compatible mask right rightCompatible)),
    refine_positive rich (BinaryEncoding.model rich recodedRight)
      (BinaryEncoding.respectsParentBits rich recodedRight)
      (BinaryEncoding.bitsPositive rich recodedRight (BinaryRecoding.positive mask right rightPositive))⟩
  exact {
    left := cellModel rich left reference
    right := cellModel rich right reference
    left_mem := leftMember
    right_mem := rightMember
    observationally_equal := refine_observationally_equivalent rich
      (BinaryEncoding.model rich recodedLeft) (BinaryEncoding.model rich recodedRight)
      (BinaryEncoding.respectsParentBits rich recodedLeft) (BinaryEncoding.respectsParentBits rich recodedRight)
      (BinaryEncoding.observationally_equivalent rich recodedLeft recodedRight
        (BinaryRecoding.observationally_equivalent mask left right equivalent))
    query_separated := by
      intro finalEquivalent
      rcases finalEquivalent rich.second
        (leftMember.2.kernelPositiveSupportedValue query.operationKernel rich.second).toSupported
        (rightMember.2.kernelPositiveSupportedValue query.operationKernel rich.second).toSupported with ⟨same⟩
      exact separated ⟨ProbabilityResult.trans
        (ProbabilityResult.symm (cellModel_conditionalCell query rich left reference))
        (ProbabilityResult.trans same (cellModel_conditionalCell query rich right reference))⟩
  }

/-- Every positive Boolean conditional counterexample lifts to the supplied
original alphabet.  Finite rational comparison returns an actual separated
source cell; the cell-level constructor then retains that very pair through
the original-query label transport.  No matched-marginal, protected-pivot,
singleton-conditioner or Boolean-reference restriction remains. -/
noncomputable def positiveConditionalCounterexampleOfBinary
    (query : ConditionalKernelQuery S) (rich : ObservedSignature.ValueRich S)
    (binary : ConditionalCounterexampleIn (GraphModelClass.positive graph.binary) query.binary) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  let cell := binary.separatedCell (fun member => member.2)
  apply positiveConditionalCounterexampleOfBinaryCell query rich binary.left binary.right
    binary.left_mem.1 binary.right_mem.1 binary.left_mem.2 binary.right_mem.2
    binary.observationally_equal cell.reference
  intro supplied
  rcases supplied with ⟨same⟩
  have values := ProbabilityResult.trans (ProbabilityResult.symm cell.leftValue.equivalent)
    (ProbabilityResult.trans same cell.rightValue.equivalent)
  cases values with
  | value equal => exact cell.separated equal

end ObservedValueRefinement
end Causality
end Thesis
