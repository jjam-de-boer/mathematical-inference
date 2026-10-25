import Thesis.CausalTransport.Soundness
import Thesis.Examples.FrontDoorCurrentIdentification

namespace Thesis
namespace Causality

open Probability

/-!
# A checked counterexample to the obsolete ID recursion

Retain the actual refuted computation, not its historical failure-unpacking
library. In the shared positive front-door fixture, this recursion returns
`9/16` where the original causal query has value `1/2`; the corrected engine
returns `1/2` on that same model. All values and both actual result equations
are checked by Lean's kernel.

Only this negative example defines the explicitly qualified `Legacy` program.
Production modules and modern fixtures must not import it. The direct
formula-aligned compiler boundary below expresses the same obstruction using
an executable result equation: no structural trace or fixed-depth branch
library is needed merely to show that an incorrect result cannot have a
sound certificate. This is not a counterexample to Pearl-style completeness.
-/

def Legacy.identifyFuel (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S) : IdentificationOutcome S :=
  match fuel with
  | 0 => .unfinished
  | fuel + 1 =>
      let identifyNext := Legacy.identifyFuel fuel
      let y := NodeSet.inter outcome remaining
      let x := NodeSet.inter action remaining
      if NodeSet.isEmpty x then
        .identified (.marginalize (NodeSet.diff remaining y) current)
      else
        let kept := G.ancestralSet remaining (GraphMutilation.bar x) y
        if NodeSet.equal kept remaining then
          let free := NodeSet.diff remaining x
          let freeComponents := G.cComponents free
          match freeComponents with
          | [] =>
              .identified (.marginalize remaining current)
          | [component] =>
              if G.isSingleCComponent remaining then
                .failed ⟨remaining, component⟩
              else if (G.cComponents remaining).any (fun piece =>
                  NodeSet.equal piece component) then
                .identified
                  (.marginalize (NodeSet.diff component y)
                    (chainProduct remaining component))
              else
                match G.containingCComponent remaining component with
                | some larger =>
                    identifyNext G larger outcome (NodeSet.inter x larger)
                      (chainProduct remaining larger)
                | none =>
                    .unfinished
          | _ :: _ :: _ =>
              IdentificationOutcome.combine
                (freeComponents.map (fun component =>
                  identifyNext G remaining component
                    (NodeSet.diff remaining component) current))
                (fun terms =>
                  .marginalize
                    (NodeSet.diff remaining (NodeSet.union y x))
                    (productTerms terms))
        else
          identifyNext G kept outcome action
            (.marginalize (NodeSet.diff remaining kept) current)

def Legacy.identifyJoint (G : ObservedGraph S) (q : JointKernelQuery S) :
    IdentificationOutcome S :=
  Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome q.action
    (observationalJointTerm S)

/-- A hypothetical certificate for every literal result of the refuted
recursion. This is data supplied by a caller, not an assumed theorem or axiom;
the concrete positive counterexample below proves it cannot be inhabited. -/
structure Legacy.FormulaAlignedCompiler
    {S : ObservedSignature} (G : ObservedGraph S)
    (C : GraphModelClass G) (correct : DSeparationCorrectness G) where
  compile : forall (query : JointKernelQuery S) (term : ProbabilityTerm S),
    Legacy.identifyJoint G query = IdentificationOutcome.identified term →
      { certificate : PublishedJointCertificate C correct query //
          certificate.formula = term }

namespace Examples
namespace FrontDoorIdentification

/-- Extract the actual displayed engine formula, with a harmless fallback
only to make this definition total.  `legacyEngine_identified` proves that the
fallback is not used; a failed or unfinished run cannot fake the regression. -/
def legacyEngineFormula : ProbabilityTerm signature :=
  match Legacy.identifyJoint graph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

set_option maxRecDepth 100000 in
/-- The refuted executable run genuinely takes the identified branch. -/
theorem legacyEngine_identified :
    Legacy.identifyJoint graph query = .identified legacyEngineFormula := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The displayed engine expression evaluates instead to `9/16`.
`decide +kernel` checks ordinary finite reduction; it does not use
`native_decide` or introduce a reduction axiom. -/
def legacyEngineAtReferenceNineSixteenths :
    ProbabilityResult.Equivalent (legacyEngineFormula.denote model reference)
      (some ⟨9, 16, by decide⟩) :=
  equivalentOfValueTest _ _ (by decide +kernel)

/-! ## The actual obstruction to a formula-aligned success compiler -/

/-- The source kernel and displayed engine formula disagree at a supported
assignment.  Positivity and compatibility above exclude regularity or graph
mismatch as explanations for the difference. -/
theorem legacyEngineFormula_not_equivalent :
    ¬ Nonempty (ProbabilityTerm.EquivalentAt model query.sourceTerm
      legacyEngineFormula reference) := by
  intro ⟨equivalent⟩
  let forced := ProbabilityResult.trans (ProbabilityResult.symm sourceAtReferenceHalf)
    (ProbabilityResult.trans equivalent legacyEngineAtReferenceNineSixteenths)
  cases forced with
  | value impossible =>
      exact (by decide : ¬ QProb.Equiv ⟨1, 2, by decide⟩ ⟨9, 16, by decide⟩)
        impossible

/-- No exact-output compiler can certify every result of the refuted
program on this positive graph. The actual result equation supplies the
candidate; published soundness then contradicts its checked numerical value.
This rules out the incorrect recursion, not the corrected current engine. -/
theorem legacyFormulaCompiler_is_uninhabited :
    ¬ Nonempty (Legacy.FormulaAlignedCompiler graph (GraphModelClass.positive graph)
      graph.dSeparationCorrectness) := by
  intro ⟨compiler⟩
  let compiled := compiler.compile query legacyEngineFormula legacyEngine_identified
  let supported : query.sourceTerm.SupportedAt model reference :=
    ⟨⟨1, 2, by decide⟩, sourceAtReferenceHalf⟩
  let sound := compiled.1.compile.denotational_soundAt
    graph.publishedSoundness model ⟨model_compatible, model_positive⟩
    reference supported
  exact legacyEngineFormula_not_equivalent ⟨compiled.2 ▸ sound⟩

end FrontDoorIdentification
end Examples
end Causality
end Thesis
