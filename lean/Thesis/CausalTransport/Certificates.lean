import Thesis.Causality.Identification
import Thesis.CausalTransport.DSeparation

namespace Thesis
namespace Causality

open Probability

/-!
Generic inspectable certificates for a source probability term.

Both joint and conditional kernel queries reduce to a source
`ProbabilityTerm`; their identification certificates differ only in which
query supplies that term.  This module factors out that shared certificate
shape. `Correspondence` provides query-specific structures and explicit
adapters to this generic representation.

Support is demanded only inside a selected `GraphModelClass`.  The classical
completeness inhabitant uses the strictly positive subclass; the SCM layer
continues to admit observational zeros.
-/

/--
An inspectable action-free reduction of one source probability term.  The
support field supplies the recursive support tree required to interpret the
concrete do-calculus derivation in every model of the selected class.
-/
structure IdentificationCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (sourceTerm : ProbabilityTerm S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : DoCalculusDerivation G sourceTerm formula
  supported : forall model : ExactModel S, (member : C.Mem model) ->
    forall assignment, sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment derivation

/--
The corresponding pre-compilation certificate: its derivation is expressed
with active-path side conditions and is compiled only after d-separation
correctness has been supplied explicitly.
-/
structure PublishedIdentificationCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (sourceTerm : ProbabilityTerm S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G sourceTerm formula
  supported : forall model : ExactModel S, (member : C.Mem model) ->
    forall assignment, sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment (derivation.compile correct)

/-- Compile path-based side conditions into the executable derivation syntax. -/
def PublishedIdentificationCertificate.compile
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {sourceTerm : ProbabilityTerm S}
    (certificate : PublishedIdentificationCertificate C correct sourceTerm) :
    IdentificationCertificate C sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation.compile correct
  supported := certificate.supported

/-! ## Structural composition of published certificates -/

/--
The reflexive published certificate for an action-free probability term.
This is the neutral element used by structural certificate folds.
-/
noncomputable def PublishedIdentificationCertificate.refl
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} (term : ProbabilityTerm S)
    (actionFree : term.ActionFree) :
    PublishedIdentificationCertificate C correct term where
  formula := term
  actionFree := actionFree
  derivation :=
    DoCalculusDerivation.refl
      (G := G) (separation := pathRuleSeparation G) term
  supported := fun _model _member _assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact ⟨sourceSupported, ⟨sourceSupported, ()⟩⟩

/--
Compose two published reductions whose intermediate probability term agrees
definitionally.  The support tree is composed in the same order: support of
the first endpoint feeds the second certificate, and both recursive support
trees are retained beneath the derivation's `trans` constructor.
-/
noncomputable def PublishedIdentificationCertificate.trans
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {sourceTerm : ProbabilityTerm S}
    (first : PublishedIdentificationCertificate C correct sourceTerm)
    (second : PublishedIdentificationCertificate C correct first.formula) :
    PublishedIdentificationCertificate C correct sourceTerm where
  formula := second.formula
  actionFree := second.actionFree
  derivation :=
    DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      first.derivation second.derivation
  supported := fun model member assignment sourceSupported => by
    let firstSupported :=
      first.supported model member assignment sourceSupported
    let secondSupported :=
      second.supported model member assignment firstSupported.endpoints.2
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact
      ⟨sourceSupported,
        ⟨secondSupported.endpoints.2,
          ⟨firstSupported, secondSupported⟩⟩⟩

/--
Lift a published reduction through a finite marginalization.  Support of the
source marginal yields support of each enumerated source summand; applying
the original certificate pointwise supplies both the recursive congruence
support and support of every target summand.
-/
noncomputable def PublishedIdentificationCertificate.marginalize
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {sourceTerm : ProbabilityTerm S}
    (nodes : NodeSet S)
    (certificate : PublishedIdentificationCertificate C correct sourceTerm) :
    PublishedIdentificationCertificate C correct
      (.marginalize nodes sourceTerm) where
  formula := .marginalize nodes certificate.formula
  actionFree := certificate.actionFree
  derivation :=
    DoCalculusDerivation.marginalizeCongr
      (G := G) (separation := pathRuleSeparation G)
      nodes certificate.derivation
  supported := fun model member assignment sourceSupported => by
    let variants := ProbabilityTerm.marginalAssignments S nodes assignment
    have sourceVariantSupported (variant : S.Assignment)
        (variantMember : variant ∈ variants) :
        sourceTerm.SupportedAt model variant := by
      change ProbabilityResult.Supported (sourceTerm.denote model variant)
      apply ProbabilityResult.supported_map_of_mem_sum variants
        (fun candidate => sourceTerm.denote model candidate) variant
        variantMember
      simpa [variants, ProbabilityTerm.SupportedAt,
        ProbabilityTerm.denote] using sourceSupported
    let pointwise := fun (variant : S.Assignment)
        (variantMember : variant ∈ variants) =>
      certificate.supported model member variant
        (sourceVariantSupported variant variantMember)
    have targetSupported :
        (ProbabilityTerm.marginalize nodes certificate.formula).SupportedAt
          model assignment := by
      change ProbabilityResult.Supported
        (ProbabilityResult.sum
          (variants.map fun variant =>
            certificate.formula.denote model variant))
      exact ProbabilityResult.sum_map_supported_of_mem variants
        (fun variant => certificate.formula.denote model variant)
        (fun variant variantMember =>
          (pointwise variant variantMember).endpoints.2)
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact
      ⟨sourceSupported,
        ⟨targetSupported,
          fun variant variantMember => pointwise variant variantMember⟩⟩

/--
Reindex both endpoints of a published certificate along syntactic equality.
The original derivation remains visible below `eqCongr`, so compilation and
recursive support inspection do not get stuck behind equality transport.
-/
noncomputable def PublishedIdentificationCertificate.reindex
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    {sourceTerm sourceTerm' targetTerm : ProbabilityTerm S}
    (certificate : PublishedIdentificationCertificate C correct sourceTerm)
    (sourceEq : sourceTerm' = sourceTerm)
    (targetEq : targetTerm = certificate.formula) :
    PublishedIdentificationCertificate C correct sourceTerm' where
  formula := targetTerm
  actionFree := targetEq ▸ certificate.actionFree
  derivation :=
    DoCalculusDerivation.eqCongr
      (G := G) (separation := pathRuleSeparation G)
      sourceEq targetEq certificate.derivation
  supported := fun model member assignment sourceSupported => by
    let innerSource :=
      ProbabilityTerm.SupportedAt.congr sourceEq sourceSupported
    let innerSupported :=
      certificate.supported model member assignment innerSource
    let targetSupported :=
      ProbabilityTerm.SupportedAt.congr targetEq.symm
        innerSupported.endpoints.2
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact ⟨sourceSupported, ⟨targetSupported, innerSupported⟩⟩

/-- Lift a published reduction through evaluation at a fixed assignment. -/
noncomputable def PublishedIdentificationCertificate.evaluateAt
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {sourceTerm : ProbabilityTerm S}
    (fixed : S.Assignment)
    (certificate : PublishedIdentificationCertificate C correct sourceTerm) :
    PublishedIdentificationCertificate C correct
      (.evaluateAt fixed sourceTerm) where
  formula := .evaluateAt fixed certificate.formula
  actionFree := certificate.actionFree
  derivation :=
    DoCalculusDerivation.evaluateAtCongr
      (G := G) (separation := pathRuleSeparation G)
      fixed certificate.derivation
  supported := fun model member assignment sourceSupported => by
    have innerSource : sourceTerm.SupportedAt model fixed := by
      simpa [ProbabilityTerm.SupportedAt, ProbabilityTerm.denote] using
        sourceSupported
    let innerSupported :=
      certificate.supported model member fixed innerSource
    have targetSupported :
        (ProbabilityTerm.evaluateAt fixed certificate.formula).SupportedAt
          model assignment := by
      simpa [ProbabilityTerm.SupportedAt, ProbabilityTerm.denote] using
        innerSupported.endpoints.2
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact ⟨sourceSupported, ⟨targetSupported, innerSupported⟩⟩

/-- Lift two published reductions through addition. -/
noncomputable def PublishedIdentificationCertificate.add
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    {leftSource rightSource : ProbabilityTerm S}
    (left : PublishedIdentificationCertificate C correct leftSource)
    (right : PublishedIdentificationCertificate C correct rightSource) :
    PublishedIdentificationCertificate C correct
      (.add leftSource rightSource) where
  formula := .add left.formula right.formula
  actionFree := ⟨left.actionFree, right.actionFree⟩
  derivation :=
    DoCalculusDerivation.addCongr
      (G := G) (separation := pathRuleSeparation G)
      left.derivation right.derivation
  supported := fun model member assignment sourceSupported => by
    have leftSourceSupported : leftSource.SupportedAt model assignment :=
      ProbabilityResult.supported_left_of_add sourceSupported
    have rightSourceSupported : rightSource.SupportedAt model assignment :=
      ProbabilityResult.supported_right_of_add sourceSupported
    let leftSupported :=
      left.supported model member assignment leftSourceSupported
    let rightSupported :=
      right.supported model member assignment rightSourceSupported
    have targetSupported :
        (ProbabilityTerm.add left.formula right.formula).SupportedAt
          model assignment :=
      ProbabilityResult.add_supported leftSupported.endpoints.2
        rightSupported.endpoints.2
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact
      ⟨sourceSupported,
        ⟨targetSupported, ⟨leftSupported, rightSupported⟩⟩⟩

/-- Lift two published reductions through multiplication. -/
noncomputable def PublishedIdentificationCertificate.multiply
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    {leftSource rightSource : ProbabilityTerm S}
    (left : PublishedIdentificationCertificate C correct leftSource)
    (right : PublishedIdentificationCertificate C correct rightSource) :
    PublishedIdentificationCertificate C correct
      (.multiply leftSource rightSource) where
  formula := .multiply left.formula right.formula
  actionFree := ⟨left.actionFree, right.actionFree⟩
  derivation :=
    DoCalculusDerivation.multiplyCongr
      (G := G) (separation := pathRuleSeparation G)
      left.derivation right.derivation
  supported := fun model member assignment sourceSupported => by
    have leftSourceSupported : leftSource.SupportedAt model assignment :=
      ProbabilityResult.supported_left_of_multiply sourceSupported
    have rightSourceSupported : rightSource.SupportedAt model assignment :=
      ProbabilityResult.supported_right_of_multiply sourceSupported
    let leftSupported :=
      left.supported model member assignment leftSourceSupported
    let rightSupported :=
      right.supported model member assignment rightSourceSupported
    have targetSupported :
        (ProbabilityTerm.multiply left.formula right.formula).SupportedAt
          model assignment :=
      ProbabilityResult.multiply_supported leftSupported.endpoints.2
        rightSupported.endpoints.2
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact
      ⟨sourceSupported,
        ⟨targetSupported, ⟨leftSupported, rightSupported⟩⟩⟩

/--
Lift two published reductions through division once support of the target
quotient is supplied.  This extra premise is essential: support of both
target factors does not by itself say that the target denominator is
positive, and certificate composition must not smuggle that semantic fact
through the purely syntactic derivation.
-/
noncomputable def PublishedIdentificationCertificate.divideWithSupport
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G}
    {numeratorSource denominatorSource : ProbabilityTerm S}
    (numerator : PublishedIdentificationCertificate C correct numeratorSource)
    (denominator :
      PublishedIdentificationCertificate C correct denominatorSource)
    (targetSupported : forall (model : ExactModel S), C.Mem model ->
      forall assignment,
        (ProbabilityTerm.divide numeratorSource denominatorSource).SupportedAt
            model assignment ->
          (ProbabilityTerm.divide numerator.formula
            denominator.formula).SupportedAt model assignment) :
    PublishedIdentificationCertificate C correct
      (.divide numeratorSource denominatorSource) where
  formula := .divide numerator.formula denominator.formula
  actionFree := ⟨numerator.actionFree, denominator.actionFree⟩
  derivation :=
    DoCalculusDerivation.divideCongr
      (G := G) (separation := pathRuleSeparation G)
      numerator.derivation denominator.derivation
  supported := fun model member assignment sourceSupported => by
    have numeratorSourceSupported :
        numeratorSource.SupportedAt model assignment :=
      ProbabilityResult.supported_numerator_of_divide sourceSupported
    have denominatorSourceSupported :
        denominatorSource.SupportedAt model assignment :=
      ProbabilityResult.supported_denominator_of_divide sourceSupported
    let numeratorSupported :=
      numerator.supported model member assignment numeratorSourceSupported
    let denominatorSupported :=
      denominator.supported model member assignment denominatorSourceSupported
    let targetSupportedAt :=
      targetSupported model member assignment sourceSupported
    dsimp [PathDoCalculusDerivation.compile,
      DoCalculusDerivation.mapRules]
    exact
      ⟨sourceSupported,
        ⟨targetSupportedAt, ⟨numeratorSupported, denominatorSupported⟩⟩⟩

/-- Restrict a certificate from a larger class to a subclass. -/
def IdentificationCertificate.restrict
    {S : ObservedSignature} {G : ObservedGraph S} {C D : GraphModelClass G}
    {sourceTerm : ProbabilityTerm S}
    (subset : C.Subset D)
    (certificate : IdentificationCertificate D sourceTerm) :
    IdentificationCertificate C sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := fun model member assignment sourceSupported =>
    certificate.supported model (subset model member) assignment sourceSupported

def PublishedIdentificationCertificate.restrict
    {S : ObservedSignature} {G : ObservedGraph S} {C D : GraphModelClass G}
    {correct : DSeparationCorrectness G} {sourceTerm : ProbabilityTerm S}
    (subset : C.Subset D)
    (certificate : PublishedIdentificationCertificate D correct sourceTerm) :
    PublishedIdentificationCertificate C correct sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := fun model member assignment sourceSupported =>
    certificate.supported model (subset model member) assignment sourceSupported

end Causality
end Thesis
