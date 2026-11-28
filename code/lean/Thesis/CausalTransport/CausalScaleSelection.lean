import Thesis.CausalTransport.CausalAbstractionInverseConditional

/-!
# Least-cost selection of a causal scale

Candidates share the fine model signature and may declare different
coarse alphabets. Each required fine experiment must have a measured
representative in a candidate's protocol. A candidate must have at least
one compatible fine model and satisfy the declared widths. Conditional
requests always need some supported model, and the caller chooses whether
any undefined case disqualifies the candidate.

The candidate list and cost function are explicit. The search certifies
the minimum among admitted candidates in that list, with ties resolved by
list order.
-/

namespace Thesis.Causality.CausalScaleSelection

open Probability Probability.Distros CausalAbstractionInverse
open CausalAbstractionSynthesis (interventionDecidableEq)

variable {fine coarse : ObservedSignature.{0}}

/-- A width limits the difference between any pair of admissible answers. -/
inductive Request (fine : ObservedSignature.{0}) where
  | event (query : EventQuery fine) (width : SignedRatio)
  | conditional (evidence query : EventQuery fine) (width : SignedRatio) (allowUndefined : Bool)

def Request.Holds (req : Request fine) (spec : Specification fine coarse) : Prop :=
  match req with
  | .event query width =>
      ∀ left right, spec.Fits left → spec.Fits right →
        SignedRatio.LE (SignedRatio.sub (query.value left).toSignedRatio
          (query.value right).toSignedRatio) width
  | .conditional evidence query width allowUndefined =>
      Nonempty (spec.SupportedModel evidence) ∧
      (allowUndefined = false → ∀ model, spec.Fits model → 0 < (evidence.value model).num) ∧
      ∀ left right : spec.SupportedModel evidence,
        SignedRatio.LE (SignedRatio.sub (left.value query).toSignedRatio
          (right.value query).toSignedRatio) width

private theorem spread_mono {lower upper first second : SignedRatio}
    (atLeast : SignedRatio.LE lower second) (atMost : SignedRatio.LE first upper) :
    SignedRatio.LE (SignedRatio.sub first second) (SignedRatio.sub upper lower) :=
  SignedRatio.add_le_add atMost ((SignedRatio.neg_le_neg_iff _ _).mpr atLeast)

/-- Since both extrema are attained, checking their width decides the
pointwise requirement over the entire fine model class. -/
private theorem event_width_iff {spec : Specification fine coarse} {query : EventQuery fine}
    (sharp : spec.QueryBounds query) (width : SignedRatio) :
    SignedRatio.LE (SignedRatio.sub sharp.upper sharp.lower) width ↔
      (Request.event query width).Holds spec := by
  constructor
  · intro bounded left right leftFits rightFits
    exact SignedRatio.le_trans (spread_mono (sharp.bounds right rightFits).1
      (sharp.bounds left leftFits).2) bounded
  · intro holds
    exact (SignedRatio.le_congr (ratio_sub_congr sharp.upperAttained sharp.lowerAttained)
      (SignedRatio.equiv_refl _)).mp
      (holds sharp.upperModel sharp.lowerModel sharp.upperFits sharp.lowerFits)

private theorem conditional_width_iff {spec : Specification fine coarse}
    {evidence query : EventQuery fine} (sharp : spec.ConditionalBounds evidence query)
    (width : SignedRatio) :
    SignedRatio.LE (SignedRatio.sub (sharp.upper.value query).toSignedRatio
      (sharp.lower.value query).toSignedRatio) width ↔
      ∀ left right : spec.SupportedModel evidence,
        SignedRatio.LE (SignedRatio.sub (left.value query).toSignedRatio
          (right.value query).toSignedRatio) width := by
  constructor
  · intro bounded left right
    exact SignedRatio.le_trans (spread_mono
      ((SignedRatio.toSignedRatio_le_iff _ _).mpr (sharp.bounds right).1)
      ((SignedRatio.toSignedRatio_le_iff _ _).mpr (sharp.bounds left).2)) bounded
  · intro holds
    exact holds sharp.upper sharp.lower

/-- The rejection records the attained limits, or the kind of support
failure, separately from its proof of failure. -/
inductive QueryFailure where
  | tooWide (lower upper : SignedRatio)
  | neverDefined
  | sometimesUndefined

inductive QueryCheck (spec : Specification fine coarse) (req : Request fine) where
  | passed (holds : req.Holds spec)
  | rejected (reason : QueryFailure) (excluded : ¬ req.Holds spec)

private def checkConditionalWidth {spec : Specification fine coarse} {evidence query : EventQuery fine}
    (sharp : spec.ConditionalBounds evidence query) (width : SignedRatio) (allowUndefined : Bool)
    (support : allowUndefined = false → ∀ model, spec.Fits model → 0 < (evidence.value model).num) :
    QueryCheck spec (.conditional evidence query width allowUndefined) :=
  let lower := (sharp.lower.value query).toSignedRatio
  let upper := (sharp.upper.value query).toSignedRatio
  if bounded : SignedRatio.LE (SignedRatio.sub upper lower) width then
    .passed ⟨⟨sharp.lower⟩, support, (conditional_width_iff sharp width).mp bounded⟩
  else .rejected (.tooWide lower upper)
    (fun claimed => bounded ((conditional_width_iff sharp width).mpr claimed.2.2))

def Request.check (spec : Specification fine coarse) (valid : spec.Valid)
    (compatible : ∃ model, spec.Fits model) (req : Request fine) : QueryCheck spec req :=
  match req with
  | .event query width =>
    match spec.solveQuery query with
    | .invalid excluded => False.elim (excluded valid)
    | .incompatible _ excluded => False.elim (excluded compatible)
    | .point _ sharp _ | .interval _ sharp _ =>
      if bounded : SignedRatio.LE (SignedRatio.sub sharp.upper sharp.lower) width then
        .passed ((event_width_iff sharp width).mp bounded)
      else .rejected (.tooWide sharp.lower sharp.upper)
        (fun claimed => bounded ((event_width_iff sharp width).mpr claimed))
  | .conditional evidence query width allowUndefined =>
    match spec.solveConditional evidence query with
    | .invalid excluded => False.elim (excluded valid)
    | .incompatible _ excluded => False.elim (excluded compatible)
    | .undefined _ _ _ allNull => .rejected .neverDefined (fun claimed => by
        obtain ⟨model⟩ := claimed.1
        have positive := (QProb.equiv_num_pos_iff (evidence.value_eq_probVal model.model)).mpr model.positive
        rw [allNull model.model model.fits] at positive
        exact (Nat.lt_irrefl 0 positive))
    | .supported _ sharp null =>
        match allowUndefined with
        | false =>
          match null with
          | .possible model fits zero => .rejected .sometimesUndefined (fun claimed => by
              have positive := claimed.2.1 rfl model fits
              rw [zero] at positive
              exact Nat.lt_irrefl 0 positive)
          | .impossible positive => checkConditionalWidth sharp width false (fun _ => positive)
        | true => checkConditionalWidth sharp width true (fun impossible =>
            False.elim (Bool.noConfusion impossible))

structure Workload (fine : ObservedSignature.{0}) where
  requiredExperiments : List (HardIntervention fine)
  requests : List (Request fine)

structure Candidate (fine : ObservedSignature.{0}) where
  coarse : ObservedSignature.{0}
  specification : Specification fine coarse
  cost : Nat

/-- Coverage means a fixed required fine experiment actually enters the
likelihood-free experimental constraint system of this candidate. -/
def Candidate.Covers (candidate : Candidate fine) (action : HardIntervention fine) : Prop :=
  ∃ measured ∈ candidate.specification.measurements,
    candidate.specification.omega action = some measured.action

instance (candidate : Candidate fine) (action : HardIntervention fine) :
    Decidable (candidate.Covers action) := by
  unfold Candidate.Covers
  infer_instance

structure Candidate.Accepted (candidate : Candidate fine) (workload : Workload fine) : Prop where
  covers : ∀ action ∈ workload.requiredExperiments, candidate.Covers action
  valid : candidate.specification.Valid
  compatible : ∃ model, candidate.specification.Fits model
  requests : ∀ req ∈ workload.requests, req.Holds candidate.specification

inductive CandidateFailure (candidate : Candidate fine) (workload : Workload fine) where
  | missingExperiment (action : HardIntervention fine) (required : action ∈ workload.requiredExperiments)
      (missing : ¬ candidate.Covers action)
  | invalidProtocol (invalid : ¬ candidate.specification.Valid)
  | incompatible (excluded : ¬ ∃ model, candidate.specification.Fits model)
  | query (req : Request fine) (listed : req ∈ workload.requests) (reason : QueryFailure)
      (excluded : ¬ req.Holds candidate.specification)

theorem CandidateFailure.excludes (failure : CandidateFailure candidate workload) :
    ¬ candidate.Accepted workload := by
  intro accepted
  cases failure with
  | missingExperiment action required missing => exact missing (accepted.covers action required)
  | invalidProtocol invalid => exact invalid accepted.valid
  | incompatible excluded => exact excluded accepted.compatible
  | query req listed _ excluded => exact excluded (accepted.requests req listed)

private inductive CoverageCheck (candidate : Candidate fine) : List (HardIntervention fine) → Type where
  | all {actions} (covers : ∀ action ∈ actions, candidate.Covers action) : CoverageCheck candidate actions
  | missing {actions} (action : HardIntervention fine) (required : action ∈ actions)
      (excluded : ¬ candidate.Covers action) : CoverageCheck candidate actions

private def checkCoverage (candidate : Candidate fine) :
    (actions : List (HardIntervention fine)) → CoverageCheck candidate actions
  | [] => .all (fun _ required => False.elim (List.not_mem_nil required))
  | action :: rest =>
    if found : candidate.Covers action then
      match checkCoverage candidate rest with
      | .all later => .all (fun a required =>
          (List.mem_cons.mp required).elim (fun same => same.symm ▸ found) (later a))
      | .missing a required missing => .missing a (List.mem_cons_of_mem _ required) missing
    else .missing action (List.mem_cons_self ..) found

private inductive RequestListCheck (candidate : Candidate fine) : List (Request fine) → Type where
  | all {reqs} (holds : ∀ req ∈ reqs, req.Holds candidate.specification) : RequestListCheck candidate reqs
  | failed {reqs} (req : Request fine) (listed : req ∈ reqs) (reason : QueryFailure)
      (excluded : ¬ req.Holds candidate.specification) : RequestListCheck candidate reqs

private def checkRequests (candidate : Candidate fine) (valid : candidate.specification.Valid)
    (compatible : ∃ model, candidate.specification.Fits model) :
    (reqs : List (Request fine)) → RequestListCheck candidate reqs
  | [] => .all (fun _ listed => False.elim (List.not_mem_nil listed))
  | req :: rest =>
    match req.check candidate.specification valid compatible with
    | .rejected reason excluded => .failed req (List.mem_cons_self ..) reason excluded
    | .passed first =>
      match checkRequests candidate valid compatible rest with
      | .failed other listed reason excluded => .failed other (List.mem_cons_of_mem _ listed) reason excluded
      | .all later => .all (fun r listed =>
          (List.mem_cons.mp listed).elim (fun same => same.symm ▸ first) (later r))

inductive CandidateCheck (candidate : Candidate fine) (workload : Workload fine) where
  | pass (accepted : candidate.Accepted workload)
  | fail (failure : CandidateFailure candidate workload)

def Candidate.check (candidate : Candidate fine) (workload : Workload fine) :
    CandidateCheck candidate workload :=
  match checkCoverage candidate workload.requiredExperiments with
  | .missing action required missing => .fail (.missingExperiment action required missing)
  | .all covers =>
    if valid : candidate.specification.Valid then
      match candidate.specification.problem.solvePruned with
      | .infeasible certificate => .fail (.incompatible
          (candidate.specification.infeasible_not_exists certificate))
      | .feasible law =>
        let compatible : ∃ model, candidate.specification.Fits model :=
          ⟨candidate.specification.fittedModel law, candidate.specification.fittedModel_fits law⟩
        match checkRequests candidate valid compatible workload.requests with
        | .failed req listed reason excluded => .fail (.query req listed reason excluded)
        | .all passed => .pass ⟨covers, valid, compatible, passed⟩
    else .fail (.invalidProtocol valid)

inductive Selection (workload : Workload fine) (candidates : List (Candidate fine)) where
  | none (excluded : ∀ candidate ∈ candidates, ¬ candidate.Accepted workload)
  | best (candidate : Candidate fine) (listed : candidate ∈ candidates)
      (accepted : candidate.Accepted workload)
      (least : ∀ other ∈ candidates, other.Accepted workload → candidate.cost ≤ other.cost)

/-- Select the cheapest accepted scale in the finite candidate list, or
prove every listed candidate fails the same workload. -/
def select (workload : Workload fine) : (candidates : List (Candidate fine)) → Selection workload candidates
  | [] => .none (fun _ listed => False.elim (List.not_mem_nil listed))
  | candidate :: rest =>
    match candidate.check workload, select workload rest with
    | .fail failure, .none excluded => .none (fun c listed =>
        (List.mem_cons.mp listed).elim (fun same => same.symm ▸ failure.excludes) (excluded c))
    | .fail failure, .best best listed accepted least =>
        .best best (List.mem_cons_of_mem _ listed) accepted (fun c member qualifies =>
          (List.mem_cons.mp member).elim (fun same => False.elim (failure.excludes (same ▸ qualifies)))
            (fun later => least c later qualifies))
    | .pass accepted, .none excluded =>
        .best candidate (List.mem_cons_self ..) accepted (fun c member qualifies =>
          (List.mem_cons.mp member).elim (fun same => same.symm ▸ Nat.le_refl candidate.cost)
            (fun later => False.elim (excluded c later qualifies)))
    | .pass accepted, .best best listed bestAccepted least =>
      if cheaper : candidate.cost ≤ best.cost then
        .best candidate (List.mem_cons_self ..) accepted (fun c member qualifies =>
          (List.mem_cons.mp member).elim (fun same => same.symm ▸ Nat.le_refl candidate.cost)
            (fun later => Nat.le_trans cheaper (least c later qualifies)))
      else .best best (List.mem_cons_of_mem _ listed) bestAccepted (fun c member qualifies =>
        (List.mem_cons.mp member).elim
          (fun same => same.symm ▸ Nat.le_of_lt (Nat.lt_of_not_ge cheaper))
          (fun later => least c later qualifies))

end Thesis.Causality.CausalScaleSelection
