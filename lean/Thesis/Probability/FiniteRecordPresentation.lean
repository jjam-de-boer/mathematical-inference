import Thesis.Probability.Construction

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Finite presentations without expanding natural weights

A finite record can have an infinite ambient label type: a bounded count law
may, for example, be stored on `List Nat`. Its existing atom occurrences
nevertheless provide a finite *sampling* type. Keep one index per occurrence
and retain its original weight, rather than expanding a large denominator
into that many unit cells. Repeated labels and zero-weight atoms are retained.

Sampling indices must not be confused with observable values. The separate
domain construction takes an explicit finite list of permitted values, which
may include values of probability zero, and enumerates its subtype without
duplicates. That presentation is bijective on the declared domain, not on an
arbitrary infinite ambient type or merely on the positive-probability cells.

Both constructions recover the original record by decoding. The shared
`FinitePresentation` interface then transports all Boolean event probabilities
and supported conditionals. No equality decision on ambient labels is needed
for occurrence indexing; domain deduplication requests one explicitly.
-/

/-- Equality of record data; normalization proof fields are proof-irrelevant. -/
theorem eq_of_atoms_den {left right : FiniteProbRecord Ω}
    (atoms : left.atoms = right.atoms) (denominator : left.den = right.den) : left = right := by
  cases left
  cases right
  cases atoms
  cases denominator
  rfl

/-- The label of an original atom occurrence, with no default value or
choice of a representative for repeated labels. -/
def atomIndexLabel (record : FiniteProbRecord Ω) (index : Fin record.atoms.length) : Ω :=
  record.atoms[index.val].1

private def indexedAtoms (atoms : List (Ω × Nat)) : List (Fin atoms.length × Nat) :=
  (List.finRange atoms.length).map (fun index => (index, atoms[index.val].2))

private theorem indexedAtoms_decode (atoms : List (Ω × Nat)) :
    (indexedAtoms atoms).map (fun atom => (atoms[atom.1.val].1, atom.2)) = atoms := by
  change (List.finRange atoms.length).map (fun index => atoms[index.val]) = atoms
  rw [List.finRange, List.map_ofFn]
  exact List.ofFn_getElem

/-- A finite sampling record with the original weights and denominator.
Its size counts occurrences, not total mass or distinct observable values. -/
def atomIndexRecord (record : FiniteProbRecord Ω) : FiniteProbRecord (Fin record.atoms.length) where
  atoms := indexedAtoms record.atoms
  den := record.den
  den_pos := record.den_pos
  total_mass := by
    have recovered := congrArg totalMass (indexedAtoms_decode record.atoms)
    rw [totalMass_map_labels] at recovered
    exact recovered.trans record.total_mass

/-- Decoding reconstructs the literal record, including order, multiplicity
and zero weights, not just its normalized event probabilities. -/
theorem atomIndexRecord_map (record : FiniteProbRecord Ω) :
    record.atomIndexRecord.map record.atomIndexLabel = record := by
  apply eq_of_atoms_den
  · exact indexedAtoms_decode record.atoms
  · rfl

theorem atomIndexRecord_length (record : FiniteProbRecord Ω) :
    record.atomIndexRecord.atoms.length = record.atoms.length := by
  simp only [atomIndexRecord, indexedAtoms, List.length_map, List.length_finRange]

/-- A finite sampling presentation with its proved decoding map. There is
deliberately no inverse on all ambient labels: repeated labels are allowed. -/
structure FinitePresentation (original : FiniteProbRecord Ω) where
  card : Nat
  record : FiniteProbRecord (Fin card)
  decode : Fin card → Ω
  recovered : record.map decode = original

def atomPresentation (record : FiniteProbRecord Ω) : FinitePresentation record where
  card := record.atoms.length
  record := record.atomIndexRecord
  decode := record.atomIndexLabel
  recovered := record.atomIndexRecord_map

namespace FinitePresentation

/-- Every original event is read through the same decoder. Sampling codes
are not exposed as extra observable distinctions. -/
theorem probVal {original : FiniteProbRecord Ω} (presentation : FinitePresentation original)
    (event : Event Ω) :
    QProb.Equiv (presentation.record.probVal (fun code => event (presentation.decode code)))
      (original.probVal event) := by
  have mapped := presentation.record.map_probVal presentation.decode event
  rw [presentation.recovered] at mapped
  exact QProb.equiv_symm mapped

/-- Support is transported in both directions, never manufactured for a
null conditioner by assigning it a default conditional value. -/
theorem eventPositive_iff {original : FiniteProbRecord Ω} (presentation : FinitePresentation original)
    (evidence : Event Ω) :
    presentation.record.EventPositive (fun code => evidence (presentation.decode code)) ↔
      original.EventPositive evidence :=
  QProb.equiv_num_pos_iff (presentation.probVal evidence)

theorem conditionOn_probVal {original : FiniteProbRecord Ω} (presentation : FinitePresentation original)
    (evidence event : Event Ω) (supported : original.EventPositive evidence) :
    QProb.Equiv
      ((presentation.record.conditionOn (fun code => evidence (presentation.decode code))
        ((presentation.eventPositive_iff evidence).mpr supported)).probVal
        (fun code => event (presentation.decode code)))
      ((original.conditionOn evidence supported).probVal event) := by
  let sourceSupported := (presentation.eventPositive_iff evidence).mpr supported
  exact QProb.equiv_trans
    (presentation.record.conditionOn_probVal _ _ sourceSupported)
    (QProb.equiv_trans
      (QProb.div_congr (presentation.probVal (fun value => evidence value && event value))
        (presentation.probVal evidence) sourceSupported supported)
      (QProb.equiv_symm (original.conditionOn_probVal evidence event supported)))

end FinitePresentation

private def domainAtoms (record : FiniteProbRecord Ω) (domain : List Ω)
    (covered : forall atom, atom ∈ record.atoms → atom.1 ∈ domain) :
    List ({value : Ω // value ∈ domain} × Nat) :=
  record.atoms.attach.map (fun atom => (⟨atom.val.1, covered atom.val atom.property⟩, atom.val.2))

private theorem domainAtoms_decode (record : FiniteProbRecord Ω) (domain : List Ω)
    (covered : forall atom, atom ∈ record.atoms → atom.1 ∈ domain) :
    (domainAtoms record domain covered).map (fun atom => (atom.1.val, atom.2)) = record.atoms := by
  unfold domainAtoms
  rw [List.map_map]
  change record.atoms.attach.map Subtype.val = record.atoms
  exact List.attach_map_subtype_val _

/-- Restrict the ambient type to a supplied finite domain that covers every
listed atom. The domain may strictly exceed the record's positive support. -/
def onDomain (record : FiniteProbRecord Ω) (domain : List Ω)
    (covered : forall atom, atom ∈ record.atoms → atom.1 ∈ domain) :
    FiniteProbRecord {value : Ω // value ∈ domain} where
  atoms := domainAtoms record domain covered
  den := record.den
  den_pos := record.den_pos
  total_mass := by
    have recovered := congrArg totalMass (domainAtoms_decode record domain covered)
    rw [totalMass_map_labels] at recovered
    exact recovered.trans record.total_mass

theorem onDomain_map (record : FiniteProbRecord Ω) (domain : List Ω)
    (covered : forall atom, atom ∈ record.atoms → atom.1 ∈ domain) :
    (record.onDomain domain covered).map Subtype.val = record := by
  apply eq_of_atoms_den
  · exact domainAtoms_decode record domain covered
  · rfl

/-- Enumerate distinct permitted values, including permitted zero-probability
values. This is a bijection of the declared subtype, not of the ambient type. -/
def domainWitness [DecidableEq Ω] (domain : List Ω) : FiniteWitness {value : Ω // value ∈ domain} :=
  FiniteWitness.ofList (deduplicate domain.attach)
    (fun value => (mem_deduplicate _ _).mpr (List.mem_attach domain value)) (deduplicate_nodup _)

def domainPresentation [DecidableEq Ω] (record : FiniteProbRecord Ω) (domain : List Ω)
    (covered : forall atom, atom ∈ record.atoms → atom.1 ∈ domain) : FinitePresentation record where
  card := (domainWitness domain).card
  record := (record.onDomain domain covered).map (domainWitness domain).encode
  decode := fun code => ((domainWitness domain).decode code).val
  recovered := by
    rw [map_comp]
    have same : (fun value => ((domainWitness domain).decode ((domainWitness domain).encode value)).val) =
        (Subtype.val : {value : Ω // value ∈ domain} → Ω) := by
      funext value
      rw [(domainWitness domain).decode_encode]
    rw [same]
    exact record.onDomain_map domain covered

/-- Unlike occurrence indexing, domain decoding is injective. An observed
value therefore has exactly one code, even if several record atoms share it. -/
theorem domainPresentation_decode_injective [DecidableEq Ω] (record : FiniteProbRecord Ω)
    (domain : List Ω) (covered : forall atom, atom ∈ record.atoms → atom.1 ∈ domain)
    (left right : Fin (domainWitness domain).card)
    (same : (record.domainPresentation domain covered).decode left =
      (record.domainPresentation domain covered).decode right) : left = right := by
  have values : (domainWitness domain).decode left = (domainWitness domain).decode right :=
    Subtype.ext same
  exact ((domainWitness domain).encode_decode left).symm.trans
    ((congrArg (domainWitness domain).encode values).trans ((domainWitness domain).encode_decode right))

end FiniteProbRecord
end Probability
end Thesis
