import Thesis.Probability.Distros.EntropyUniform
import Thesis.Probability.ConstructiveRealGibbsFamilyDerivative

namespace Thesis.Probability
open ConstructiveReal
open Distros

/-- A finite physical microstate model. Indices are distinct physical states,
even when energy and particle count coincide. Energies are signed rational
data; particle numbers are naturals. Physical applicability of these chosen
states and observables is an additional modeling assumption. -/
structure FinitePhysicalModel (states : Nat) where
  nonempty : 0 < states
  energy : Fin states → SignedRatio
  particles : Fin states → Nat

namespace FinitePhysicalModel

/-- Explicit admissibility by a nonempty list of distinct microstate indices.
This is a physical restriction of the state space, not a distribution record
whose repeated atom occurrences may be merged as presentation choices. -/
structure Sector (model : FinitePhysicalModel states) where
  cells : List (Fin states)
  nonempty : 0 < cells.length
  distinct : cells.Nodup

def all (model : FinitePhysicalModel states) : model.Sector :=
  ⟨List.finRange states, by simpa only [List.length_finRange] using model.nonempty, finRange_nodup states⟩

namespace Sector

def state {model : FinitePhysicalModel states} (sector : model.Sector) (i : Fin sector.cells.length) : Fin states := sector.cells[i.val]

theorem state_mem {model : FinitePhysicalModel states} (sector : model.Sector) (i : Fin sector.cells.length) :
    sector.state i ∈ sector.cells := List.getElem_mem i.isLt

theorem state_injective {model : FinitePhysicalModel states} (sector : model.Sector) (i j : Fin sector.cells.length)
    (same : sector.state i = sector.state j) : i = j :=
  Fin.ext ((List.getElem_inj sector.distinct).mp same)

/-- A selected admissible sector inherits its observables without identifying
states sharing their values. -/
def asModel {model : FinitePhysicalModel states} (sector : model.Sector) : FinitePhysicalModel sector.cells.length :=
  ⟨sector.nonempty, (fun i => model.energy (sector.state i)), (fun i => model.particles (sector.state i))⟩

def grid {model : FinitePhysicalModel states} (sector : model.Sector) : EntropyGrid (Fin states) := ⟨sector.cells, sector.distinct⟩

/-- Restriction is computed from a Boolean predicate and one admitted state.
Its nonemptiness proof does not choose a state from a proposition. -/
def restrict {model : FinitePhysicalModel states} (sector : model.Sector) (predicate : Fin states → Bool)
    (witness : Fin sector.cells.length) (admitted : predicate (sector.state witness) = true) : model.Sector :=
  ⟨sector.cells.filter predicate,
    List.length_pos_of_mem (List.mem_filter.mpr ⟨sector.state_mem witness, admitted⟩), sector.distinct.filter predicate⟩

theorem restrict_mem {model : FinitePhysicalModel states} (sector : model.Sector) (predicate : Fin states → Bool)
    (witness : Fin sector.cells.length) (admitted : predicate (sector.state witness) = true) (i : Fin states) :
    i ∈ (sector.restrict predicate witness admitted).cells ↔ i ∈ sector.cells ∧ predicate i = true := List.mem_filter

/-- A finite fixed-energy shell, using rational value equivalence
rather than syntactic equality of unreduced energy presentations. -/
def energyShell {model : FinitePhysicalModel states} (sector : model.Sector) (energy : SignedRatio)
    (witness : Fin sector.cells.length) (atEnergy : SignedRatio.Equiv (model.energy (sector.state witness)) energy) : model.Sector :=
  sector.restrict (fun i => decide (SignedRatio.Equiv (model.energy i) energy)) witness (decide_eq_true atEnergy)

theorem energyShell_exact {model : FinitePhysicalModel states} (sector : model.Sector) (energy : SignedRatio)
    (witness : Fin sector.cells.length) (atEnergy : SignedRatio.Equiv (model.energy (sector.state witness)) energy)
    (i : Fin states) (member : i ∈ (sector.energyShell energy witness atEnergy).cells) :
    i ∈ sector.cells ∧ SignedRatio.Equiv (model.energy i) energy :=
  ⟨(List.mem_filter.mp member).1, of_decide_eq_true (List.mem_filter.mp member).2⟩

/-- Fixed-particle admissibility for a closed canonical system. -/
def particleShell {model : FinitePhysicalModel states} (sector : model.Sector) (count : Nat)
    (witness : Fin sector.cells.length) (atCount : model.particles (sector.state witness) = count) : model.Sector :=
  sector.restrict (fun i => decide (model.particles i = count)) witness (decide_eq_true atCount)

theorem particleShell_exact {model : FinitePhysicalModel states} (sector : model.Sector) (count : Nat)
    (witness : Fin sector.cells.length) (atCount : model.particles (sector.state witness) = count)
    (i : Fin states) (member : i ∈ (sector.particleShell count witness atCount).cells) :
    i ∈ sector.cells ∧ model.particles i = count :=
  ⟨(List.mem_filter.mp member).1, of_decide_eq_true (List.mem_filter.mp member).2⟩

/-- The actual physical model for a canonical ensemble has a fixed particle
number, established by the computed sector rather than left implicit. -/
def canonicalModel {model : FinitePhysicalModel states} (sector : model.Sector) (count : Nat)
    (witness : Fin sector.cells.length) (atCount : model.particles (sector.state witness) = count) :
    FinitePhysicalModel (sector.particleShell count witness atCount).cells.length :=
  (sector.particleShell count witness atCount).asModel

theorem canonicalModel_particles {model : FinitePhysicalModel states} (sector : model.Sector) (count : Nat)
    (witness : Fin sector.cells.length) (atCount : model.particles (sector.state witness) = count)
    (i : Fin (sector.particleShell count witness atCount).cells.length) :
    (sector.canonicalModel count witness atCount).particles i = count :=
  (sector.particleShell_exact count witness atCount _ ((sector.particleShell count witness atCount).state_mem i)).2

/-- Closed microcanonical admissibility fixes both energy and particle
number within the prior sector, with an explicit admitted witness. -/
def closedShell {model : FinitePhysicalModel states} (sector : model.Sector) (energy : SignedRatio) (count : Nat)
    (witness : Fin sector.cells.length) (atEnergy : SignedRatio.Equiv (model.energy (sector.state witness)) energy)
    (atCount : model.particles (sector.state witness) = count) : model.Sector :=
  sector.restrict (fun i => decide (SignedRatio.Equiv (model.energy i) energy ∧ model.particles i = count)) witness
    (decide_eq_true ⟨atEnergy, atCount⟩)

theorem closedShell_exact {model : FinitePhysicalModel states} (sector : model.Sector) (energy : SignedRatio) (count : Nat)
    (witness : Fin sector.cells.length) (atEnergy : SignedRatio.Equiv (model.energy (sector.state witness)) energy)
    (atCount : model.particles (sector.state witness) = count) (i : Fin states)
    (member : i ∈ (sector.closedShell energy count witness atEnergy atCount).cells) :
    i ∈ sector.cells ∧ SignedRatio.Equiv (model.energy i) energy ∧ model.particles i = count :=
  ⟨(List.mem_filter.mp member).1, of_decide_eq_true (List.mem_filter.mp member).2⟩

/-- The uniform law is derived as the unique Shannon maximum on this
explicitly admissible physical sector. It has ordinary rational weights. -/
def uniform {model : FinitePhysicalModel states} (sector : model.Sector) : Distro (Fin states) := sector.grid.uniform sector.nonempty

theorem uniform_support {model : FinitePhysicalModel states} (sector : model.Sector) :
    sector.uniform.AlmostSurely (fun i => i ∈ sector.cells) := sector.grid.uniform_support sector.nonempty

theorem uniform_entropy {model : FinitePhysicalModel states} (sector : model.Sector) :
    ExactLog.Equiv (sector.uniform.entropy sector.grid sector.uniform_support)
      (ExactLog.log (PositiveRatio.ofNat sector.cells.length sector.nonempty)) := sector.grid.uniform_entropy sector.nonempty

theorem uniform_maximal {model : FinitePhysicalModel states} (sector : model.Sector) (law : Distro (Fin states))
    (support : law.AlmostSurely (fun i => i ∈ sector.cells)) :
    ExactLog.LE (law.entropy sector.grid support) (sector.uniform.entropy sector.grid sector.uniform_support) :=
  (ExactLog.le_congr (ExactLog.equiv_refl _) (ExactLog.equiv_symm sector.uniform_entropy)).mp
    (law.entropy_le_log_card sector.grid support sector.nonempty)

theorem uniform_unique {model : FinitePhysicalModel states} (sector : model.Sector) (law : Distro (Fin states))
    (support : law.AlmostSurely (fun i => i ∈ sector.cells))
    (maximal : ExactLog.Equiv (law.entropy sector.grid support) (sector.uniform.entropy sector.grid sector.uniform_support)) :
    law.SameLaw sector.uniform :=
  (law.entropy_eq_log_card_iff sector.grid support sector.nonempty).mp (ExactLog.equiv_trans maximal sector.uniform_entropy)

/-- The physical microcanonical law fixes energy and particle number within
the prior admissible sector. Maximality and uniqueness follow from the
uniform theorems on its explicitly computed closed shell. -/
def microcanonical {model : FinitePhysicalModel states} (sector : model.Sector) (energy : SignedRatio) (count : Nat)
    (witness : Fin sector.cells.length) (atEnergy : SignedRatio.Equiv (model.energy (sector.state witness)) energy)
    (atCount : model.particles (sector.state witness) = count) : Distro (Fin states) :=
  (sector.closedShell energy count witness atEnergy atCount).uniform

end Sector
end FinitePhysicalModel
end Thesis.Probability
