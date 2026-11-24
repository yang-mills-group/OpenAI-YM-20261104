import YangMills.OPECoefficientLaws
import YangMills.PhysicalOPE.PowerTrees
import YangMills.CutoffTrajectory
import YangMills.FiniteVolume
import YangMills.Phases
import YangMills.ShortDistance
import YangMills.VacuumReconstruction

/-! The continuum limit of four-dimensional Wilson Yang–Mills theory. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open Filter Set
open scoped Topology

namespace Wilson

/-- All continuum assertions refer to the hierarchy obtained from these volumes
and to the same microscopic insertions. -/
structure ContinuumLimit {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g}
    (lattice : WilsonData B C) (values : PeriodPointTable C)
    (volumes : ℕ → ℕ) (T : Hierarchy C) : Prop where
  smeared : C.Converges volumes (fun v => T.correlation none (T.project ∘ v))
  pointwise (n : ℕ) (v : Fin n → C.Token) (K : Set (Points n)) :
    IsCompact K → K ⊆ separated n → ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
      dist (periodValue values (volumes k) v z) (T.correlation none (T.project ∘ v) z) < ε
  reconstruction : T.Reconstructed
  fieldSpace : Reconstruction.TableLaws T
  vacuumSectors : Nonempty (Reconstruction.Phases T)
  adjoints : lattice.AdjointOn T
  phaseCorrelations : ObservablePhases.Law lattice T
  ope : T.OperatorProductExpansion
  coefficients : T.CoefficientLaws
  fusionTrees : T.PowerTreeExpansion
  ward : Nonempty T.StressWardLaws
  trace : T.TraceTest
  ultraviolet : ∃ coordinates : ShortDistance.Coordinates B T, ShortDistance.MaxwellLimit B T coordinates

/-- Fix the lattice fields and their finite-volume point values before choosing
a sequence of volumes. Every such sequence admits the indicated continuum limit. -/
def Construction.Realizes {g : GaugeGroup} (run : Construction g) (B : Maxwell.Reference g) : Prop :=
  WilsonTrajectory B run.family ∧
  ∃ (lattice : WilsonData B run.family) (values : PeriodPointTable run.family),
    FixedPointReturns run.family values ∧ ∀ (p : ℕ → ℕ) (increasing : StrictMono p),
      let limit := run.refine p increasing
      ContinuumLimit lattice values (p ∘ limit.indices) limit.hierarchy

end Wilson
end YangMills
