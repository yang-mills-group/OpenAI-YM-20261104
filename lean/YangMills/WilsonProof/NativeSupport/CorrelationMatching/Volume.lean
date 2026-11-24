import YangMills.LatticeSections
import YangMills.LatticeFields
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy
import YangMills.WilsonProof.NativeSupport.OriginalPointReturns
import YangMills.WilsonProof.NativeSupport.WilsonBridge
import YM.FullVolume.Profiles

/-! Continuum limits of the original periodic Wilson measurements. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.CorrelationMatching

open Filter MeasureTheory Set
open scoped Topology

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The raw coordinates used to lift continuum fields are the coefficient
vectors of the original graded lattice insertions, in their original order. -/
def NativeCoordinates {B : Maxwell.Reference g} (lattice : YM.Family g.core)
    (data : Wilson.WilsonData B (wilsonFamily lattice)) : Prop :=
  ∃ widths : ∀ d, data.raw.width d = (lattice.labels.level d).extra + 1,
    ∀ (d : ℕ) (v : Wilson.RawSpace (data.raw.width d)),
      data.raw.token ⟨d, v⟩ = ⟨d, fun i => v (Fin.cast (widths d).symm i)⟩

/-- The Wilson family admits smooth fixed-period kernels on configurations separated
modulo that period. Every finite-difference stencil converges along the full mesh
sequence at approaching lattice sites, by interpolation, and against suitable tests. -/
def SmoothMeshLimit {B : Maxwell.Reference g} (data : Wilson.WilsonData B C) : Prop :=
  ∃ lattice : YM.Family g.core, ∃ same : wilsonFamily lattice = C,
    lattice.Makes ∧ YM.FullVolume.PositionsUV lattice YM.Extraction.Sequence.full ∧
      NativeCoordinates lattice (same.symm ▸ data)

/-- Locally uniform infinite-volume limit of one fixed-period kernel table on
the indicated refinement, for every finite tuple of original lattice insertions. -/
def PeriodLimit (kernels : Wilson.PeriodPointTable C) (T : Hierarchy C)
    (periods : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (labels : Fin n → C.Token) (K : Set (Points n)),
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
      dist (Wilson.periodValue kernels (periods k) labels x)
        (T.correlation none (T.project ∘ labels) x) < ε

abbrev TestTable (C : WilsonFamily g) :=
  (n : ℕ) → (Fin n → C.Token) → SeparatedTest n → ℂ

/-- At every suitable period take the full ultraviolet limit of the smeared Wilson
moment, then take the volume limit on the requested sequence of periods. -/
def HasTestLimits (C : WilsonFamily g) (periods : ℕ → ℕ) (L : TestTable C) : Prop :=
  ∀ (n : ℕ) (labels : Fin n → C.Token) (t : SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (periods k) t) ∧ ∃ row : ℕ → ℂ,
      (∀ m, C.suitable m t →
        Tendsto (fun N => C.smear N m labels t) atTop (𝓝 (row m))) ∧
      Tendsto (fun k => row (periods k)) atTop (𝓝 (L n labels t))

/-- The hierarchy on a refinement represents every joint table that already
converges on the requested volume sequence. -/
def RepresentsTestLimits (T : Hierarchy C) (requested : ℕ → ℕ) : Prop :=
  ∀ L : TestTable C, HasTestLimits C requested L →
    ∀ (n : ℕ) (labels : Fin n → C.Token) (t : SeparatedTest n),
      L n labels t = ∫ x, t x * T.correlation none (T.project ∘ labels) x

/-- Every finite tuple in the measured frame, at each radius, lifts to a tuple
of original Wilson insertions. Its period and tested limits are therefore read
from the same kernels as all other Wilson moments. -/
def RealizesInputs (T : Hierarchy C) {B : Maxwell.Reference g}
    (frame : (r : ℝ) → (d : ℕ) → B.sector d ≃ₗ[ℂ] T.Field d) : Prop :=
  ∀ (r : ℝ) (n : ℕ) (d : Fin n → ℕ) (v : (i : Fin n) → B.sector (d i)),
    ∃ labels : Fin n → C.Token,
      T.project ∘ labels = fun i => ⟨d i, frame r (d i) (v i)⟩

/-- For the declared raw coordinates, every measured column is read using one
unique linear section per grade. The same section is used at every radius. -/
theorem realizedInputs {B : Maxwell.Reference g} {D : Wilson.WilsonData B C} {T : Hierarchy C}
    (adjoint : D.AdjointOn T) (frame : (r : ℝ) → (d : ℕ) → B.sector d ≃ₗ[ℂ] T.Field d) :
    RealizesInputs T frame := by
  choose lift property _ using fun d => adjoint.orthogonalSection d
  intro r n d v
  exact ⟨fun i => D.raw.token ⟨d i, (lift (d i) (frame r (d i) (v i))).ofLp⟩,
    funext fun i => (property (d i) (frame r (d i) (v i))).1⟩

end YangMills.CorrelationMatching
end
