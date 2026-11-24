import YM.FVA2.Main
import YM.FVA2.PhysicalDeck

/-! Unit-shape ordinary OPE coefficients in the fixed position convention. The finite
far experiment uses the independently normalized Wilson correlations and its own Gram.
The target is computed from MS subtraction, the actual coupling and both field maps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMSDictionaryFarRead
open Filter Function Finset Lattice Maxwell XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater PowerSeries
open scoped Classical BigOperators Topology
variable {G : Gauge} (Z : WilsonPrescription G)
  (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν : ℝ)
local notation "W₀" => Measure.outlook Z.scheme Z.criterion
local notation "f₀" => Measure.f Z.criterion ν T
local notation "Z₀" => Measure.Z Z.scheme Z.criterion ν T
variable {hG : G.Simple} {σ : Prescription (Press.portDeck G)} {dial : Bool}
  (M : Main.Match Z hG T σ dial) {n h : ℕ}

/-- The inverse graded output frame acts after substitution in the diagram and every incoming mark. -/
def converted (u : Scan G n) (ψ : Test n) : Bill G :=
  refund (seats Z₀) (seats (replay Z₀)) f₀
    (fun v => Canon.Yield ψ (Canon.FarCoefficients (Equator.wave ν T) v)) u

include M in
theorem converted_eq (u : Scan G n) (ψ : Test n) :
    converted Z T ν u ψ = Canon.Yield ψ (Canon.FarCoefficients W₀ u) := by
  let contract := M.details.toServed.toPosted.toQuoted.toContract
  have gift := Canon.tested (u:=u) (ν:=ν) contract 0 ψ
  have out := M.separatedOPE ν
  simp only [out.continuum.start_u, out.wilson.start_u] at gift
  change credit (seats Z₀) f₀ (fun v => Canon.Yield ψ (Canon.FarCoefficients (Equator.wave ν T) v)) u =
    receipt (seats Z₀) (Canon.Yield ψ (Canon.FarCoefficients W₀ u)) at gift
  unfold converted refund
  rw [gift, timely, spin_v (Canon.office contract), receipt_K]

/-- The full inverse of the finite position-space exterior matrix is applied to its full product vector. -/
def nearby (P : Read.Geology G h) (u : Scan G n) (ψ : Test n) (s : ℝ) (b : Dframe.Toon G h) :=
  Read.FProg (GroupS.gaugeN Z.scheme Z.criterion T ν) (install W₀) P u s ψ b

def cutoff (q : ℕ) (t : ℝ) (row : PowerSeries ℂ) : ℂ :=
  ∑ k ∈ range (q+1), (t:ℂ)^k * coeff k row

include M in
theorem far (P : Read.Geology G h) (live : Read.Detected W₀ P) (u : Scan G n) (ψ : Test n)
    (b : Dframe.Toon G h) (q : ℕ) (t : ℝ) :
    Tendsto (fun s => cutoff q t (nearby Z T ν P u ψ s b)) atTop
      (𝓝 (cutoff q t (converted Z T ν u ψ (Dframe.flash b)))) := by
  rw [converted_eq Z T ν M]
  unfold cutoff
  apply tendsto_finsetSum
  intro k _
  exact tendsto_const_nhds.mul ((M.separatedOPE ν).wilson.kxcoeff P live u ψ b k)

end YM.Integration.WilsonMSDictionaryFarRead
