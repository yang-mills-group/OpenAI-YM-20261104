import YM.Integration.WilsonPositionProgramSubmittedProgram
import YM.FVA2.Notch.Quiz
import YM.FVA2.Notch.Card

/-! On the true position mesh, one-sixteenth clearance supplies the original
finite Wilson registry with the same signed MS trajectory and trial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramOriginalTrial
open Function Filter Set Finset Metric MeasureTheory Real Lattice MS MS.High
open MS.Book MS.Book.Convolve MS.Tone MS.Tide MS.Rake MS.Land MS.Dial MS.Orbit MS.Fleet MS.Vista
open XSpace.Cirrus XSpace.Expense FVA2.Notch FVA2.Arrival FVA2.Arrival.Schedule
open scoped Topology Classical
open private permit from YM.FVA2.Notch.Cover
variable {n : ℕ} (K : Set (Points n)) (compact : IsCompact K) (away : K⊆conf n) (μ : ℝ)
local notation "ρ" => (1/16:ℝ)
local notation "T" => Flight.trail ρ K μ

theorem cleared : Clearance (Flight.trail ρ K μ).side (Flight.trail ρ K μ).head := by
  intro j b
  change (periodN (psi j.sample.F)).val ≤ 16 * pdist (wrap (periodN (psi j.sample.F)) (Lattice.lift (wrap (periodN (psi j.sample.F)) j.peg))-thin (psi j.sample.F) b)
  rw [wrap_lift]
  have h := (permit j).choose_spec.1 b
  change min ρ ρ * ((periodN (psi j.sample.F)).val:ℝ) ≤ (pdist (wrap _ j.peg-thin _ b):ℝ) at h
  rw [min_self] at h
  exact_mod_cast (show ((periodN (psi j.sample.F)).val:ℝ) ≤ 16*(pdist (wrap _ j.peg-thin _ b):ℝ) by linarith)

include compact away in
theorem uses : Dial.Uses (Flight.trail ρ K μ) (FVA2.Notch.Pitch.go ρ K) μ := by
  have h := Flight.worthy compact (show (0:ℝ)<ρ by norm_num) away μ
  exact ⟨h.total,h.knit,h.reality,Pitch.pending (r:=ρ) (K:=K) μ,Pitch.grows (r:=ρ) (K:=K) μ,cleared K μ,h.wind⟩

end YM.Integration.WilsonPositionProgramOriginalTrial
