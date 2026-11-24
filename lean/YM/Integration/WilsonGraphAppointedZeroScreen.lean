import YM.Integration.WilsonPositionPrescribedScreen
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedScreen
open Function Filter Set Finset MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ→PhysMS.tower S)


theorem correctionAtZero (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ)
    (solved : ∀ᶠ r in Trace.Pilot.trail,
      Fray.SetEq (V.measure d) 0 (hierarchy F J d r)) :
    ∀ᶠ r in Trace.Pilot.trail, correction F J V d r = 0 := by
  have near : Tendsto (fun _ : ℝ => guide G d (0 : Change G d))
      Trace.Pilot.trail (𝓝 0) := by
    simp only [map_zero]
    exact tendsto_const_nhds
  filter_upwards [unique F J lead V d (fun _ => 0) near, solved] with r localRule zeroFits
  exact localRule.mp zeroFits

theorem slopeAtZero (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ)
    (solved : ∀ᶠ r in Trace.Pilot.trail,
      Fray.SetEq (V.measure d) 0 (hierarchy F J d r)) :
    ∀ᶠ r in Trace.Pilot.trail, Bijective (slope (V.measure d) 0 (hierarchy F J d r)) := by
  filter_upwards [(original F J lead V d).2, correctionAtZero F J lead V d solved]
    with r checks correction
  simpa only [correction] using checks.2.2

theorem zeroIsUnique (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ)
    (solved : ∀ᶠ r in Trace.Pilot.trail, Fray.SetEq (V.measure d) 0 (hierarchy F J d r))
    (b : ℝ → Change G d)
    (near : Tendsto (fun r => guide G d (b r)) Trace.Pilot.trail (𝓝 0)) :
    ∀ᶠ r in Trace.Pilot.trail, Fray.SetEq (V.measure d) (b r) (hierarchy F J d r) ↔ b r = 0 := by
  filter_upwards [unique F J lead V d b near, correctionAtZero F J lead V d solved]
    with r localRule correction
  simpa only [correction, eq_comm] using localRule

end YM.Integration.WilsonPositionPrescribedScreen
