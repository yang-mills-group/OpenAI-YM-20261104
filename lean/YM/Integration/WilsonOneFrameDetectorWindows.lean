import YM.Integration.WilsonOneFrameFixedReadings
import YM.Next.UV_STRESS.Focus

/-! All finite compact windows needed by the derivative detector, on the
original sequence of radii with the measured homogeneous columns. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOneFrameDetectorWindows
open Filter Set Function Lattice Wilson RG Source OPE Spec Table Climb Ward Maxwell PhysMS Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonOneFrameFixedReadings (ruler)
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)
    (radii:Scaling S)

include lead owed simple in
theorem original (N D m : ℕ) (B : ℝ) (positive : 0 < B) :
    (ruler F J Z radii).jets N D m B := by
  intro n _ j _ v _ ε ep
  have along : Tendsto radii.r atTop trail :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ radii.drips (Eventually.of_forall radii.positive)
  exact along.eventually (WilsonPositionHomogeneousLeading.jets F J Z lead owed simple (fun i => (v i).1)
    (fun i => (v i).2) j (window_closed B n) (fun _ hx => spaced_conf (inv_pos.mpr positive) hx.1) ep)

end YM.Integration.WilsonOneFrameDetectorWindows
end
