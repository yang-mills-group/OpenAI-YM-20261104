import YM.Integration.WilsonConditionalTaylorSceneCalibration
import YM.Integration.FVA1Physical.Round2.VacuumInvoice

/-! The finite-volume kinetic denominator is paid for every height and
period by the very pre-existing vacuum invoice on the selected run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorCaliperPayment

open Filter Lattice RG Precision MSbar MSbar.Heath MSbar.Midpoint
open PhysicalNext.Repeat.Legato Qlocal.Schedule WilsonConditionalTaylorSceneCalibration

variable {G : Gauge} (R : Run G) (u : G.ColorIndex) (V : Voice G)
  (paid : vacuumInvoice u V R.metals R.rolls R.alloy R.kit)

include paid in
theorem pulse (j n : ℕ) : Alto.Sampled (R.family.side j n) (R.family.path.levels.params j) := by
  have growth : Tendsto (fun m=>(R.alloy.B.a.params m).order) atTop atTop := by
    apply tendsto_atTop.2
    intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with k hk
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 k hk).1)
  exact ((paid.1 growth).levy.pulse j n)

include paid in
theorem denominator {N n k r : ℕ} {S : Scene R.family.path.levels n r}
    (scene : Realized R.alloy.B.kin N n k r (Lis.sun G u) S) (j : ℕ) (lo : k ≤ j) (hi : j ≤ N) :
    |caliper (R.family.side j n) (Lis.sun G u) (inkAt R N n j)+2|≤1 :=
  charged R scene j lo hi (pulse R u V paid j n)

end YM.Integration.WilsonConditionalTaylorCaliperPayment
end

