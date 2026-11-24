import YM.Integration.WilsonCoherentMayerWindingTemperature

/-! The true block size and a regulator floor independent of the upper date and period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerWindingGeometry
open RG ConnectedActivityE6 PhysicalNext.Repeat.Legato
variable {G:Gauge} (R:Run G)

theorem count (i per:ℕ):
    (R.family.path.levels.clock.op i per).ratio.count.val=(R.family.S.block i).val:=rfl

def floor (i:ℕ):ℝ:= (Real.sqrt (2*R.alloy.B.a.clock.hatBeta i))⁻¹

theorem lower (N per i:ℕ)(cut:i≤N):
    0< floor R i ∧ floor R i ≤ Coat.gStep (R.family.path.rep N per i).beta:=by
  let x:=R.alloy.B.a.clock.hatBeta i
  let β:=(R.family.path.rep N per i).beta
  have hx:0<x:=lt_trans zero_lt_one (R.alloy.B.a.fits.delayed i)
  have band:= (R.makes.wilson.represents N per i cut).band
  have lo: x/2≤β:=band.1
  have hi: β≤2*x:=band.2
  change 0<(Real.sqrt (2*x))⁻¹ ∧ (Real.sqrt (2*x))⁻¹≤(Real.sqrt β)⁻¹
  exact ⟨by positivity,inv_anti₀ (Real.sqrt_pos.mpr ((half_pos hx).trans_le lo)) (Real.sqrt_le_sqrt hi)⟩

end YM.Integration.WilsonCoherentMayerWindingGeometry
