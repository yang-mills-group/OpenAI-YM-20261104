import YM.Integration.WilsonCoherentClockDebit
import YM.Extra.WILSON_STARTUP.Fast
import YM.Pert.Asymptotics.RawAxis

/-! The true temperature at a populated inner date falls within the original
spool aperture at the preceding date, for every later upper cutoff. The
functional evaluated here is the issued single Wilson sheet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentInheritedSpool
open Filter Real Lattice Wilson RG Tree Precision ConnectedActivityE6
open RGComparison.Core16 RGComparison.Core16.Lumen PertExtension.Series.Tested FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology
variable {G:Gauge} (R:Run G)

theorem temperature (simple:G.Simple) (i N per:ℕ) (live:i+1≤N):
    let β:=R.family.path.β N per (i+1)
    let g:=regulatorRun R.family N per (i+1)
    g=Coat.gStep β ∧ 0<g ∧ g≤(sqrt (R.family.path.levels.clock.hatBeta i/2))⁻¹:=by
  let a:=R.family.path.levels
  let β:=R.family.path.β N per (i+1)
  have pos:0<a.clock.hatBeta i/2:=half_pos (zero_lt_one.trans (a.fits.delayed i))
  have rising:=WilsonStartup.Timing.hat_mono a (Gauge.slopeConstant_pos simple).le (Nat.le_succ i)
  have scale:a.clock.hatBeta i/2≤β:=(div_le_div_of_nonneg_right rising (by norm_num)).trans
    (R.makes.wilson.represents N per (i+1) live).band.1
  exact ⟨rfl,inv_pos.mpr (Real.sqrt_pos.mpr (pos.trans_le scale)),
    inv_anti₀ (Real.sqrt_pos.mpr pos) (Real.sqrt_le_sqrt scale)⟩

theorem branch (i:ℕ) :
    (WilsonCoherentFiniteIssue.stagePatch R i).Branches R.family.path.levels.clock.kernel G :=
  (R.family.path.levels.blocks i 0).branches

theorem measured (simple:G.Simple) (i N per:ℕ) (live:i+1≤N) {I:Type} [Fintype I] (J:I→Spool.Lamp G)
    {P:Parcel.Oven (WilsonCoherentFiniteIssue.stagePatch R i)} (X:P.Form G) {U:Lumen.Stage}
    {r:ℕ} {C:ℝ} (allowed:(sqrt (R.family.path.levels.clock.hatBeta i/2))⁻¹≤Forge.dollar U.L)
    (cost:C≤2+log (R.family.path.levels.clock.hatBeta i))
    (paid:P.Offers X R.family.path.levels.clock.kernel)
    (large:Bid.Larger (G:=G) (R.family.path.levels.clock.op i per))
    (T:Forest (R.family.path.levels.clock.op i per).ratio)
    (u:Pins G (R.family.side i per)) (o:I→Site (R.family.side (i+1) per)) (inside:∀a,‖u a‖≤X.Q)
    (money:Spool.Price U r C (Spool.rank J (R.family.path.levels.clock.op i per) T X
       (Next.Foundations.chart G) u o) (Spool.reads J (R.family.path.levels.clock.op i per) u o))
    (tag:(R.family.path.levels.clock.op i per).Choices) (v:(Descent.nil (top:=R.family.side (i+1) per)).Tags):
    let D:=R.family.path.levels.clock.op i per
    let g:=regulatorRun R.family N per (i+1)
    ‖Spool.reads J D u o g-peval (WilsonCoherentJointReturn.series J D T R.metals.O u o large tag v) r g‖
      ≤g^(r+1)*(2+log (R.family.path.levels.clock.hatBeta i)):=by
  obtain ⟨_,hot,cap⟩:=temperature R simple i N per live
  have recorded:=WilsonCoherentClockDebit.measured J (R.family.path.levels.clock.op i per) X
    (Next.Foundations.chart_ok G) R.alloy.B.ratio large T T u o paid inside money tag v hot (cap.trans allowed)
  exact recorded.trans (mul_le_mul_of_nonneg_left cost (pow_nonneg hot.le _))

end YM.Integration.WilsonCoherentInheritedSpool
