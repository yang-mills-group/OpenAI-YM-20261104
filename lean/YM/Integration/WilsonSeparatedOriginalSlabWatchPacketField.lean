import YM.Integration.WilsonSeparatedOriginalSlabWatchPacket
import YM.Integration.WilsonSeparatedOriginalSlabWatchRaw

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchPacketField
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Lattice Wilson Next.UVStress RG05Readout.Pulse
open WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchBorn
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{I:Type}[Fintype I]

theorem physical (F:Final C f S)(W:Watch C)(s:I→ℕ)(a:(i:I)→S.Field (s i))(r:ℝ)(K:Set (Points (Fintype.card I)))
    (live:∀y∈K,joined W (native (r • y))∈conf _):
    ContinuousOn (fun y=>watch W s a (r • y)) K:=by
  have sc:Continuous (fun y:Points (Fintype.card I)=>r • y):=continuous_const_smul r
  exact (WilsonSeparatedOriginalSlabWatchRaw.continuous F (panel W s a ∘runNames _)).comp ((joined_continuous W).comp (native_continuous.comp sc)).continuousOn live

theorem calibration (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s:I→ℕ)(a:(i:I)→S.Field (s i))(h:ℕ)(r:ℝ)(K:Set (Points (Fintype.card I)))
    (safe:∀y∈K,∀j≤h,orbitMargin R.port j (native (r • y)) 0):
    ContinuousOn (fun y=>R.packet h (native (r • y)) a 0) K:=by
  intro y hy;apply ContinuousAt.continuousWithinAt
  have sc:Continuous (fun y:Points (Fintype.card I)=>r • y):=continuous_const_smul r
  have input:Continuous (fun w:Points (Fintype.card I)=>(native (r • w),(0:E4))):=(native_continuous.comp sc).prodMk (show Continuous (fun _:Points (Fintype.card I)=>(0:E4)) from continuous_const)
  unfold Reader.packet
  exact tendsto_finsetSum _ (fun (j:Fin (h+1)) _=>(LinearMap.toContinuousLinearMap (F.sector.derivatives.rise (d:=j.val) (Nat.le_of_lt_succ j.isLt))).continuous.continuousAt.comp (((R.fresh_smooth j.val (native (r • y)) 0 a (safe y hy j.val (Nat.le_of_lt_succ j.isLt))).continuousAt).comp (f:=fun w:Points (Fintype.card I)=>(native (r • w),(0:E4))) input.continuousAt))

end YM.Integration.WilsonSeparatedOriginalSlabWatchPacketField
