import YM.Integration.WilsonMixedTaggedUnweight
import YM.Integration.WilsonMixedTaggedMeasuredWindow

/-! Use a previously chosen reporting depth for both output arrays. The
fixed quota date is eventually below the original crossing predecessor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedSpend
open Filter Finset Function Lattice Wilson RG Marker RG05Readout Many OPE
open Push AbsoluteSums Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical

theorem chosen {G:Gauge}{n:Side}{I V:Type}[Fintype I][DecidableEq V]{J:Census V}
    {S:I → Support n}{F:I → Config G n → Poly J}{B:ℕ}{α δ c E A:ℝ}{w:V → ℝ}
    (bank:Towed w S F B α δ) (wp:∀v,0 < w v) (dp:0 < δ) (cp:0 ≤ c) (ep:0 ≤ E)
    (cap:δ ≤ c*A) (bought:∀s:J.Mode,A ≤ E*Poly.toll w s) :
    Towed (fun _:V=>(1:ℝ)) S F B α (c*E) := by
  apply WilsonMixedTaggedUnweight.original bank wp dp (mul_nonneg cp ep)
  intro i U s _
  simpa only [mul_assoc] using cap.trans (mul_le_mul_of_nonneg_left (bought s) cp)

theorem lower {G:Gauge} (R:Run G) :
    Tendsto (fun r:ℝ=>RG05Readout.crossLevel R.family.S r-1-1) (𝓝[>] (0:ℝ)) atTop := by
  have zoom:Tendsto (fun r:ℝ=>OPE.run r) (𝓝[>] (0:ℝ)) atTop := by
    simpa only [Function.comp_def,Real.log_inv,OPE.run] using
      (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have physical:RateIs (𝓝[>] (0:ℝ)) OPE.run id (-1) := OPE.loglife tendsto_id
  have finish:=RG05Readout.pace_crossing R.family.path.levels.fits.mesh zoom physical
  apply Filter.tendsto_atTop.2
  intro n
  filter_upwards [finish.1.grows.eventually_ge_atTop (n+2)] with r hr
  change n+2 ≤ RG05Readout.crossLevel R.family.S r at hr
  change n ≤ RG05Readout.crossLevel R.family.S r-1-1
  omega

end YM.Integration.WilsonMixedTaggedSpend
