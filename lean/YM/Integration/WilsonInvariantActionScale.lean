import YM.TraceExtension.Link.Rad

/-! Physical powers in the exact dimension-four trace calibration are
smaller than every perturbative power on its actual Wilson coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionScale
open Filter Function Asymptotics Trace.Pilot Trace.Over
open scoped Topology
variable {G : Gauge}

private theorem physical_log (k : ℕ) :
    Tendsto (fun r : ℝ=>r^4*(LogV r)^k) trail (𝓝 0) := by
  have core := (Real.isLittleO_pow_log_id_atTop (n:=k)).tendsto_div_nhds_zero.comp
    (tendsto_inv_nhdsGT_zero (𝕜:=ℝ))
  have small : Tendsto (fun r:ℝ=>r^3) trail (𝓝 0) := by
    simpa using ((show Tendsto (fun r:ℝ=>r) trail (𝓝 0) from nhdsWithin_le_nhds).pow 3)
  have out:=small.mul core
  rw [mul_zero] at out
  apply out.congr
  intro r
  change r^3*(Real.log r⁻¹^k/r⁻¹)=_
  simp only [LogV,div_eq_mul_inv,inv_inv]
  ring

theorem flat (simple : G.Simple) {g δ : ℝ→ℝ} (coupling : Coupling G g)
    (trace : Tendsto (fun r=>LogV r*(4*δ r)) trail (𝓝 (-1))) (q : ℕ) :
    Tendsto (fun r=>(r^4/(4*δ r))/(g r)^q) trail (𝓝 0) := by
  have den:=trace.mul (coupling.running.pow q)
  have hs : G.slopeConstant≠0 := (Gauge.slopeConstant_pos simple).ne'
  have hz : (-1:ℝ)*(G.slopeConstant⁻¹)^q≠0:=mul_ne_zero (by norm_num) (pow_ne_zero _ (inv_ne_zero hs))
  have out:=(physical_log (q+1)).div den hz
  rw [zero_div] at out
  have top:=(coupling.conforms simple).pow q
  have product:=out.mul top
  rw [zero_mul] at product
  apply product.congr'
  have logpos : Tendsto LogV trail atTop:=Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  filter_upwards [coupling.positive,logpos.eventually_gt_atTop 0,trace.eventually_ne (by norm_num : (-1:ℝ)≠0)]
    with r hg hl hδ
  change LogV r*(4*δ r)≠0 at hδ
  have dd : 4*δ r≠0 :=right_ne_zero_of_mul hδ
  change r^4*(LogV r)^(q+1)/(LogV r*(4*δ r)*(LogV r*(g r)^2)^q)*(g r)^q=_
  rw [mul_pow,pow_succ (LogV r) q,←pow_mul,Nat.mul_comm 2 q,pow_mul]
  field_simp [hg.ne',hl.ne',dd]

end YM.Integration.WilsonInvariantActionScale
