import YM.Integration.WilsonThermometerWardShoulderFunding
import YM.Integration.WilsonThermometerWardBareAperture

/-! The scale distance from any preparation within the booked short course
to its actual next bare source is sublogarithmic in the measured coupling. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardCloseSpan
open Filter Lattice Wilson RG RG16 QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "H" => R.alloy.B.a.clock.hatBeta

private theorem polylog (d:ℕ) {c δ:ℝ} (hc:0≤c) (hd:0<δ):
    ∀ᶠ x:ℝ in atTop,(c+1)*(Real.log x)^(d+1)≤(δ/8)*x:=by
  have fare:0<δ/(8*(c+1)):=by positivity
  have small:=(isLittleO_log_rpow_rpow_atTop ((d+1):ℝ) (by norm_num:0<(1:ℝ))).def fare
  filter_upwards [small,eventually_ge_atTop (1:ℝ)] with x order one
  have p:0≤x:=zero_le_one.trans one
  have l:0≤Real.log x:=Real.log_nonneg one
  change ‖Real.log x^((d+1):ℝ)‖≤δ/(8*(c+1))*‖x^(1:ℝ)‖ at order
  rw [←Nat.cast_add_one] at order
  have val:(Real.log x)^(d+1)≤δ/(8*(c+1))*x:=by
    simpa only [Real.rpow_natCast,Real.rpow_one,
      Real.norm_of_nonneg (pow_nonneg l _),Real.norm_of_nonneg p] using order
  refine (mul_le_mul_of_nonneg_left val (by linarith):(c+1)*(Real.log x)^(d+1)≤_).trans_eq ?_
  field_simp

theorem original (simple:G.Simple) (slow:∀n,((R.family.S.block n).val:ℝ)≤Real.log (Lambda (A) n))
    (degree:ℕ) {cap δ:ℝ} (cost:0≤cap) (width:0<δ):
    ∀ᶠ b:ℕ in atTop,∀j≤b,PaceR.Close R degree cap j b→∀N per,b<N→∀k:ℕ,j≤k→
      R.family.S.scale (b+1)-R.family.S.scale k≤δ*Real.log (regulatorRun R.family N per j)⁻¹:=by
  have grows:Tendsto H atTop atTop:=
    tendsto_const_nhds.add_atTop (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have scale:Tendsto (fun b=>2+Real.log (H b)) atTop atTop:=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp grows)
  filter_upwards [scale.eventually (polylog degree cost width),
    (Real.tendsto_log_atTop.comp scale).eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp grows).eventually_ge_atTop 2,grows.eventually_ge_atTop 16,
    PaceR.covers_hat R simple degree cap] with b earnings one warm hot window
  intro j jb close N per live k jk
  let z:=Real.log (2+Real.log (H b))
  have unit:1≤z:=one
  have h:(cap+1)*z^(degree+1)≤(δ/8)*(2+Real.log (H b)):=earnings
  have land:R.family.S.scale b-R.family.S.scale j≤cap*z^degree:=close
  have last:Real.log ((R.family.S.block b).val:ℝ)≤z:=
    (Real.log_le_self (by exact_mod_cast (R.family.S.block b).property.le)).trans (slow b)
  have prior:R.family.S.scale j≤R.family.S.scale k:=(OPE.scale_mono R.family.S).monotone jk
  have interval:R.family.S.scale (b+1)-R.family.S.scale k≤(cap+1)*z^(degree+1):=by
    rw [R.family.S.scale_succ]
    have ld:cap*z^degree≤cap*z^(degree+1):=mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ unit (Nat.le_succ _)) cost
    have st:z≤z^(degree+1):=by simpa using pow_le_pow_right₀ unit (show 1≤degree+1 by omega)
    rw [add_mul,one_mul]
    linarith only [prior,land,last,ld,st]
  let β:=R.family.path.β N per j
  let g:=regulatorRun R.family N per j
  have half:=window j j le_rfl jb close
  have lower:H j/2≤β:=(R.makes.wilson.represents N per j (jb.trans live.le)).band.1
  have b4:4≤β:=by linarith only [half,lower,hot]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (by linarith : 0<β))
  have relat:g⁻¹^2=β:=by change (((Real.sqrt β)⁻¹)⁻¹)^2=β;rw [inv_inv,Real.sq_sqrt (by linarith)]
  have square:H b≤g⁻¹^4:=by
    rw [show 4=2*2 by decide,pow_mul,relat]
    nlinarith only [half,lower,mul_nonneg (by linarith:0≤β) (by linarith:0≤β-4)]
  have logs:=Real.log_le_log (by linarith only [hot]:0<H b) square
  rw [Real.log_pow] at logs
  have temp:Real.log (H b)≤4*Real.log g⁻¹:=by simpa using logs
  change 2≤Real.log (H b) at warm
  have trade:(δ/8)*(2+Real.log (H b))≤δ*Real.log g⁻¹:=by
    calc
      _≤(δ/8)*(2*(4*Real.log g⁻¹)):=mul_le_mul_of_nonneg_left (by linarith only [warm,temp]) (by positivity)
      _=_:=by ring
  exact interval.trans (h.trans trade)

end YM.Integration.WilsonThermometerWardCloseSpan
