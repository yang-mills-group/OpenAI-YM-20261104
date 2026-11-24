import YM.Integration.WilsonThermometerWeakPastBlocks

/-! The actual reporter and its preceding ordinary weak date share a
fourth-power monitor on the funded logarithmic date window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakStarRatio
open Filter Set Lattice RG Push Trace.Terrace
open scoped Classical Topology
variable {G:Gauge} (A:Levels G)

private theorem double {x y:ℝ} (lower:2≤Real.log x) (mono:x≤y) (pos:0<x) (upper:y≤2*x):
    Real.exp ((Real.log (Real.log y))^2)≤ Real.exp ((Real.log (Real.log x))^2)^4:=by
  have yPos:=pos.trans_le mono
  have logbase:=Real.log_le_log pos mono
  have prices:=Real.log_le_log yPos upper
  rw [Real.log_mul (by norm_num) pos.ne'] at prices
  have two:Real.log 2≤1:=by have h:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num);norm_num at h;exact h
  have logx:0<Real.log x:=by linarith
  have logy:0<Real.log y:=logx.trans_le logbase
  have top:=Real.log_le_log logy (show Real.log y≤2*Real.log x by linarith)
  rw [Real.log_mul (by norm_num) logx.ne'] at top
  have bottom:=Real.log_le_log (by norm_num:0<(2:ℝ)) lower
  have first:0≤Real.log (Real.log x):=Real.log_nonneg (by linarith)
  have second:0≤Real.log (Real.log y):=Real.log_nonneg (by linarith)
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have square:=sq_le_sq₀ second (show 0≤2*Real.log (Real.log x) by positivity) |>.2
    (show Real.log (Real.log y)≤2*Real.log (Real.log x) by linarith only [top,bottom])
  norm_num
  nlinarith only [square]

theorem original (simple:G.Simple):∀ᶠ k:ℕ in atTop,∀ ℓ≥k,
    A.S.scale ℓ-A.S.scale k≤Real.log (A.clock.hatBeta ℓ) → A.clock.monitor ℓ≤A.clock.monitor k^4:=by
  have C:=Gauge.slopeConstant_pos simple
  have high:=hrate A simple
  have loghigh:=Real.tendsto_log_atTop.comp high
  have weak:∀ᶠ m:ℕ in atTop,0<A.clock.hatBeta m ∧
        ‖Real.log (A.clock.hatBeta m)‖ ≤ (1/(2*G.slopeConstant))*‖A.clock.hatBeta m‖ :=
    (high.eventually_gt_atTop 0).and (high.eventually (Real.isLittleO_log_id_atTop.bound (show 0<1/(2*G.slopeConstant) by positivity)))
  obtain ⟨m,ready⟩:=eventually_atTop.mp weak
  filter_upwards [eventually_ge_atTop m,loghigh.eventually_ge_atTop 2] with k hk floor ℓ hℓ gap
  obtain ⟨pos,logb⟩:=ready ℓ (hk.trans hℓ)
  simp only [Real.norm_eq_abs,abs_of_pos pos] at logb
  have rate:G.slopeConstant*Real.log (A.clock.hatBeta ℓ) ≤ A.clock.hatBeta ℓ/2:=by
    have same:2*G.slopeConstant*(1/(2*G.slopeConstant))=1:=by field_simp
    have h:=mul_le_mul_of_nonneg_left ((le_abs_self _).trans logb) (show 0≤2*G.slopeConstant by positivity)
    linarith only [h,congr_arg (fun r:ℝ=>r*A.clock.hatBeta ℓ) same]
  have state:=stamps A k ℓ
  change A.clock.hatBeta ℓ=A.clock.hatBeta k+G.slopeConstant*(A.S.scale ℓ-A.S.scale k) at state
  apply double floor (monoBeta A simple hℓ) (ready k hk).1
  linarith only [state,mul_le_mul_of_nonneg_left gap C.le,rate]

end YM.Integration.WilsonThermometerWeakStarRatio
end
