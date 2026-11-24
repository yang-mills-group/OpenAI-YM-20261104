import YM.Integration.FVA1Physical.Round2.MeasuredFieldFee
import YM.Integration.FVA1Physical.Marked.CurrentRunField
import YM.MSbar.Geneva.Snow
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term

/-! A fixed field-coordinate ball is genuinely inside the strict physical
regular domain, uniformly over all admitted periodic lattices and cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Lattice RG YM.Wilson Precision PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Mosaic
open MSbar.Rolling MSbar.Wave Push.Uniform AnalyticBridge.SectorAffine.Offset
open YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology

theorem chart_strict {G:Gauge} {c:Side} (B:BudgetPoint) (V:Voice G) (clear:Clear G V)
    (z:Positions (Primary c G)) (depth:shade G*‖z‖ ≤ V.r)
    (price:V.C*(shade G*‖z‖) ≤ B.threshold/8) : palace z∈Boulevard.sunny B := by
  have calmEnough:palace z∈RG.calm G c (B.threshold/2):=by
    intro e _
    let a:=panel G c z e
    have size:‖a‖ ≤ shade G*‖z‖:=pain z e
    have est: G.chord (G.lieExp a) ≤ V.C*‖a‖:=(clear.small a (size.trans depth)).2
    change G.chord (palace z e) ≤ (B.threshold/2)/4
    rw [show palace z e=G.lieExp a by change G.lieExp a*1=_;rw [mul_one]]
    exact (est.trans ((mul_le_mul_of_nonneg_left size (zero_le_one.trans clear.cost)).trans price)).trans_eq (by ring)
  exact fun i=>(faceBound calmEnough i).trans_lt (half_lt_self B.threshold_pos)

theorem regular_field_domain {G:Gauge} (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (V:Voice G) (clear:Clear G V) (D:ℝ) (hD:0 ≤ D) :
    ∀ᶠ k:ℕ in atTop,∀ N n j,k ≤ j → j < N →
      let H:=R.family.path
      let g:=cue (H.rep N n (j+1)).beta
      ∀ z:Positions (Primary (R.family.side j n) G),‖z‖ ≤ D → 
        ‖g•z‖ < 1 ∧ palace (g•z)∈Boulevard.sunny (H.rep N n j).p := by
  let H:=R.family.path
  let a:=H.levels
  let c:=a.clock
  let t:=min (1/2:ℝ) (V.r/(1+shade G))
  have shade0:= (shade_pos G).le
  have sp:0 < 1+shade G:=by linarith only [shade0]
  have tp:0 < t:=lt_min (by norm_num) (div_pos clear.depth sp)
  have dp:0 < D+1:=by linarith only [hD]
  have clocks:=actual_clock_small H (q:=1) zero_lt_one (div_pos tp dp) hG R.T.choice
  have grows:=Multi.Wage.hat_tend hG a
  have monitors:Tendsto c.monitor atTop atTop:=Real.tendsto_exp_atTop.comp
    ((tendsto_pow_atTop (n:=2) (by norm_num)).comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp grows)))
  obtain ⟨k₀,cover⟩:=eventually_atTop.mp (monitors.eventually_ge_atTop (16*V.C*shade G*D))
  filter_upwards [clocks,eventually_ge_atTop k₀] with k small cut N n j kj hj
  intro H' g z hz
  let x:=c.hatBeta j
  let y:=c.hatBeta (j+1)
  have hx:0 < x:=zero_lt_one.trans (a.fits.delayed j)
  have hy:0 < y:=zero_lt_one.trans (a.fits.delayed (j+1))
  have band: y/2 ≤ (H.rep N n (j+1)).beta ∧ (H.rep N n (j+1)).beta ≤ 2*y:=(R.T.choice.represents N n (j+1) hj).band
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos hy).trans_le band.1))
  have up:g ≤ 2*cue x:=(Mosaic.ever hy band.1 band.2).2.trans (mul_le_mul_of_nonneg_left
    (inv_anti₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt (WilsonBulk.Parapet.Agenda.hat_mobile a hG (Nat.le_succ j)))) zero_le_two)
  have use:=small (j+1) (kj.trans (Nat.le_succ j)) N n hj
  change g^(1:ℝ) ≤ t/(D+1) at use
  rw [Real.rpow_one] at use
  have norm_bound:‖g•z‖ ≤ g*D := by rw [norm_smul,Real.norm_of_nonneg gp.le];gcongr
  have scaled:‖g•z‖ ≤ t:=norm_bound.trans ((mul_le_mul_of_nonneg_left (by linarith only [hD] : D ≤ D+1) gp.le).trans
    ((le_div_iff₀ dp).mp use))
  refine ⟨scaled.trans_lt ((min_le_left ..).trans_lt (by norm_num)),chart_strict _ V clear _ ?_ ?_⟩
  · calc
      _ ≤ (1+shade G)*t := mul_le_mul (le_add_of_nonneg_left zero_le_one) scaled (norm_nonneg _) sp.le
      _ ≤ V.r := by rw [mul_comm];exact (le_div_iff₀ sp).mp (min_le_right ..)
  · have bound:V.C*(shade G*‖g•z‖) ≤ V.C*(shade G*((2*cue x)*D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_bound.trans (mul_le_mul_of_nonneg_right up hD)) shade0)
        (zero_le_one.trans clear.cost)
    have paid:=mul_le_mul_of_nonneg_left (cover j (cut.trans kj)) (show 0 ≤ cue x from inv_nonneg.mpr (Real.sqrt_nonneg _))
    have same:(H'.rep N n j).p=a.budget j:=(R.T.choice.represents N n j hj.le).vac
    rw [same]
    change _ ≤ (cue x*c.monitor j)/8
    nlinarith only [bound,paid]

end YM.Integration.FVA1Physical.Round2.Curvature
