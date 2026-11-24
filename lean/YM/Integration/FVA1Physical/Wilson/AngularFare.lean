import YM.Integration.FVA1Physical.Wilson.FluctuationChart
import YM.OPE.Therm.Rite

/-! A strictly subthermal plaquette cutoff still pays any inverse coupling power after
one block of the genuine reflection estimate. The onset depends only on stage data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Lattice RG Next.Rank MSbar.Heath.Stock MSbar.Heath.Cottage
open scoped Topology

def angularCut (x:ℝ) : ℝ := cue x * Real.log x * Real.sqrt (Real.sqrt (Real.log x))

theorem angular_fare (G:Gauge) (B:Stage) (L:Side) (K:ℕ) :
    ∀ᶠ x:ℝ in atTop,∀ g:ℝ,0<g → g ≤ 2*cue x →
      Real.exp ((L.val:ℝ)^4*(Vac.fiat G B x+Fintype.card PlaqAxes) -
        angularCut x/(g/strength B.clip)) ≤ (x⁻¹)^K := by
  let A:=Vac.fiat G B 1+(Fintype.card PlaqAxes:ℝ)
  let c:=(L.val:ℝ)^4*(|A|+2*Module.finrank ℝ G.Mat)+(K:ℝ)
  let b:=strength B.clip
  have c0:0 ≤ c := by dsimp only [c]; positivity
  have bp:0<b:=strength_pos _
  have grow:=Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,grow.eventually_ge_atTop (2*c/b),
    eventually_gt_atTop (0:ℝ)] with x hlog far hx g hg high
  let t:=Real.log x
  let u:=Real.sqrt (Real.sqrt t)
  have t0:0 ≤ t := zero_le_one.trans hlog
  have lin:Vac.fiat G B x+Fintype.card PlaqAxes=A+2*Module.finrank ℝ G.Mat*t:=by
    dsimp only [A,t,Vac.fiat];rw [Real.log_one];ring
  have hA:A≤|A| *t:=(le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
  have cost:(L.val:ℝ)^4*(Vac.fiat G B x+Fintype.card PlaqAxes)+(K:ℝ)*t ≤ c*t:=by
    rw [lin];dsimp only [c];calc
      _ ≤ (L.val:ℝ)^4*(|A| *t+2*Module.finrank ℝ G.Mat*t)+(K:ℝ)*t := by
        nlinarith only [mul_le_mul_of_nonneg_left hA (show 0 ≤ (L.val:ℝ)^4 by positivity)]
      _ = _ := by ring
  have power:2*c ≤ u*b := (div_le_iff₀ bp).mp far
  have paid:c*t ≤ angularCut x/(g/b):=by
    rw [div_div_eq_mul_div,le_div_iff₀ hg]
    calc
      _ ≤ c*t*(2*cue x):=mul_le_mul_of_nonneg_left high (mul_nonneg c0 t0)
      _ = cue x*t*(2*c):=by ring
      _ ≤ cue x*t*(u*b):=mul_le_mul_of_nonneg_left power
        (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) t0)
      _ = angularCut x*b:=by unfold angularCut;dsimp only [t,u];ring
  calc
    _ ≤ Real.exp (-((K:ℝ)*t)):=Real.exp_monotone (by linarith only [cost,paid])
    _ = _:=by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hx,inv_pow]

/-- Every fixed constant times the plaquette cutoff lies strictly inside the actual thermal
chart width. Translation or source placement has no effect on this estimate. -/
theorem angular_below_thermal (C:ℝ) : ∀ᶠ x:ℝ in atTop,C*angularCut x < MSbar.Heath.Cottage.room x := by
  have grow:=Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [grow.eventually_gt_atTop C,eventually_gt_atTop (1:ℝ)] with x h hx
  have t0:0<Real.log x:=Real.log_pos hx
  have g0:0<cue x:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hx))
  have u0:0<Real.sqrt (Real.sqrt (Real.log x)):=Real.sqrt_pos.mpr (Real.sqrt_pos.mpr t0)
  have same:x^(-(1/2:ℝ))=cue x:=by rw [Real.rpow_neg (zero_lt_one.trans hx).le,←Real.sqrt_eq_rpow];rfl
  unfold angularCut MSbar.Heath.Cottage.room MSbar.Heath.Stock.distance
  rw [same]
  calc
    _ = (cue x*Real.log x)*(C*Real.sqrt (Real.sqrt (Real.log x))) := by ring
    _ < (cue x*Real.log x)*(Real.sqrt (Real.sqrt (Real.log x)) * Real.sqrt (Real.sqrt (Real.log x))) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h u0) (mul_pos g0 t0)
    _ = _ := by rw [Real.mul_self_sqrt (Real.sqrt_nonneg _)]

end YM.Integration.FVA1Physical.Wilson
