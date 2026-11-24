import YM.Integration.FVA1Physical.Sources.Round2.FieldReadingOn
import YM.MSbar.Chord.Carpet
import YM.WilsonBulk.Agenda.Hat

/-! Changing from bond derivatives into ordinary field coordinates on the
actual adjacent scales cancels the inverse cutoff power exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Lattice Function RG YM.Wilson Precision PhysicalNext.Repeat.Legato
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Mosaic
open Push.Uniform AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open scoped BigOperators Classical

def chartFactor (G:Gauge) (q:ℕ) : ℝ := (q.factorial:ℝ)*deed q*(1+floorY G q)^q

theorem measured_chart_identity (G:Gauge) (B:BudgetPoint) (q:ℕ) (g:ℝ) :
    |g|^q * earnE B G q=(|g|/B.threshold)^q * chartFactor G q := by
  unfold earnE composeCost chartFactor
  rw [div_pow]
  ring

theorem measured_chart_cap (G:Gauge) (B:BudgetPoint) (q:ℕ) {g t:ℝ}
    (ratio:|g|≤t*B.threshold) : |g|^q*earnE B G q≤t^q*chartFactor G q := by
  have charge:0≤chartFactor G q:=by
    have hd:0≤deed q:=add_nonneg zero_le_one (Finset.sum_nonneg fun i _=>zero_le_one.trans (polar_one i))
    have hf:0≤floorY G q:=(account q G).choose_spec.1
    unfold chartFactor
    positivity
  rw [measured_chart_identity]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg (abs_nonneg g) B.threshold_pos.le)
    ((div_le_iff₀ B.threshold_pos).mpr ratio) q) charge

theorem actual_field_scale {G:Gauge} (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    {N n j:ℕ} (inside:j<N) :
    let H:=R.family.path
    let fine:=(H.rep N n (j+1)).beta
    |(Real.sqrt fine)⁻¹| ≤ 2*(H.rep N n j).p.threshold := by
  intro H fine
  let a:=H.levels
  let x:=a.clock.hatBeta j
  let y:=a.clock.hatBeta (j+1)
  have hx:0<x:=zero_lt_one.trans (a.fits.delayed j)
  have hy:0<y:=zero_lt_one.trans (a.fits.delayed (j+1))
  have band: y/2≤fine ∧ fine≤2*y:=(R.T.choice.represents N n (j+1) inside).band
  have pos:0<fine:=(half_pos hy).trans_le band.1
  have upper:cue fine≤2*cue y:=(Mosaic.ever hy band.1 band.2).2
  have step:cue y≤cue x:=inv_anti₀ (Real.sqrt_pos.mpr hx)
    (Real.sqrt_le_sqrt (WilsonBulk.Parapet.Agenda.hat_mobile a hG (Nat.le_succ j)))
  have cap:cue x≤a.clock.threshold j:=le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (Real.one_le_exp (sq_nonneg _))
  have same:(H.rep N n j).p=a.budget j:=(R.T.choice.represents N n j inside.le).vac
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr pos)),same]
  exact upper.trans (mul_le_mul_of_nonneg_left (step.trans cap) zero_le_two)

theorem paid_actual_chart {G:Gauge} (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    {N n j:ℕ} (inside:j<N) (q:ℕ) :
    let H:=R.family.path
    |(Real.sqrt (H.rep N n (j+1)).beta)⁻¹|^q * earnE (H.rep N n j).p G q ≤ 2^q*chartFactor G q :=
  measured_chart_cap G _ q (actual_field_scale hG R inside)

end YM.Integration.FVA1Physical.Round2.Curvature
