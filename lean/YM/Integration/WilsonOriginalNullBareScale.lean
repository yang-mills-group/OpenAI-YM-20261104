import YM.Integration.WilsonOriginalNullBareInvoice
import YM.Integration.WilsonCenteredReporterClock

/-! The auxiliary detector step and the actual section price at the true top date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareScale
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.Local Push.PriceCompiler Next.Foundations Extra.Histories Pert.Asymptotics RG16
open private monotone from YM.Integration.WilsonMeasuredImpulseCalendar
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
theorem original (simple:G.Simple)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels) (I:ℝ):
    ∀ᶠ n:ℕ in atTop, ∀ per,
    let B:=R.alloy.B.a.clock.hatBeta n
    let H:=R.alloy.B.a.clock.hatBeta (n+1)
    let g:=regulatorRun R.family (n+1) per (n+1)
    let μ:=(R.family.path.levels.params n).columns
    2 ≤ B ∧ B ≤ H ∧ 0<g ∧ g ≤ 1 ∧ g⁻¹ ≤ 2*(1+H) ∧ 0 ≤ μ ∧ μ ≤ 8*H ∧ I*g^3*μ ≤ 1/2 :=by
  let a:=R.alloy.B.a
  have rise:Tendsto a.clock.hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [WilsonCenteredReporterClock.original R simple slow ready,
    rise.eventually_ge_atTop (2*(8*(1+|I|))^2),rise.eventually_ge_atTop 2] with n native large warm
  intro per B H g μ
  have step:B≤H:=monotone simple a (Nat.le_succ n)
  have eps:2*(8*(1+|I|))^2 ≤ H:=large.trans step
  have h2:2 ≤ H:=warm.trans step
  obtain ⟨xpos,_,_,col,_,_,_,_,_⟩:=native (n+1) per (Nat.lt_succ_self n)
  let β:=(R.family.path.rep (n+1) per (n+1)).beta
  have beta:0<β:=Overlay.beta_positive R.makes.wilson le_rfl
  have lo:H/2≤β:=(R.makes.wilson.represents (n+1) per (n+1) le_rfl).band.1
  have hi:β≤2*H:=(R.makes.wilson.represents (n+1) per (n+1) le_rfl).band.2
  let x:=Real.sqrt β
  have xp:0<x:=Real.sqrt_pos.mpr beta
  have square:x^2=β:=Real.sq_sqrt beta.le
  have gg:g=x⁻¹:=rfl
  have grow:8*(1+|I|)≤x:=by
    rw [←Real.sqrt_sq (show 0≤8*(1+|I|) by positivity)]
    exact Real.sqrt_le_sqrt (by linarith only [eps,lo])
  have px:1≤x:=by linarith only [grow,abs_nonneg I]
  have cp:0≤μ:=zero_le_one.trans (R.family.path.levels.params n).columns_ge
  have capped:μ ≤ 4*x^2:=by
    change μ ≤ 4*(g⁻¹)^2 at col
    rw [gg,inv_inv] at col
    exact col
  rw [gg,inv_inv]
  refine ⟨warm,step,inv_pos.mpr xp,inv_le_one_of_one_le₀ px,?_,cp,?_,?_⟩
  · nlinarith only [px,square,hi,h2,sq_nonneg (x-1)]
  · linarith only [capped,square,hi]
  · rw [inv_pow]
    have h:2*I*μ ≤ x^3:=by
      calc
        2*I*μ ≤ 2*|I| *μ:=mul_le_mul_of_nonneg_right (by linarith only [le_abs_self I]) cp
        _ ≤ 2*|I| *(4*x^2):=mul_le_mul_of_nonneg_left capped (by positivity)
        _ ≤ x^3:=by nlinarith only [mul_nonneg (sub_nonneg.mpr grow) (sq_nonneg x),sq_nonneg x]
    field_simp [xp.ne']
    linarith only [h]
end YM.Integration.WilsonOriginalNullBareScale
