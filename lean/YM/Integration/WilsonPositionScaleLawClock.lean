import YM.Integration.WilsonPositionScaleLawQinter
import YM.Integration.WilsonMaxwellThermometerKineticRunning

/-! The dyadic cost uses the measured kinetic coefficient on the original
cutoff, including the reporting-date and regulator filter of that theorem. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawClock
open Filter Set Function Metric Maxwell XSpace XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register
open Lattice Wilson RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open WilsonMaxwellThermometerKineticPanel WilsonPositionThermometerCapStation WilsonPositionCapTransport
open Trace.Over (b0)
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical

def radius(r:ℝ)(n:ℕ):=r*(1/2:ℝ)^n

theorem falls (r:ℝ)(hr:0<r):Tendsto (radius r) atTop trail:=by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,.of_forall fun n=>(mul_pos hr (pow_pos (by norm_num) n))⟩
  have h:= (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num:0≤(1/2:ℝ)) (by norm_num)).const_mul r
  change Tendsto (fun n:ℕ=>r*(1/2:ℝ)^n) atTop (𝓝 0)
  simpa only [mul_zero] using h

theorem logRadius (r:ℝ)(hr:0<r)(n:ℕ):LogV (radius r n)=(n:ℝ)*Real.log 2-Real.log r:=by
  rw [LogV,Real.log_inv,radius,Real.log_mul hr.ne' (pow_ne_zero _ (by norm_num)),Real.log_pow,one_div,Real.log_inv];ring

private theorem logRate (r:ℝ)(hr:0<r):Tendsto (fun n:ℕ=>LogV (radius r n)/((n:ℝ)+1)) atTop (𝓝 (Real.log 2)):=by
  have deep:Tendsto (fun n:ℕ=>(n:ℝ)+1) atTop atTop:=by
    apply ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)).congr
    intro n;change ((n+1:ℕ):ℝ)=_;simp
  have small:Tendsto (fun n:ℕ=>(Real.log r+Real.log 2)/((n:ℝ)+1)) atTop (𝓝 0):=deep.const_div_atTop _
  have lim:=tendsto_const_nhds (x:=Real.log 2) |>.sub small
  rw [sub_zero] at lim
  apply lim.congr;intro n;rw [logRadius r hr];field_simp;ring

theorem rate {G:Gauge}{g:ℝ→ℝ}(funded:Coupling G g)(r:ℝ)(hr:0<r):
    Tendsto (fun n:ℕ=>((n:ℝ)+1)*g (radius r n)^2) atTop (𝓝 ((2*b0 G*Real.log 2)⁻¹)):=by
  have hlog:0<Real.log 2:=Real.log_pos (by norm_num)
  have lim:=(funded.running.comp (falls r hr)).div (logRate r hr) hlog.ne'
  have coeff:G.slopeConstant⁻¹/Real.log 2=(2*b0 G*Real.log 2)⁻¹:=by
    simp only [Trace.Over.beta_eq,div_eq_mul_inv,mul_inv_rev];ring
  rw [coeff] at lim
  apply lim.congr'
  filter_upwards [(tendsto_order.mp (logRate r hr)).1 0 hlog] with n hn
  have led:LogV (radius r n)≠0:=fun h=>by rw [h,zero_div] at hn;exact lt_irrefl _ hn
  change LogV (radius r n)*g (radius r n)^2/(LogV (radius r n)/((n:ℝ)+1))=_
  field_simp

variable {G:Gauge}(Z:WilsonPrescription G){R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(A:ℝ→Group R.family 6)
    {Y:Ultrafilter (ℕ×ℕ)}{Q:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}(simple:G.Simple){B:ℕ}
local notation "visits"=>trail.curry (Y:Filter (ℕ×ℕ))
local notation "therm"=>WilsonPositionRawCutoff.thermometer Z F J A
local notation "cash"=>WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B)

theorem original (pace:WilsonWindowReportingPace.Slow R.kit)(hB:0<B)
    (bliss:Bliss F Y arch Q)(book:Book (f:=f) (l:=Y) (H:=Q) A J)(lead:Leading F J)
    (axis:ℝ×(ℕ×ℕ)→ℝ)(live:∀ᶠw in visits,0<axis w)
    (panel:Tendsto (fun w=>therm w.1 w.2/axis w) visits (𝓝 1))
    (clock:Tendsto (fun w=>axis w/cash w.1 w.2) visits (𝓝 1))(r:ℝ)(hr:0<r):
    Tendsto (fun n:ℕ=>((n:ℝ)+1)*kinetic Z F J (radius r n)^2) atTop (𝓝 ((2*b0 G*Real.log 2)⁻¹)):=
  rate (WilsonMaxwellThermometerKineticRunning.original Z F J A simple pace hB bliss book lead axis live panel clock).2 r hr

end YM.Integration.WilsonPositionScaleLawClock
end
