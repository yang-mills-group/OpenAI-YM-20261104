import YM.Integration.WilsonReflectedPurchasedFiling
import YM.Integration.WilsonCloseCaptureDate

/-! The real-radius launch and capture carry identical logarithmic height.
The original fixed-reference replica loss is a positive spatial power even
after both physical regulators are released. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedPhysicalRate
open Filter Function Lattice Wilson RG OPE RG16.Literal MergeProof Ribbons Bid PhysMS
open OPE.Log Trace.Pilot
open Extra.Histories PhysicalNext.Repeat.Legato Bandage Push Trace.Physical.GermGraph
open scoped Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple)

def capture (r:ℝ):ℕ := WilsonCloseCaptureDate.level R.family.S r - 1
def launch (v:ℕ) (r:ℝ):ℕ := WilsonMeasuredWindow.stop R.family.path.levels simple v r

theorem dates (slow:WilsonWindowReportingPace.Slow R.kit) (v:ℕ) (wide:0<v) :
    Height R.family.S trail LogV (capture R) 1 ∧
      Height R.family.S trail LogV (launch R simple v) 1 :=
  ⟨Log.previous PhysMS.to_log_zoom (WilsonCloseCaptureDate.height R) R.family.path.levels.fits.mesh,
    WilsonMeasuredWindow.measured_stop_height R.family.path.levels simple v (WilsonFundedMeasuredWindow.paced R slow) wide PhysMS.to_log_zoom PhysMS.length_rate⟩

omit simple in
theorem physical (u h:ℕ) {E:ℝ→ℝ} (fee:RateIs trail LogV E (-(h:ℝ))) (K:ℝ) :
    ∀ᶠ r in trail,
      2*(K/Real.exp (((h:ℝ)+1/16)*LogV r)) + E r/gainChart R.family.path (capture R r) u
        ≤ Real.exp ((-(h:ℝ)-1/32)*LogV r) :=by
  have time:=PhysMS.to_log_zoom
  have cap:Height R.family.S trail LogV (capture R) 1:=
    Log.previous time (WilsonCloseCaptureDate.height R) R.family.path.levels.fits.mesh
  have gain:RateIs trail LogV (fun r=>gainChart R.family.path (capture R r) u) (1/8:ℝ):=by
    apply RateIs.exp'
    have base:=(tendsto_const_nhds (x:=R.family.S.scale u)).div_atTop time
    simpa only [sub_zero,mul_one,←sub_div,←mul_div_assoc] using! ((cap.pace.sub base).const_mul (1/8:ℝ))
  have major:0<1+|K|:=by positivity
  have pay:=((RateIs.const (c:=2) time zero_lt_two).mul
    ((RateIs.const time major).div (RateIs.exp ((h:ℝ)+1/16) time))).add (fee.div gain) time
  have target:=RateIs.exp (-(h:ℝ)-1/32) time
  have smaller: max (0+(0-((h:ℝ)+1/16))) (-(h:ℝ)-1/8) < -(h:ℝ)-1/32 :=
    max_lt (by linarith) (by linarith)
  filter_upwards [target.overtakes (pay.pays time) time smaller] with r price
  refine le_trans ?_ price.le
  have below:K ≤ 1+|K|:=by linarith [le_abs_self K]
  exact add_le_add (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right below (Real.exp_pos _).le) zero_le_two) le_rfl
end YM.Integration.WilsonReflectedPhysicalRate
