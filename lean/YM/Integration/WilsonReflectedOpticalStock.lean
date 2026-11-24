import YM.Integration.WilsonReflectedOpticalRate
/-! The measured section and wrapped-coordinate fees cost two fixed
powers of the actual running inverse coupling, at any reporting point
between the old enrollment and the common lower mesh. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOpticalStock
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonOriginalMicroscopicGuardedPage WilsonReflectedAffordableArm
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family
local notation "L₀" => (C₀).path.levels
local notation "H₀" => (L₀).clock.hatBeta

theorem monotone (simple:G.Simple):Monotone (H₀):=by
  intro i j leq
  unfold Calendar.hatBeta
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (WilsonReflectedRelativeDate.monotone R leq) (Gauge.slopeConstant_pos simple).le)

theorem columns (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit):
    ∀ᶠ f:ℕ in atTop,stock (C₀) f≤H₀ f:=by
  obtain ⟨i,stocked⟩:=eventually_atTop.mp (factor_large (C₀) 1 zero_lt_one)
  filter_upwards [eventually_ge_atTop (i+1)] with f after
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show f≠0 by omega)
  have paid:4*stock (C₀) (k+1)≤factor (C₀) k:=by simpa only [Real.rpow_one] using (stocked k (by omega)).2
  have one:1≤H₀ k:=((L₀).fits.delayed k).le
  have logH:=Real.log_le_self (zero_le_one.trans one)
  have logL:=Real.log_le_self (show 0≤2+Real.log (H₀ k) by linarith only [Real.log_nonneg one])
  have cap:factor (C₀) k≤Real.log (2+Real.log (H₀ k)):=slow.2 k
  have rise:=monotone R simple (Nat.le_succ k)
  linarith only [paid,cap,logH,logL,one,rise]

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(d:ℕ):
    ∃C:ℝ,0<C ∧ ∀ᶠ j:ℕ in atTop,∀f,j≤f→((L₀).budget j).supportExponent≤100 →
    ((L₀).budget f).supportExponent≤100 →
    charge R d f*(1+wrapCost R d j) ≤ C*(H₀ f)^2:=by
  let w:=WilsonCapturedPrimaryCoreBill.wrapFee ((C₀).labels.level d) (C₀).params
  let v:=|price (C:=C₀) d|
  let u:=Real.exp 200
  have wp:0≤w:=mul_nonneg (Nat.cast_nonneg _) (germ_close ((C₀).labels.level d) (C₀).params).choose_spec.1.le
  have vp:0≤v:=abs_nonneg _
  have up:0<u:=Real.exp_pos _
  refine ⟨(12+v*u)*(1+w*u),mul_pos (by positivity) (by positivity),?_⟩
  obtain ⟨floor,due⟩:=eventually_atTop.mp (columns R simple slow)
  filter_upwards [eventually_ge_atTop floor] with j paid
  intro f late entry exit
  have one:1≤H₀ f:=((L₀).fits.delayed f).le
  have xp:0≤H₀ f:=zero_le_one.trans one
  have earnedJ:stock (C₀) j≤H₀ f:=(due j paid).trans (monotone R simple late)
  have earnedF:=due f (paid.trans late)
  have front:Real.exp (2*((L₀).budget j).supportExponent)≤u:=Real.exp_le_exp.mpr (by linarith only [entry])
  have back:Real.exp (2*((L₀).budget f).supportExponent)≤u:=Real.exp_le_exp.mpr (by linarith only [exit])
  have wbudget:wrapCost R d j≤w*u*(H₀ f):=mul_le_mul (mul_le_mul_of_nonneg_left front wp) earnedJ
    (zero_le_one.trans ((L₀).params j).columns_ge) (mul_nonneg wp up.le)
  have pbudget:projectionBill R d f≤v*u:=mul_le_mul_of_nonneg_left back vp
  have quiet:charge R d f≤(12+v*u)*H₀ f:=by
    unfold charge
    linarith only [earnedF,pbudget,one,le_mul_of_one_le_right (mul_nonneg vp up.le) one]
  have wrapped:1+wrapCost R d j≤(1+w*u)*H₀ f:=by linarith only [wbudget,one]
  have wnon:0≤1+wrapCost R d j:=by
    have pos:0≤wrapCost R d j:=mul_nonneg (mul_nonneg wp (Real.exp_nonneg _)) (zero_le_one.trans ((L₀).params _).columns_ge)
    linarith only [pos]
  exact (mul_le_mul quiet wrapped wnon (mul_nonneg (by positivity) xp)).trans_eq (by ring)

end YM.Integration.WilsonReflectedOpticalStock
end
