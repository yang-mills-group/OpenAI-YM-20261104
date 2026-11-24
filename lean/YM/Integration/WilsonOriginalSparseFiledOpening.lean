import YM.Integration.WilsonOriginalSparseFiledTotal

/-! The crop, both printed tail orders and every numerical extraction cost are
chosen before the physical cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledOpening
open Filter WilsonOriginalSparseFiledTotal
open scoped Topology

def near (P pole E:ℕ) := P+pole+E+2
def tail (H:ℝ) (P pole E:ℕ) (ω:ℝ) := (H^(near P pole E))⁻¹+ω

structure Ready (G:Gauge) (height bill saved:ℕ) (H:ℝ) : Prop where
  hot : 2≤H
  thermal : Real.exp 1≤H
  fixed : WilsonOriginalSparseFiledRosterCash.room G (3*height)≤H
  late : (512*((2*(1+(bill+2)+saved):ℕ)+1:ℝ))^2≤Real.log H
  size : ((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)≤H
  all : ∀d≤3*height, load G d H≤H

theorem scheduled (G:Gauge) (height bill saved:ℕ):∀ᶠ H:ℝ in atTop,Ready G height bill saved H:=by
  filter_upwards [eventually_ge_atTop 2,eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (WilsonOriginalSparseFiledRosterCash.room G (3*height)),
    Real.tendsto_log_atTop.eventually_ge_atTop ((512*((2*(1+(bill+2)+saved):ℕ)+1:ℝ))^2),
    eventually_ge_atTop (((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)),calendar G (3*height)]
    with H two therm fixed late size cap
  exact ⟨two,therm,fixed,late,size,cap.2⟩

def starts (G:Gauge) (height bill saved:ℕ):ℝ:=(eventually_atTop.mp (scheduled G height bill saved)).choose

theorem enrolled (G:Gauge) (height bill saved:ℕ) {H:ℝ} (admit:starts G height bill saved≤H):
    Ready G height bill saved H:=(eventually_atTop.mp (scheduled G height bill saved)).choose_spec H admit

/-- Pay the actual external Laurent power and the positively priced link reader.
Only the chosen threshold changes when the Taylor horizon grows. -/
theorem quoted {G:Gauge} {H β g L ω:ℝ} {height bill saved:ℕ} (date:Ready G height bill saved H)
    (thermal:β≤2*H) (dated:g=(Real.sqrt β)⁻¹) (hn:0≤ω) (P pole E:ℕ) (salary:L≤H^E)
    (ln:0≤L) :
    (g^pole)⁻¹*(L*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ))*((H^(P+pole+E+1))⁻¹+H*ω)
      ≤ (H^P)⁻¹+H^(pole+E+2)*ω := by
  have h2:=date.hot
  have hp:0<H:=by linarith
  have base:Real.sqrt β≤H:=Real.sqrt_le_iff.mpr
    ⟨hp.le,thermal.trans (by nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr h2)])⟩
  have raised:(g^pole)⁻¹≤H^pole:=by
    simpa [dated,inv_pow] using pow_le_pow_left₀ (Real.sqrt_nonneg β) base pole
  have sc:0≤((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ):=by positivity
  have ls:=mul_le_mul salary date.size sc (pow_nonneg hp.le _)
  have toll:(g^pole)⁻¹*(L*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ))≤H^(pole+E+1):=by
    rw [mul_assoc L,pow_succ,pow_add]
    simpa only [mul_assoc] using mul_le_mul raised ls (mul_nonneg ln sc) (pow_nonneg hp.le _)
  have nn:0≤(H^(P+pole+E+1))⁻¹+H*ω:=by positivity
  apply (mul_le_mul_of_nonneg_right toll nn).trans_eq
  rw [mul_add,show P+pole+E+1=P+(pole+E+1) by omega,pow_add,
    show pole+E+2=(pole+E+1)+1 by omega,pow_succ H (pole+E+1)]
  simp only [pow_add,pow_succ]; field_simp

/-- A fixed physical clock multiplies the full normalized finite-period invoice.
The original fine cutoff may still range freely in its uniform input estimate. -/
theorem winding {ι:Type*} {l:Filter ι} {n:ι→ℝ} (grows:Tendsto n l atTop)
    (scale C reach:ℝ) (a:ℕ) {σ:ℝ} (pos:0<σ):
    Tendsto (fun i=>scale*(C*(1+n i)^a*Real.exp (-σ*(n i-2*reach)))) l (𝓝 0):=by
  have lifted:Tendsto (fun i=>1+n i) l atTop:=tendsto_const_nhds.add_atTop grows
  have decay:=(tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a:ℝ) σ pos).comp lifted
  have fixed:=decay.const_mul (scale*C*Real.exp (σ*(1+2*reach)))
  simpa only [mul_zero] using (show Tendsto (fun i=>scale*(C*(1+n i)^a*Real.exp (-σ*(n i-2*reach))))
      l (𝓝 ((scale*C*Real.exp (σ*(1+2*reach)))*0)) from by
    convert fixed using 2 with i
    simp only [Function.comp_apply,Real.rpow_natCast]
    rw [show -σ*(n i-2*reach)=σ*(1+2*reach)+(-σ*(1+n i)) by ring,Real.exp_add]
    ring)

end YM.Integration.WilsonOriginalSparseFiledOpening
