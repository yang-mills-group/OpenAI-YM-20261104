import YM.Integration.WilsonThermometerWeakPairClock
import YM.Integration.WilsonCenteredNestedLoggedRow

/-! Two actual running couplings and the two logarithmic tariffs at
the separation t=a/g(a)^B. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRunningWindow
open Filter Set Trace.Pilot PhysMS WilsonCenteredNestedLoggedRow WilsonThermometerWeakPairClock
open scoped Topology
variable {G:Gauge} (simple:G.Simple) (g:ℝ→ℝ) (hg:Coupling G g)

private lemma log_square {a t:ℝ} (tp:0<t) (le:t^2≤a) : LogV a ≤ 2*LogV t :=by
  have logs:=Real.log_le_log (pow_pos tp 2) le
  rw [Real.log_pow] at logs
  unfold LogV
  rw [Real.log_inv,Real.log_inv]
  norm_num at logs
  linarith

private lemma positive_root {x y:ℝ} (yp:0<y) (h:x^2≤8*y^2) : x≤3*y := by
  by_contra! bad
  have product:=mul_pos (sub_pos.mpr bad) (by linarith only [bad,yp]:0<x+3*y)
  nlinarith only [product,h,sq_nonneg y]

include simple hg in
theorem original (B:ℕ) :
    let t:=scale g B
    ∀ᶠ a in trail,0<g a ∧ 0<g (t a) ∧ g (t a)≤3*g a ∧
      (a/t a)=(g a)^B ∧ shell (t a)≤ shell a ∧ shell a*(g a)^2≤G.slopeConstant⁻¹+2 :=by
  let t:=scale g B
  let β:=G.slopeConstant⁻¹
  have βp:0<β:=inv_pos.mpr (Gauge.slopeConstant_pos simple)
  have late:=small simple g hg B
  have lower:=hg.running.eventually (le_mem_nhds (show β/2<β by linarith))
  have bound:=hg.running.eventually (ge_mem_nhds (show β<2*β by linarith))
  have soft:=hg.running.eventually (ge_mem_nhds (show β<β+1 by linarith))
  have less:∀ᶠ x:ℝ in trail,x<1:=(gt_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hg.positive,late.eventually hg.positive,lower,late.eventually bound,
    soft,late.eventually less,ordered simple g hg B,
    (hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    PhysMS.subpower_payment hg simple 1 1 zero_lt_one 1 zero_lt_one (2*B)] with a ap gp gtp lo hi upper smallT orderedA gone budget
  have ap':0<a:=ap
  have tp:0<t a:=lt_of_lt_of_le ap' orderedA
  have paid:a≤(g a)^(2*B):=by simpa only [Real.rpow_one,one_mul] using budget
  have power:a≤((g a)^B)^2:=by simpa only [←pow_mul,mul_comm B 2] using paid
  have short:(t a)^2≤a:=by
    change (a/(g a)^B)^2≤a
    rw [div_pow,div_le_iff₀ (pow_pos (pow_pos gp _) _)]
    nlinarith only [mul_le_mul_of_nonneg_left power ap'.le]
  have logs:=log_square tp short
  have logpos:0<LogV a:=by
    rw [LogV,Real.log_inv]
    exact neg_pos.mpr (Real.log_neg ap' (orderedA.trans_lt smallT))
  change β/2≤LogV a*(g a)^2 at lo
  change LogV (t a)*(g (t a))^2≤2*β at hi
  change LogV a*(g a)^2≤β+1 at upper
  have sq:(g (t a))^2≤8*(g a)^2:=by
    apply le_of_mul_le_mul_left _ logpos
    nlinarith only [mul_le_mul_of_nonneg_right logs (sq_nonneg (g (t a))),hi,lo]
  have rate:a/t a=(g a)^B:=by
    change a/(a/(g a)^B)=(g a)^B
    field_simp [ap'.ne',(pow_pos gp B).ne']
  have sl:shell (t a)≤ shell a:=by
    unfold shell
    rw [abs_of_nonpos (Real.log_nonpos tp.le smallT.le),abs_of_nonpos (Real.log_nonpos ap'.le (orderedA.trans smallT.le))]
    linarith only [Real.log_le_log ap' orderedA]
  have bill:shell a*(g a)^2≤β+2:=by
    unfold shell
    rw [abs_of_nonpos (Real.log_nonpos ap'.le (orderedA.trans smallT.le))]
    rw [LogV,Real.log_inv] at upper
    nlinarith only [upper,pow_le_one₀ gp.le gone (n:=2)]
  exact ⟨gp,gtp,positive_root gp sq,rate,sl,bill⟩

end YM.Integration.WilsonCenteredNestedRunningWindow
