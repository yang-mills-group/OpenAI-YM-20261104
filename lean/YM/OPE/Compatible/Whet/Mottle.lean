import YM.OPE.Compatible.Clove.Topaz
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
lemma expDiff_low (a b:ℝ)(h:a≤b): |Real.exp a-Real.exp b| ≤ |a-b| * Real.exp b:=by
    simp only [abs_of_nonpos (sub_nonpos.mpr h),abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h))]; have hv:=Real.add_one_le_exp (a-b); rw [Real.exp_sub,le_div_iff₀ (Real.exp_pos _)] at hv; linarith
lemma expDiff (a b:ℝ): ‖Real.exp a-Real.exp b‖ ≤ ‖a-b‖*(Real.exp a+Real.exp b):=by
    rcases le_total a b with h|h
    · exact (expDiff_low a b h).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_nonneg _)) (abs_nonneg _))
    rw [norm_sub_rev, norm_sub_rev a]; exact (expDiff_low b a h).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_nonneg _)) (norm_nonneg (b-a)))
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure]
def Impact (A B: Law E)(z:E):= (-(A.P z z))/2-(-(B.P z z))/2
local notation "mH" A=> ∫ x,(Law.kern (A) x) ∂μ
lemma lightA (A:Law E):0 < mH A:=by
     apply integral_exp_pos; convert! lumpZ μ A 1 Bond.one using 1; rw [one_mul];rfl
lemma skin (A B:Law E)(p q:E→ℝ)(hx:Bond p)(hy:Bond q)(h:∀ x,‖p x*Impact A B x‖ ≤ q x):
    let a:= mH A
    let b:= mH B
    ‖A.average μ p*a-B.average μ p*b‖ ≤ (‖A.average μ q‖ *a + ‖B.average μ q‖ *b):=by
      intro a b; let w:=A.kern; let t:=B.kern; have ha:a>0:= lightA μ A; have hb:b>0:= lightA μ B; have he:∀ x, ‖w x-t x‖≤ ‖Impact A B x‖*(w x+t x):= fun x=>expDiff ..; unfold Law.average; rw [Real.norm_eq_abs (_/a),Real.norm_eq_abs (_/b),abs_div,abs_div,abs_of_pos ha,abs_of_pos hb,div_mul_cancel₀ _ ha.ne',div_mul_cancel₀ _ hb.ne', div_mul_cancel₀ _ ha.ne',div_mul_cancel₀ _ hb.ne'] -- parentheses
      rw [← integral_sub (lumpZ μ A _ hx) (lumpZ μ B _ hx)]
      have hv : Integrable (fun x=>(q*w) x+(q*t) x) μ:= (lumpZ μ A _ hy).add (lumpZ μ B _ hy); apply le_trans (norm_integral_le_of_norm_le hv (Eventually.of_forall (fun x=>?_))) ((le_of_eq (integral_add (lumpZ μ A _ hy) (lumpZ μ B _ hy))).trans (add_le_add (le_abs_self _) (le_abs_self _)))
      change ‖p x*w x-p x*t x‖ ≤ q x*w x+q x*t x; rw [← mul_sub,norm_mul, ← mul_add]; apply (mul_le_mul_of_nonneg_left (he x) (norm_nonneg _)).trans; rw [←mul_assoc,←norm_mul]; exact mul_le_mul_of_nonneg_right (h x) (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
lemma swollen (A B:Law E)(p q r:E→ℝ)(hx:Bond p)(hy:Bond q)(hz:Bond r)(h:∀ x,‖p x*Impact A B x‖ ≤ q x)(hv:∀ x,‖Impact A B x‖≤ r x):
    ‖A.average μ p-B.average μ p‖ ≤ (‖A.average μ q‖+‖B.average μ q‖)+(‖A.average μ r‖+‖B.average μ r‖)*(‖A.average μ p‖+‖B.average μ p‖):=by
    let a:= mH A; let b:=mH B
    have ha:= lightA μ A; change a>0 at ha; have hb:= lightA μ B; change b>0 at hb; let D:= A.average μ; let W:=B.average μ
    let c:=max a b; have hc: c>0:=ha.trans_le (le_max_left ..)
    have ht: ‖D p*a-W p*b‖ ≤ c*(‖D q‖+‖W q‖):= (skin μ A B p q hx hy h).trans (by rw [mul_add]; apply add_le_add <;> rw [mul_comm c] <;> gcongr; exact le_max_left ..; exact le_max_right ..)
    have h':=skin μ A B 1 r Bond.one hz (by simpa using hv); rw [Law.empty,Law.empty] at h'; change ‖1*a-1*b‖ ≤ _ at h'; rw [one_mul,one_mul] at h'
    have he: ‖a-b‖ ≤ c * (‖D r‖ + ‖W r‖):= h'.trans (by rw [mul_add];apply add_le_add <;> rw [mul_comm c] <;> gcongr; exact le_max_left ..; exact le_max_right ..)
    let U:= ‖D p‖ + ‖W p‖; let v:= c*(‖D r‖+‖W r‖); let b':=c*(‖D q‖+‖W q‖); have ht' : ‖(D p-W p) * c‖≤ b'+v*U:=by
        rcases le_total a b with h|h
        · rw [show (D p-W p)* c= (D p*a-W p*b)+D p*(b-a) from (by rw [show c=b from max_eq_right h];ring)]; apply (norm_add_le ..).trans; rw [norm_mul, mul_comm v,norm_sub_rev b]; exact add_le_add ht (mul_le_mul (le_add_of_nonneg_right (norm_nonneg _)) he (norm_nonneg _) (by unfold U;positivity))
        rw [show (D p-W p)*c=(D p*a-W p*b) - W p * (a-b) from (by rw [show c=a from max_eq_left h]; ring)]; apply (norm_sub_le ..).trans; rw [norm_mul,mul_comm v]; exact add_le_add ht (mul_le_mul (le_add_of_nonneg_left (norm_nonneg _)) he (norm_nonneg _) (by unfold U;positivity))
    rw [norm_mul,Real.norm_of_nonneg hc.le, mul_comm, show b'+v*U=c*((‖D q‖+‖W q‖)+(‖D r‖+‖W r‖)*(‖D p‖+‖W p‖)) from by unfold b' v U;ring, mul_le_mul_iff_right₀ hc] at ht'; exact ht'
end YM.OPE.Quit.PriceZ
