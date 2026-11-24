import YM.OPE.Compatible.Chain.Polar
/-!
# both resolutions summed. Absolute entry width station. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
-- book
lemma matrixPay (X Y:Matrix M M ℂ){x y:ℝ}(hx:∀ i j,‖X i j‖≤x)(hy:∀ i j,‖Y i j‖≤y)(i j:M) : ‖(X*Y) i j‖ ≤ (Fintype.card M:ℝ)*(x*y):=by
       rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans; apply le_trans (Finset.sum_le_sum (g:=fun _=>x*y) (s:=univ) ?_); exact le_of_eq (by simp); intro k _; rw [norm_mul]; exact mul_le_mul (hx i k) (hy k _) (norm_nonneg _) ((norm_nonneg _).trans (hx i k))
lemma pole_pay (h:4≤r): ∃ b:ℝ,0<b ∧ ∀ v:Train r,∀ n:Side,∀ p:Site n,∀ u≥0,∀ i j:M, p≠0 → ‖(under (ShellRow C v) u p) i j‖ ≤ b/(win p)^2:=by
      obtain ⟨d,hp,H⟩:= bough_bill C h; exact ⟨d⁻¹,inv_pos.mpr hp,fun v n p u hu i j h=> plain_bill hu hp h (H v n u hu p) i j⟩
lemma pole_changed (h:4 ≤ r):∃ k:ℝ,0≤ k ∧ ∀ v:Train r,∀ n:Side,∀ p:Site n,∀ u>0,∀ i j:M,
  ‖((under (ShellRow C v) u p) i j - slender (ShellRow C v) p i j)‖ ≤ k*Real.sqrt u*(win p)^(-(3:ℤ))+(if p=0 then u⁻¹ else 0) :=by
   obtain ⟨d,hp,H⟩:=bough_bill C h
   let s:= (Fintype.card M:ℝ)
   let D:= (d⁻¹+d⁻¹) * (s*d⁻¹*d⁻¹); have hs:0≤s:=Nat.cast_nonneg _; have hD:0≤D:=by unfold D; positivity
   refine ⟨Real.sqrt D,Real.sqrt_nonneg _,fun v n p u hu i j=>?_⟩
   let A:= ShellRow C v; let W:=spline A (mon p); let Z:=bough A u (mon p); by_cases hq:p=0
   · have hz: slender A p i j=0:=by simp [slender,hq]
     change ‖Z⁻¹ i j-slender A p i j‖≤ _; rw [hz, sub_zero,if_pos hq]; apply (le_add_of_nonneg_left ?_).trans' (entryC (d:=u) ?_ hu _ _)
     · exact mul_nonneg (by positivity) (zpow_nonneg (norm_nonneg _) _)
     intro x; apply le_trans _ (H v n u hu.le p x); exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (sqLength_nonneg _)
   rw [if_neg hq,add_zero,slender,if_neg hq]; let t:= win p; have ht:0<t:=win_p p hq; let X:=W⁻¹; let Y:=Z⁻¹; let a:=d⁻¹; have hx(o j:M): ‖X o j‖ ≤ a/t^2:=(by have he:= plain_bill (show (0:ℝ)≤0 from le_rfl) hp hq (H v n 0 le_rfl p) o j; simpa [under,bough] using he)
   have hy(o j:M): ‖Y o j‖ ≤ a/t^2:= plain_bill hu.le hp hq (H v n u hu.le p) o j
   let c:= ‖Y i j-X i j‖; have he:c ≤ (a+a)/t^2:= (norm_sub_le ..).trans ((add_le_add (hy _ _) (hx _ _)).trans_eq (add_div ..).symm)
   have ho:c ≤ u*(s*a*a)/t^4:= by
        have hj: IsUnit W.det:=conduit h v hq; have hk:IsUnit Z.det:= Value.det_unit (by have ht:=win_p p hq; positivity) (H v n u hu.le p)
        have hh: Y-X= Y*(W-Z)*X:=by rw [mul_sub,sub_mul,mul_assoc Y W X,show W*X=1 from Matrix.mul_nonsing_inv _ hj,show Y*Z=1 from Matrix.nonsing_inv_mul _ hk, one_mul,mul_one]
        rw [show c=‖(Y-X) i j‖ from rfl,hh,show W-Z= -((u:ℂ) • 1) from by unfold W Z bough; abel]; simp only [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,Matrix.neg_apply, norm_neg,Matrix.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]; exact le_trans (mul_le_mul_of_nonneg_left (matrixPay _ _ hy hx i j) hu.le) (le_of_eq (by change u*(s*_)=_;ring))
   change c ≤ Real.sqrt D * Real.sqrt u * t ^ (-(3:ℤ)); apply le_of_sq_le_sq (b:=Real.sqrt D * Real.sqrt u * t ^ (-(3:ℤ))) _ (by positivity); rw [mul_pow, mul_pow (Real.sqrt D),Real.sq_sqrt hD,Real.sq_sqrt hu.le]; unfold D; apply le_trans (b:=((a+a)/t^2)*(u*(s*a*a)/t^4)); rw [pow_two]; exact mul_le_mul he ho (norm_nonneg _) ((norm_nonneg _).trans he)
   unfold a; apply le_of_eq; simp only [_root_.zpow_neg]; field_simp
end YM.OPE.Cascade.Terp
