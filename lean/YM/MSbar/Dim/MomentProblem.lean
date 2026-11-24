import YM.MSbar.Dim.Wide
import Mathlib.Topology.ContinuousMap.Weierstrass

/-! Extension in dimension for multiple-contour integrals. Use after removing gamma factors all
kernels with no ε-dependent weights (iterate even for evanescent-index traces by linearity).
Compact support required before continuation. This is not a generic uniqueness rule for analytic
functions from sparse integer values. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Polynomial
open scoped Topology ContDiff BigOperators Classical
section
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsLocallyFiniteMeasure μ] {K : Set X} (hc:IsCompact K) {F G:X→ℂ} (hf : ContinuousOn F K)(hg : ContinuousOn G K) {t:X→ℝ} (ht:ContinuousOn t K) {b : ℝ} (hb: MapsTo t K (Icc 0 b))
include ht hc hf

lemma moment_poly (hp:∀ n:ℕ, (∫ x in K,(↑(t x):ℂ)^n*F x ∂μ)=0) (q: Polynomial ℝ) : (∫ x in K,(↑(q.eval (t x)):ℂ)*F x ∂μ)=0:=by
   induction q using Polynomial.induction_on' with
   | monomial n a => simp_rw [eval_monomial,ofReal_mul,ofReal_pow,mul_assoc]; rw [integral_const_mul,hp n,mul_zero]
   | add p q ih jh => simp_rw [eval_add,Complex.ofReal_add,add_mul]; rw [integral_add,ih,jh,zero_add] <;> exact (((continuous_ofReal.comp_continuousOn (Polynomial.continuous _ |>.comp_continuousOn ht)).mul hf).integrableOn_compact hc)
include hb
lemma moment_real (hp:∀ n:ℕ, (∫ x in K,(↑(t x):ℂ)^n*F x ∂μ)=0) {g:ℝ→ℝ} (h : ContinuousOn g (Icc 0 b)) : (∫ x in K,(↑(g (t x)):ℂ)*F x ∂μ)=0:=by
   apply norm_le_zero_iff.mp; apply le_of_forall_pos_le_add; intro ε he
   let m:=∫ x in K,‖F x‖ ∂μ; have hm : 0 ≤ m := integral_nonneg fun _=>norm_nonneg _
   let δ:=ε/(1+m); have hd : 0<δ :=by unfold δ; positivity
   obtain ⟨q,hq⟩:= exists_polynomial_near_of_continuousOn 0 b g h δ hd
   let v(x:X):ℂ:= ↑(g (t x)); let u(x:X):ℂ:= ↑(q.eval (t x)); have hv: ContinuousOn v K := continuous_ofReal.comp_continuousOn (h.comp ht hb); have hu: ContinuousOn u K:= continuous_ofReal.comp_continuousOn (q.continuous.comp_continuousOn ht)
   have h1:IntegrableOn (v*F) K μ:=(hv.mul hf).integrableOn_compact hc; have h2: IntegrableOn (u*F) K μ:=(hu.mul hf).integrableOn_compact hc
   change ‖∫ x in K,v x * F x ∂μ‖ ≤ _
   have hV(x:X)(hx:x∈K) : ‖v x-u x‖≤δ:=by unfold v u; rw [← ofReal_sub, Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]; exact (hq _ (hb hx)).le
   rw [zero_add]; calc
    _ = ‖∫ x in K,v x*F x-u x*F x ∂μ‖:= by rw [integral_sub (f:=fun x=>v x*F x) (g:=fun x=>u x*F x) h1 h2,show (∫ x in K,u x*F x ∂μ)=0 from moment_poly hc hf ht hp q,sub_zero]
    _ ≤ ∫ x in K,δ*‖F x‖ ∂μ:= norm_integral_le_of_norm_le ((hf.integrableOn_compact hc).norm.const_mul δ) ((ae_restrict_mem hc.measurableSet).mono (fun x hx =>by rw [← sub_mul,norm_mul]; exact mul_le_mul_of_nonneg_right (hV x hx) (norm_nonneg _)))
    _ ≤ ε := by rw [integral_const_mul]; change δ*m≤ε; calc
                 δ*m≤δ*(1+m):=by gcongr; simp
                 _ = ε:=div_mul_cancel₀ _ (by linarith)

lemma moment_complex (hp:∀ n:ℕ, (∫ x in K,(↑(t x):ℂ)^n*F x ∂μ)=0) {g:ℝ→ℂ} (h : ContinuousOn g (Icc 0 b)) : (∫ x in K, g (t x)*F x ∂μ)=0:=by
   let f(x:X):= g (t x); let u:= fun x:X=> (f x).re; let v:= fun x:X=> (f x).im
   let r(x:X):ℂ:= u x; let S (x:X):ℂ:= v x; let d(x:X):=r x*F x; let e(x:X):=S x*F x
   have he:ContinuousOn f K:= h.comp ht hb; have hr:ContinuousOn r K:= continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn he);have hs:ContinuousOn S K:=continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn he)
   have hw(x:X):f x*F x=d x+I*e x:=by rw [← re_add_im (f x)]; unfold d e S r u v; ring
   have ht' : IntegrableOn (fun x=> I*e x) K μ:= ((hs.mul hf).integrableOn_compact hc).const_mul I
   change (∫ x in K,f x*F x ∂μ)=_; simp_rw [hw]; rw [integral_add (f:=d) (g:=fun x=> I*e x) ((hr.mul hf).integrableOn_compact hc) ht',integral_const_mul,show (∫ x in K,d x ∂μ)=0 from moment_real hc hf ht hb hp (Complex.continuous_re.comp_continuousOn h),show (∫ x in K,e x ∂μ)=0 from moment_real hc hf ht hb hp (Complex.continuous_im.comp_continuousOn h)]; ring
include hg
lemma moment_eq (hp:∀ n:ℕ, (∫ x in K,(↑(t x):ℂ)^n*F x ∂μ)=∫ x in K,(↑(t x):ℂ)^n*G x ∂μ) {g:ℝ→ℂ} (h : ContinuousOn g (Icc 0 b)) : (∫ x in K, g (t x)*F x ∂μ)=∫ x in K,g (t x)*G x ∂μ:=by
   let f:= F-G;have he(A:X→ℂ)(hA:ContinuousOn A K):(∫ x in K,A x*f x ∂μ)=(∫ x in K,A x*F x ∂μ)-(∫ x in K,A x*G x ∂μ):=by
       unfold f;simp_rw [Pi.sub_apply,mul_sub]; exact integral_sub ((hA.mul hf).integrableOn_compact hc) ((hA.mul hg).integrableOn_compact hc)
   apply sub_eq_zero.mp; rw [← he (fun x=>g (t x)) (h.comp ht hb)]; refine moment_complex hc (hf.sub hg) ht hb (fun n=>?_) h; change ∫ x in K,(↑(t x):ℂ)^n*f x ∂μ=0; rw [he (fun x=> (↑(t x):ℂ)^n) ((continuous_ofReal.comp_continuousOn ht).pow n),hp n, sub_self]
end
end YM.MSbar.Dim
