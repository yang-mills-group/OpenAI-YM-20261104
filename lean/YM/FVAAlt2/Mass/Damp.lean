import YM.FVAAlt2.Mass.Reading
import Mathlib.Analysis.Polynomial.Basic
/-! # Power/log bound polynomial rigidity and finite perturbations. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Mass
open Function Finset Filter MeasureTheory Topology Set Metric
open FormalOPE FormalOPE.RG10 RG10.Position.Grade
open MS MS.FVA.Currency
open scoped Topology BigOperators ContDiff Classical Polynomial
open Polynomial Real
lemma vanishes {f:ℝ→ℝ}(h:Polys f): Tendsto (fun x:ℝ=> f x/ exp x ) atTop (𝓝 0):=by
 obtain ⟨d,M,hp,H⟩:=h; let p:ℝ:= M * ( 2:ℝ )^d
 have ht := tendsto_pow_mul_exp_neg_atTop_nhds_zero d
 apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (g:=fun x:ℝ=>p*(x^d* exp (-x))) (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ ?_
 · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx; have he:0≤x:=zero_le_one.trans hx; rw [norm_div,norm_of_nonneg (exp_pos _).le]; apply div_le_of_le_mul₀ _ ( by positivity ) ?_ -- theorem order
   · have he:0≤p:=mul_nonneg hp (by positivity); positivity
   apply ( H x ).trans; rw [ exp_neg, mul_assoc p, mul_assoc (x^d),inv_mul_cancel₀ (exp_ne_zero x),mul_one,abs_of_nonneg he]; unfold p; rw [ mul_assoc M, ← mul_pow ]; gcongr; linarith
 simpa only [mul_zero] using ht.const_mul p
lemma blows (p:Polynomial ℝ)(h:Polys (fun x=>p.eval (exp x)))(hv:p.eval 0=0): p=0:= by
 have he : p.degree < Polynomial.degree (Polynomial.X (R:=ℝ)):= by
    apply (Polynomial.div_tendsto_atTop_zero_iff_degree_lt _ _ X_ne_zero).1
    apply ((vanishes h).comp Real.tendsto_log_atTop).congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; simp [ Real.exp_log hx ]
 by_contra hp; obtain hz:= (Polynomial.natDegree_lt_natDegree_iff hp).mpr he; rw [natDegree_X] at hz; rw [ eq_C_of_natDegree_eq_zero ( show p.natDegree=0 from (by omega)) ] at hp hv; rw [eval_C] at hv; exact hp (hv ▸ map_zero C)
lemma para_sums {I:Type}(s:Finset I)(f:I→ Polynomial ℝ)(q:ℝ): (∑ i∈s, f i ).eval q=∑ i∈s, (f i).eval q:= map_sum (evalRingHom q) f s
lemma dampen {I:Type}(s:Finset I)(a:I→ℕ)(f:I→ℝ)(h:∀ i∈s,a i=0→ f i=0)
    (hx:Polys (fun x=>∑ i∈s, moving (a i) x * f i)) : ∑ i∈s,f i=0:= by
 let p:= ∑ i∈s, C (f i) * X^(a i); have he : ∀ x,p.eval x=∑ i∈s, x^(a i)*f i:= fun x=> by unfold p; rw [para_sums];apply sum_congr rfl; intro i _; simp only [eval_mul,eval_C,eval_pow,eval_X]; exact mul_comm ..
 have ht:p=0:= by
   apply blows; · rw [show (fun x:ℝ=>p.eval (exp x))=_ from funext fun x=> he _]; exact hx
   rw [he]; refine sum_eq_zero fun i hi=>?_ ; by_cases e:a i=0; rw [h i hi e,mul_zero]; rw [zero_pow e,zero_mul]
 simpa [ht] using (he (1:ℝ)).symm
end YM.FVAAlt2.Mass
