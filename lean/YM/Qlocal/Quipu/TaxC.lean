import YM.Qlocal.Quipu.Tax
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Vase
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V} (s':V→Site c) {s:Senses R}(A:Vase s G n)(x:Site c)(W:Config G c) (z:ℕ)(M:Ambient G c)
def brand (b:Bool)(G:Gauge)(n:ℕ)(x:Site c)(s:Walk): Ambient G c→CColor G:= if b then hype G n x s else slopePath G x s
lemma physical_ (q:Bool)(l:Walk): brand q G z x l (physical W) = colorUp G (amend G z q (travel W x l)):= by
 unfold brand amend; split; exact hypeActual G z x l W
 unfold slopePath; rw [stringMat_physical,stringMat_physical,travel_reverse,colorProject_skew]; rfl; simp only [star_smul,star_trivial,G.mat_inv,star_sub,star_star,← smul_neg,neg_sub]
lemma brand_l (b:Bool)(l:Walk): ContDiff ℂ ω (brand b G z x l):= by
 unfold brand; split; exact hypeDiff G z x l
 unfold slopePath; exact (colorProject G).contDiff.comp (((stringMat_contDiff l x).sub (stringMat_contDiff ..)).const_smul _)
def swatch (A:Vase s G n)(x:Site c)(z:ℕ)(M:Ambient G c):ℂ:= ∑ i:Ink G n, (A.ink i:ℂ) * ∏ j:Fin n, brand (A.tan j) G z x (A.maps j).tour M (i j)
lemma real_bill : swatch A x z (physical W)=(read A x z W:ℂ):= by
 unfold swatch; rw [globe]; unfold Noon.bump; simp_rw [physical_]; push_cast; rfl
lemma reign : ContDiff ℂ ω (swatch A x z):= ContDiff.sum (fun _ _=> contDiff_const.mul (contDiff_prod fun i _=> (contDiff_apply ℂ _ _).comp (brand_l ..)))
local notation "X"=> Lasso.bire z a
abbrev stature (z:ℕ)(a:ℝ):= Work.F02.radius (bire z a)
def ticketC (G:Gauge)(z n:ℕ):= (Lasso.quote G z+Lasso.ticket G)^n
lemma ticketC_pos (G:Gauge)(z n:ℕ): 0≤ ticketC G z n:= pow_nonneg (add_nonneg (Lasso.quote_pos G z).le (zero_le_one.trans (Lasso.ticket_ge ..))) _
variable (h:0<a)(hh:M∈ Metric.ball (physical W) (stature z a))
include h hh
lemma promotes (u: Bool)(s:Walk): ‖brand u G z x s M‖ ≤ (Lasso.quote G z+ Lasso.ticket G) * Real.exp (a*s.length):= by
 unfold brand; let Q:=Lasso.ticket G; split; · exact (cost_hype G h z _ _ _ M (ball_subset_closedBall hh)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one.trans (ticket_ge ..))) (Real.exp_pos _).le)
 have hv : bire z a/2 ≤ a:= le_trans (half_le_self (bire_pos h _).le) (div_le_self h.le (by exact le_add_of_nonneg_left (Nat.cast_nonneg _)))
 exact (cost_berry G W s x (bire_pos h z) M (ball_subset_closedBall hh)).trans (mul_le_mul (le_add_of_nonneg_left (quote_pos ..).le) (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _))) (Real.exp_pos _).le (by have hh:= ticket_ge G; have hv:= quote_pos G z; positivity))
lemma ferried : ‖A.swatch x z M‖≤ ticketC G z n*A.fare a:= by
 unfold swatch fare sizeC; let P:= Lasso.quote G z+ Lasso.ticket G; have hp:0 ≤ P:=add_nonneg (quote_pos ..).le (zero_le_one.trans (ticket_ge ..)); let X':=ticketC G z n * Real.exp (a*A.momentum)
 have hv(i:Ink G n): ‖∏ j:Fin n, brand (A.tan j) G z x (A.maps j).tour M (i j)‖ ≤ X':= by
    rw [norm_prod]; apply (prod_le_prod (fun i _=> norm_nonneg _) (g:=fun i:Fin n=> P * Real.exp (a*(A.maps i).tour.length)) (fun i _=> (norm_le_pi_norm ..).trans (promotes x W z M h hh ..))).trans; rw [prod_mul_distrib, ← Real.exp_sum,← Finset.mul_sum]; unfold X'; rw [prod_const, Finset.card_univ,Fintype.card_fin]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (pow_nonneg hp n); apply mul_le_mul_of_nonneg_left _ h.le; exact_mod_cast (show ∑ i: Fin n, (A.maps i).tour.length ≤ A.momentum from (Finset.sum_le_sum (g:=fun i =>(A.maps i).range + (A.maps i).tour.length) (fun i _=> Nat.le_add_left ..)).trans (Nat.le_add_right ..)) -- maybe cast sum direction
 rw [mul_left_comm (ticketC ..) (∑ i:Ink G n,|A.ink i|), Finset.sum_mul]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum (fun i _=>?_); rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
omit hh
lemma openness (z:ℕ):0<stature z a:= radius_pos (bire_pos h _)
lemma paid (z:ℕ): |read A x z W|≤ ticketC G z n*A.fare a:= by rw [← Real.norm_eq_abs, ← Complex.norm_real, ← real_bill]; exact ferried A x W z (physical _) h (mem_ball_self (openness h z))
end YM.Qlocal.Quipu.Sonnet.Vase
