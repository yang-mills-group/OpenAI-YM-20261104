import YM.MS.Drops.Shadow
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
variable {G:Gauge}
variable (L K:Degree G)
local notation "U" => xy (fax L) (fax K)
lemma pay_positive (s:ℝ): 0<Pay s:= by unfold Pay τ; positivity
lemma hand (s:ℝ) : Integrable (fun w:E4=> wearΦ L K s w):= by
    have hv:=pay_positive s; let f(a b:ℂ):= a+(exp s)^2 • b; obtain h:= downE L K ( passion hv ); obtain hU:= downE L K (majorM hv); exact ( h.integral.add ( hU.integral.smul ( exp s ^2 ) ) ).congr ( lit_ae.mono fun t ht=> ( lease_s L K s _ ht ).symm )
variable {s u v:ℝ}
abbrev ntC (w u:ℝ): ℝ:= 2*τ^2*exp w^4*u^2
lemma nt_pos (v:ℝ)(w:E4): 0≤ ntC v ‖w‖:= by unfold ntC; positivity
lemma phaseQ (w:E4)(s:ℝ): ‖major (Pay s) w‖=exp (-Pay s*‖w‖^2):= Eq.trans (Complex.norm_real _) ( Real.norm_of_nonneg (exp_pos _|>.le))
lemma scales (t:ℝ)(w:E4): ‖stage0 L K t w‖= ntC t ‖w‖ * ‖U (ν w)*major (Pay t) w‖:= by rw [stage_v,norm_mul,norm_mul (U _), Complex.norm_real, ν_sq, norm_mul (U _)]; unfold ntC leaseTax; rw [ show -2*exp t^4*(τ^2 * ‖w‖^2) = -(ntC t ‖w‖) from (by unfold ntC; ring), norm_neg, Real.norm_of_nonneg ( nt_pos t w ) ]; unfold ntC; ring
lemma basin (h:s∈ Set.Icc u v) (w:E4) : ‖stage0 L K s w‖≤ ntC v ‖w‖ * ‖U (ν w)*leaseTax u w‖:= by rw [ scales ]; have hU:=h.1; have hv:= h.2; have hx := pay_positive s; apply mul_le_mul _ _ (norm_nonneg _) (nt_pos v w); unfold ntC; gcongr; unfold leaseTax; rw [norm_mul,norm_mul, phaseQ,phaseQ,neg_mul,neg_mul]; unfold Pay τ; gcongr
lemma winds0 (s u:ℝ): Integrable (fun w:E4=>ntC u ‖w‖ * ‖U (ν w)*leaseTax s w‖):= by
   obtain hp:= downE L K ( majorM ( pay_positive s ) ); simp_rw [ntC,mul_assoc ((2*τ^2*exp u^4):ℝ) ]; exact (hp.price 2).const_mul _
lemma stage_h (s:ℝ): Integrable (stage0 L K s):= by
    have he : AEStronglyMeasurable (fun t:E4=>U (ν t)*leaseTax s t):= ( downE L K ( majorM ( pay_positive s ) ) ).integral.aestronglyMeasurable
    apply (winds0 L K s s).mono' _ (Eventually.of_forall fun i=> ( scales L K s i ).le);
    have h : AEStronglyMeasurable (fun w:E4=> U (ν w)*leaseTax s w*(((-2*exp s^4* Momentum.sq (ν w):ℝ)):ℂ)) volume:= he.mul (f:=fun t=> U (ν t)*leaseTax s t) (g:= fun w=> (((-2*exp s^4* Momentum.sq (ν w):ℝ)):ℂ)) (by simp_rw [ν_sq]; fun_prop)
    rw [ show stage0 L K s=( fun w=> _ ) from funext fun w=> ?_ ]; exact h; rw [ stage_v ]; ring
-- derivatives already h continuity.
lemma listener (F:E4→ℂ)(hp:Integrable F)(x:E4): Integrable (fun p=> Radian.wave x p* F p):= hp.bdd_mul (by unfold Radian.wave; fun_prop) (Eventually.of_forall (p:=fun i=> ‖Radian.wave x i‖≤1) (by simp))
abbrev γX (L K:Degree G)(x:E4)(s:ℝ):= harmon (wearΦ L K s) x
def pair_slope (f g:Local.BV.Grade G)(x:QP)(s:ℝ):= 2* ∫ p:QP, Tone.bill x p * Cdeg f g s p ∂planeF
lemma budget (s:ℝ)(x:E4): harmon (stage0 L K s) x= -pair_slope (fax L) (fax K) (out x) s:= by
   rw [ Radian.wind, pair_slope, ← ampFπ.integral_comp (ν.toHomeomorph.measurableEmbedding) (fun p=>Tone.bill _ p * _) ]; rw [← neg_mul, ← integral_const_mul ]; refine integral_congr_ae (Eventually.of_forall fun p=>?_); dsimp only; rw [ν_bill]; exact mul_left_comm ..
lemma receipt (s:ℝ)(x:E4): HasDerivAt (γX L K x) (-pair_slope (fax L) (fax K) ( out x ) s) s:= by
    let F(t:ℝ)(p:E4):= Radian.wave x p* wearΦ L K t p; let H(t:ℝ)(p:E4):= Radian.wave x p*stage0 L K t p; have he (t:ℝ): Integrable (F t):= listener _ ( hand L K t ) x; let b(t:E4):= ntC (s+1) ‖t‖ * ‖U (ν t)* leaseTax (s-1) t‖
    obtain ht:= hasDerivAt_integral_of_dominated_loc_of_deriv_le ( Icc_mem_nhds (show s-1<s by linarith) (show s<s+1 by linarith) ) ( Eventually.of_forall fun t=> (he t).aestronglyMeasurable ) ( he s ) ( show AEStronglyMeasurable ( H s ) volume from ( listener _ (stage_h L K s) x ).aestronglyMeasurable ) ( bound:=b ) ( Eventually.of_forall fun k=> fun t ht=> show ‖H t k‖≤ _ from (by unfold H; rw [norm_mul,price_wave,one_mul]; exact basin L K ht k ) ) ( winds0 L K (s-1) (s+1) ) (Eventually.of_forall fun t=> fun u hu=> (dark_w L K t u).const_mul _ ) -- Bool hx
    rw [ ← budget, show γX L K x=fun t=>∫ p,F t p from funext fun i=> Radian.wind _ _, Radian.wind ]; exact ht.2
end YM.MS.Drops
