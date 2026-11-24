import YM.OPE.Compatible.Crib.Speck
/-! # surviving polynomial tensor costs. no log B within interpolation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set Finset
open scoped Topology BigOperators Classical ContDiff
open Silt Cloud Tensor PertExtension Flume Flume.Page Flume.Script Jargon Score Drift GaussianScore Series Libra Shell Char Spells Radial Stranded
variable {E:Type}{r s t D x C ε:ℝ}{p q k:ℕ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {f:E→ℝ}
omit [FiniteDimensional ℝ E] in lemma Wager (h:anthem k f)(hp:0  ≤ r)(hs:∀ y:E,‖y‖ ≤ s+1 → ‖f y‖ ≤ r)(x y:E)(hx:‖x‖  ≤ s): ‖pointD y f x‖  ≤ Glee k*r*‖y‖:=by
        apply ((fderiv ℝ f x).le_opNorm y).trans; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply norm_fderiv_le_of_lip' _ (mul_nonneg (GleeHi _) hp); filter_upwards [Metric.closedBall_mem_nhds x (show (0:ℝ)<1 by norm_num)] with i hi; rw [Metric.mem_closedBall,dist_eq_norm] at hi; exact Lap2 h x i le_rfl hi (fun y ht=>hs y (ht.trans (add_le_add_left hx _))) -- Point
lemma Lender (h:anthem k f)(x:E)(j:ℕ)(hp:0  ≤ r)(hx:‖x‖ ≤ t)(he:∀ y:E,‖y‖ ≤ t+j →‖f y‖ ≤ r): ‖iteratedFDeriv ℝ j f x‖  ≤ Glee k ^j *r :=by
      induction j generalizing f r with
      | zero=> simpa using he x (by rwa [Nat.cast_zero,add_zero])
      | succ j ih=>
           refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (pow_nonneg (GleeHi _) _) hp) (fun v=>?_); let y:= v (Fin.last j); let g:= pointD y f; have hh(i:E)(ht:‖i‖ ≤ t+j): ‖g i‖ ≤ Glee k*r*‖y‖:= Wager h hp (fun u hu=> he u (by simpa [add_assoc] using! hu)) i _ ht; have hv:= ih ((veils y h).bloat (show k-1  ≤ k by omega)) (mul_nonneg (mul_nonneg (GleeHi _) hp) (norm_nonneg y)) hh
           let A:=Fin.init v; rw [show iteratedFDeriv ℝ (j+1) f x v= Fline g A x from ?_]; apply ((iteratedFDeriv ℝ j g x).le_opNorm A).trans; apply (mul_le_mul_of_nonneg_right hv (prod_nonneg (fun _ _=>norm_nonneg _))).trans_eq; rw [Fin.prod_univ_castSucc]; unfold A y Fin.init; ring
           exact (congr_arg (iteratedFDeriv ℝ _ f x) (Fin.snoc_init_self v).symm).trans (congr_fun (rungs (h.cost.smooth.of_le le_top) A y) x)
structure Velvet (f:E→ℝ)(C:ℝ)(k:ℕ):Prop where
       pos : 0 ≤ C
       roll : ContDiff ℝ 3 f
       seats (j:ℕ)(hj:j≤3)(x:E) : ‖iteratedFDeriv ℝ j f x‖ ≤ C*(1+‖x‖)^k
noncomputable abbrev glueV (r:ℝ)(k:ℕ):= (max 1 (Glee k))^ (3:ℕ)*(r*4^k)
lemma scour (h:anthem k f)(hp:0 ≤ r)(hv:∀ x:E,‖f x‖  ≤ r*(1+‖x‖)^k):Velvet f (glueV r k) k:=by
       let g:=Glee k; have ht:= GleeHi k; constructor; exact mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left ..)) _) (by positivity)
       · exact h.cost.smooth.of_le le_top
       intro j hj x; let b:=(r*4^k)*(1+‖x‖)^k; have hB:0  ≤ b:=by unfold b; positivity
       have hz(y:E)(hm:‖y‖  ≤ ‖x‖ + j): ‖f y‖ ≤ b:= (hv y).trans (by unfold b; rw [mul_assoc,←mul_pow]; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) hp; have he:(j:ℝ)  ≤ 3:= Nat.cast_le.mpr hj; linarith only [he,hm,norm_nonneg x])
       apply (Lender h x j hB le_rfl hz).trans ((mul_le_mul_of_nonneg_right ?_ hB).trans_eq (show (max 1 (Glee k))^ (3:ℕ)* b= _ from (by unfold glueV b; ring))); exact (pow_le_pow_left₀ (GleeHi k) (le_max_right ..) _).trans (pow_le_pow_right₀ (le_max_left ..) hj)
noncomputable abbrev Rpot (r:ℝ)(k:ℕ):= glueV (((k+1:ℕ):ℝ)*r) k
lemma foldsP (p:Song E)(hp:∀ i≤k,‖p i‖  ≤ t): Velvet (Strike k p) (Rpot t k) k:=by
       have ht:= (norm_nonneg _).trans (hp 0 (by omega)); apply scour (sailCost p k) (by positivity); intro x; unfold Strike; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>t*(1+‖x‖)^k) (fun j hj=>?_)).trans_eq (by rw [sum_const,nsmul_eq_mul,card_range];ring)); unfold Tensor.diagonal; have hv:j  ≤ k:=Nat.le_of_lt_succ (mem_range.mp hj); apply ((p j).le_opNorm ..).trans; rw [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul (hp j hv) ((pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) hv)) (pow_nonneg (norm_nonneg _) _) ht
end YM.OPE.Crown
