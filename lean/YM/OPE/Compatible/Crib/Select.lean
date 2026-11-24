import YM.OPE.Compatible.Crib.Snack
/-! # Numeric germ Lipschitz of Mark on tangents. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set Finset
open scoped Topology BigOperators Classical ContDiff
open Silt Cloud Tensor PertExtension Flume Flume.Page Flume.Script Jargon Score Drift GaussianScore Series Libra Shell Char Spells Radial Stranded
variable {E:Type}{r s t D x C:ℝ}{p q k:ℕ}
variable [NormedAddCommGroup E][NormedSpace ℝ E]
section interp
abbrev γ (x:E→ℝ)(i:ℕ)(z y:E):= iteratedFDeriv ℝ i x z (fun _=>y)
lemma lance {p:E→ℝ}(h:ContDiff ℝ 2 p) (a x:E): pointD a (pointD a p) x= γ p 2 x a:=by
     unfold γ; let v:=fun _:Fin 1=>a; rw [show (fun _:Fin 2=> a)=Fin.cons a v from (by funext i;fin_cases i<;> rfl), Analysis.cons_inner (f:=p) (j:=1) (by exact_mod_cast h.contDiffAt),iteratedFDeriv_one_apply];rfl

lemma Gaff {x y v w:E}(p:E→ℝ)(u t' b:ℝ) (h:‖x‖ ≤  t)(ht:‖y‖ ≤ t)(hp:‖v‖ ≤ s)(hz:‖w‖ ≤ s)(he:‖x-y‖ ≤ u) (hv:‖v-w‖  ≤  t') (hr:ContDiff ℝ 3 p)(hm:∀ i:ℕ,i ≤  3 →∀ x:E,‖x‖ ≤ t→ ‖iteratedFDeriv ℝ i p x‖  ≤  b) :∀ i:ℕ,i ≤  2 →
      ‖γ p i x v- γ p i y w‖ ≤  b*u*s^i+b*i*t'*s^(i-1):=by
        intro i hi; let X:=iteratedFDeriv ℝ i p x; let Y:=iteratedFDeriv ℝ i p y; have he' : (↑i:ℕ∞ω)<3:=by exact_mod_cast (show i < 3 by omega)
        have hh: ‖X-Y‖ ≤  b * ‖x-y‖:=by
              refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=iteratedFDeriv ℝ i p) (fun j _=>hr.differentiable_iteratedFDeriv he' j) (fun p hp=>norm_fderiv_iteratedFDeriv.trans_le (hm (i+1) (by omega) _ (mem_closedBall_zero_iff.mp hp))) (convex_closedBall 0 t) (mem_closedBall_zero_iff.mpr ht) (mem_closedBall_zero_iff.mpr h)
        have hB:=hm i (by omega) y ht; have hb:0 ≤ b:=(norm_nonneg _).trans hB; have hs:0  ≤ s:=(norm_nonneg _).trans hp
        rw [show γ p i x v-γ p i y w=(X-Y) (fun _=>v)+(γ p i y v- γ p i y w) from by rw [_root_.sub_apply]; unfold X Y γ;ring]; apply (norm_add_le ..).trans; apply add_le_add
        · apply ((X-Y).le_opNorm ..).trans; rw [prod_const, card_univ,Fintype.card_fin]; exact mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left he hb)) (pow_le_pow_left₀ (norm_nonneg _) hp _) (pow_nonneg (norm_nonneg _) _) (mul_nonneg hb ((norm_nonneg _).trans he))
        unfold γ; clear he'; interval_cases i
        · simp only [iteratedFDeriv_zero_apply,sub_self,norm_zero,Nat.cast_zero,mul_zero,zero_mul]
          exact le_rfl
        · simp only[iteratedFDeriv_one_apply,Nat.cast_one,mul_one,Nat.sub_self,pow_zero]; rw [← _root_.map_sub]; refine ((fderiv ℝ p y).le_opNorm _).trans (mul_le_mul ?_ hv (norm_nonneg _) hb); rwa[← norm_iteratedFDeriv_one]
        let A:=iteratedFDeriv ℝ 2 p y; have hP (i j:E){u t:ℝ}(hi:‖i‖  ≤  t)(hj:‖j‖  ≤ u): ‖A ![i,j]‖  ≤  b*(t*u):=by
             have ht:0  ≤ t:=(norm_nonneg _).trans hi; apply (A.le_opNorm ..).trans; rw [Fin.prod_univ_two]; exact mul_le_mul hB (mul_le_mul hi hj (norm_nonneg _) ht) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb
        have he(i:E): (fun _:Fin 2=>i)=![i,i]:=funext fun j=>by fin_cases j <;>rfl
        rw [he,he,show A ![v,v] - A ![w,w] = A ![v-w,v]+ A ![w,v-w] from ?_]; apply (norm_add_le ..).trans; exact (add_le_add (hP _ _ hv hp) (hP _ _ hz hv)).trans_eq (by norm_num; ring)
        rw [show A ![v-w,v]=A ![v,v]-A ![w,v] from DFunLike.congr_fun (A.curryLeft.map_sub v w) ![v], show A ![w,v-w]=A ![w,v]-A ![w,w] from DFunLike.congr_fun ((A.curryLeft w).curryLeft.map_sub v w) ![]];ring
end interp
end YM.OPE.Crown
