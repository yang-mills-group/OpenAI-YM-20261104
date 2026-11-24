import YM.MS.Arc.R1
import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.FastTrees
/-!
# Uniform dimensional sweep derivatives

Use unit-parameter estimates before any integrations. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open ContinuousLinearMap
variable {I E F G A B: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F][NormedAddCommGroup G][NormedSpace ℝ G]
variable {z:UScale I}{u v:I→ Tree E F}{a:I→ℝ}
omit [CompleteSpace F] in
lemma Q.at_d (h:quiet z u a): quiet z (fun i=>d (u i)) a:= (Q.fder h).L (apply ℝ F ((1,0):ℝ×E))
private def row (x:ℝ): ℝ× E →L[ℝ] (ℝ× E):= (x • fst ℝ ℝ E).prod (snd ℝ ℝ E)
private lemma row_eq (x:ℝ)(p:ℝ×E): row x p=(x*p.1,p.2):= rfl
private lemma row_pay (x:ℝ)(h:0≤x)(he:x≤1): ‖row (E:=E) x‖≤1:=by
   refine opNorm_le_bound _ zero_le_one (fun p=>?_); rw [row_eq,Prod.norm_def,Prod.norm_def,norm_mul,norm_of_nonneg h,one_mul]; exact max_le_max (mul_le_of_le_one_left (norm_nonneg _) he) le_rfl

lemma Q.at_chop (h:quiet z u a) (hh:∀ i, Reflect (u i)): quiet z (fun i=>chop (u i)) a:= by
   let v i:=d (d (u i)); have hV: quiet z v a:= Q.at_d (Q.at_d h); let μ:= (volume.restrict (Ioc (0:ℝ) 1)); have hQ : Heat.Cour μ := ⟨Icc 0 1,isCompact_Icc,(ae_restrict_mem measurableSet_Ioc).mono fun p hp=>Ioc_subset_Icc_self hp⟩
   intro b; induction b with
   | zero=>
       refine ⟨fun i=> c_chop (h.smooth i),fun j=>?_⟩; obtain ⟨C,hC,b,hb⟩:= (hV 0).quoted j; refine ⟨C,hC,b,fun i p _=>?_⟩
       have he: Majorant μ (fun t p=> v i (row t p)):=Heat.Lot (volume.restrict (Ioc (0:ℝ) 1)) hQ ((hV.smooth i).comp (show ContDiff ℝ ∞ (fun q:ℝ× (ℝ×E)=> (q.1*q.2.1,q.2.2)) by fun_prop)); dsimp only; rw [show chop (u i)=(fun p=> ∫ t,v i (row t p) ∂μ) from funext fun p=> intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1), he.identity];
       let X:= (stump z).cheap i p; let V:= C* X^b*(a i); simp only [cheap_length,one_pow,pow_zero,div_one,mul_one]; change ‖(∫ t, iteratedFDeriv ℝ j _ _ ∂μ)‖ ≤ V
       have hν : ( volume.restrict (Ioc (0:ℝ) 1)).real univ=1:= by simp -- maybe `measureReal_def`
       haveI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1))); refine le_trans (norm_integral_le_of_norm_le (integrable_const (μ:=μ) V) ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht=>?_))) ?_
       · rw [show (fun p=>v i (row t p))=(v i) ∘ (row t) from rfl,(row t).iteratedFDeriv_comp_right (hV.smooth i) p (by exact_mod_cast le_top)]; apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..); simp only [Finset.prod_const,Finset.card_univ, Fintype.card_fin]; refine (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (row_pay t ht.1.le ht.2))).trans ?_; simpa only [V,X,stump,Scale.slow,row_eq,cheap_length,pow_zero, div_one,one_pow,mul_one] using hb i (row t p) (mem_univ _)
       simp only [integral_const, show μ.real Set.univ=1 from hν,one_smul, le_refl]
   | succ b ih=> exact stack_step (fun i p=> restore (hh i) (h.smooth i) p.1 p.2) ih (Q.at_d h b)
omit [CompleteSpace F] in lemma met (f:Tree E F): pruning 0 f=f:=rfl
-- recursion via chop
omit [CompleteSpace F] in lemma spent (b:ℕ) (f:Tree E F): pruning (b+1) f=chop (pruning b f):= Function.iterate_succ_apply' chop ..
lemma pruned (h:quiet z u a)(H:∀ i, Reflect (u i))(b:ℕ): quiet z (fun i=> pruning b (u i)) a∧∀ i, Reflect (pruning b (u i)):= by
   induction b with
   | zero=> exact ⟨h,H⟩
   | succ b ih=> simp_rw [spent]; exact ⟨Q.at_chop ih.1 ih.2,fun i=>chop_even (ih.2 i) (ih.1.smooth i)⟩
end YM.MS.Arc
