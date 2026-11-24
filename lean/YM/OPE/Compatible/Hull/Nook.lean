import YM.OPE.Compatible.Hull.Loom
/-!
# uniform first comparison with stochastic low slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt Tensor Cloud
open Cascade.Paver Libra.Shell
variable {E F X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]{f:F→ℝ}
variable {I J:Type}{i j k r:ℕ}
section
variable [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (A:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
variable [Fintype I](S:E→L[ℝ] PAD I){C:ℝ}
def RinB (I:Type)[Fintype I](C:ℝ):ℝ := 1+ (Fintype.card I:ℝ)*((2:ℕ).factorial:ℝ)*C
lemma measRR (hp:∀ i:I, ‖Silt.chamber A S i i‖≤ C) (p:E→ℝ){U:ℝ}(hU:0 ≤ U) (h:∀ x:E, ‖p x‖≤ U*‖S x‖): ‖A.average μ p‖≤U*RinB I C:=by
       let L(i:I):= coQ S i; let F(i:I):E→ℝ:= ⇑(L i)^2; let q:E→ℝ:= (fun _=>1)+∑ i,F i; have he(i:I):Bond (F i):= (Bond.glyph (L i)).pow _; have hq:Bond q:= (Bond.keep _).add (Sumbond _ _ fun i _=>he i); have hs(x:E): 0 ≤ q x:=by unfold q; simp only [Pi.add_apply,Finset.sum_apply]; exact add_nonneg zero_le_one (sum_nonneg fun i _=>sq_nonneg _)
       have ht(x:E): ‖S x‖≤q x:=(pi_norm_le_iff_of_nonneg (hs x)).2 fun i=>by
            let y:ℝ:= S x i; unfold q; simp only[Pi.add_apply, Finset.sum_apply]; have hb:‖y‖≤1+y^2:=by rw [Real.norm_eq_abs]; nlinarith only [sq_abs y,sq_nonneg (|y|-1),abs_nonneg y]
            exact hb.trans (add_le_add_right (single_le_sum (f:=fun i=>F i x) (fun i hi=>sq_nonneg _) (mem_univ i)) 1)
       apply (boundedV A μ (q:=U • q) (runsG A μ (Stature.poly (Bond.scale U hq) 0)) (fun i=> (h i).trans (mul_le_mul_of_nonneg_left (ht i) hU))).trans; rw [scooted]; apply mul_le_mul_of_nonneg_left _ hU; unfold q RinB; rw [sun _ _ (Bond.keep _) (show Bond (∑ i,F i) from Sumbond _ _ fun i _=>he i),singleConst,science _ _ _ _ fun i _=>he i]; have he(i):A.average μ (F i) ≤ ((2:ℕ).factorial:ℝ)*C:= (Real.le_norm_self _).trans ((mediate μ A (L i) 1 _ (hp i)).trans_eq (by rw[pow_one])); apply add_le_add_right; exact (sum_le_sum (fun i hi=>he i)).trans_eq (by rw [Finset.sum_const,card_univ,nsmul_eq_mul];exact (mul_assoc ..).symm)
lemma RisRR {f:PAD I→ℝ}(h:Stature f k)(hi:i+1≤k)(hv:∀ i:I,‖Silt.chamber A S i i‖≤ C)(v:Fin i→ PAD I){b:ℝ}(hh:∀ x, ‖iteratedFDeriv ℝ (i+1) f x‖≤ b): ‖iteratedFDeriv ℝ i f 0 v - taxA A μ S f v‖ ≤ b*(∏ j,‖v j‖)* RinB I C:=by
      let F(x:PAD I):=iteratedFDeriv ℝ i f x; let p:E→ℝ:=fun _=> F 0 v; let q:= Fline f v ∘ S; let U:= ∏ j,‖v j‖; have hB:= (norm_nonneg _).trans (hh 0); have hU:0 ≤ U:= Finset.prod_nonneg fun j _=>norm_nonneg _
      rw [show iteratedFDeriv ℝ i f 0 v - taxA A μ S f v=A.average μ (p-q) from ?_]; swap; · rw [duneSub _ _ (p:=p) (q:=q) (runsG A μ (Stature.poly (Bond.keep _) 0)) (exil _ _ _ (h.mono (by omega:i ≤ k)) v)]; exact congr_arg (·-_ ) ((singleConst μ A _).symm)
      apply measRR A μ S hv (p-q) (mul_nonneg hB hU); intro x; let y:=S x; change ‖F 0 v-F y v‖≤ _; refine ((F 0-F y).le_opNorm v).trans ?_
      refine (mul_le_mul_of_nonneg_right ?_ hU).trans_eq (show b*‖y‖*U=b*U*‖y‖ from ?_) -- rename
      · have hX:= Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=F) (fun y _=> h.smooth.differentiable_iteratedFDeriv (Nat.cast_lt.mpr (by omega:i < k)) _) (fun y _=> norm_fderiv_iteratedFDeriv |>.trans_le (hh y)) (convex_univ (𝕜:=ℝ)) (Set.mem_univ y) (Set.mem_univ (0:PAD I)); simpa only [zero_sub,norm_neg] using hX
      ring
end
end YM.OPE.Jargon
