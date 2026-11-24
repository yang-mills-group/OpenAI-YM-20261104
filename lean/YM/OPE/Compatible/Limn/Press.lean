import YM.OPE.Compatible.Limn.Sport
/-! # All ray budgets with cap on regression forms -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side} {X Y:Type}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f}{F:Forest S.ratio} {I:Seats F}
open Finset Module
open Green (wt)
section
variable [Fintype X] [Fintype Y]{s:X→Site f}{p:Y→Site f}{A:Matrix X Y ℝ}
lemma prow (h:Pours A s p t R)(ht:0<t)(i:X): ∑ j:Y,|A i j| ≤ R:=by simpa only [Wisps.rate,zero_mul,Real.exp_zero,one_mul] using (h.weaker ht.le le_rfl).row i
lemma Hymn (v:Y→ℝ)(h:Pours A s p t R)(ht:0<t)(hv:∀ i,|v i|≤ b)(hb:0≤b)(x:X): ‖(A*ᵥ v) x‖≤ R*b:=by
         apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (prow h ht x) hb); rw [sum_mul]; apply Finset.sum_le_sum; intro i _; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
lemma CoverSlip (u:Y→Prop)[DecidablePred u](ht:0<t)(h:Pours A s p t R)(x:X)(hv:∀ y:Y,u y→ε ≤ separation (s x) (p y)): ∑ i:Y, (if u i then ‖A x i‖ else 0) ≤ Real.exp (-(t*ε))*R:=by
         refine le_trans (sum_le_sum (g:=fun i=> Real.exp (-(t*ε)) * (Wisps.rate t (separation (s x) (p i)) * |A x i|)) fun i _=> ?_) ?_
         · split
           next ht'=> rw [←mul_assoc, Wisps.rate,←Real.exp_add]; exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (sub_nonneg.mpr (mul_le_mul_of_nonneg_left (hv i ht') ht.le)|>.trans_eq (show _ = - (t*ε) + t * (separation _ _:ℕ) from (by ring))))
           exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Wisps.rate_pos ..).le (abs_nonneg _))
         rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (h.row x) (Real.exp_nonneg _)
end
section
lemma Cast_price [Fintype X][DecidableEq X](x:Keys G X)(u:X × G.ColorIndex): ‖cash (Tip G X) x u‖ ≤‖x‖:=by
       rw [Tip_ψ]; apply le_trans _ (norm_le_pi_norm x u.1); exact (PiLp.norm_apply_le _ _).trans le_rfl -- name
abbrev crestPrice (G:Gauge)(s:ℝ):= ((Fintype.card G.ColorIndex):ℝ) * s
lemma Tip_T [Fintype X][DecidableEq X](x:Keys G X)(ht:0 ≤ t)(hz:∀ i, ‖cash (Tip G X) x i‖ ≤ t): ‖x‖ ≤ crestPrice G t :=by
        apply (pi_norm_le_iff_of_nonneg (show 0 ≤ crestPrice G t from mul_nonneg (Nat.cast_nonneg _) ht)).2; intro i; let A:=EuclideanSpace.basisFun G.ColorIndex ℝ; rw [← A.sum_repr (x i)]; apply (norm_sum_le ..).trans; apply le_trans (Finset.sum_le_sum (g:=fun j:G.ColorIndex=>t) (fun j _=>?_)) (le_of_eq (by rw [sum_const,card_univ,nsmul_eq_mul])); rw [norm_smul,OrthonormalBasis.norm_eq_one,mul_one]; specialize hz (i,j); rw [Tip_ψ] at hz; exact hz -- defeq?
-- T extension regression outside formula
variable (B: Matrix (Key F G) (Key F G) ℝ)(I:Seats F)
local notation "Iζ"=>Key F G
local notation "jμ"=>clipRail S F I B
lemma Evoke {v:ℝ}(h:Pours (clipRail S F I B) (pointK S F∘ shout G I) (pointK S F) t v)(hb:0<t)(C:Law (AxisChart G F))(ht:Trained (countingBasis F G) B C)(hm:B.PosDef)(x:AxisChart G F): ‖ChartUp S F I C x‖ ≤ crestPrice G (v*‖x‖) :=by
          apply Tip_T _ (mul_nonneg h.pos (norm_nonneg _)); intro i; rw [hop _ _ _ _ _ ht hm]; exact Hymn _ h hb (fun i=> Cast_price x _) (norm_nonneg _) i
abbrev dark (j:Key F G) := j.1 ∉ I
lemma Adu (C:Law (AxisChart G F))(h:Trained (countingBasis F G) B C)(ht:B.PosDef)(x:AxisChart G F)(p:Rubric G I): cash (Tip G (↥I)) (ChartUp S F I C x) p= cash (countingBasis F G) x (shout G I p)+ ∑ i:Key F G, if dark I i then clipRail S F I B p i * cash (countingBasis F G) x i else 0:=by
       let T:=shout G I; let v:= ChartUp S F I C; let L:=clipRail S F I B; let u:=cash (countingBasis F G) x
       have hp(i:Iζ)(hx:i.1 ∈ I): L p i= if T p=i then 1 else 0:=by
            let j:Rubric G I:= (⟨_,hx⟩,i.2); have hv:T j=i:=rfl; change L p (T j)=_; rw [show L p (T j)= _ from boots S F I B C h ht p j]; by_cases hP:T p=i; · rw [if_pos hP, if_pos (T.injective (hv.trans hP.symm))]
            rw [if_neg hP, if_neg (show j≠p from fun he=> hP (he ▸ hv))]
       rw [hop _ _ _ _ _ h ht]; change ∑ i,L p i*u i=u _ +_; let f(i:Iζ):= if T p=i then (1:ℝ)*u i else 0; have hx(i:Iζ): L p i*u i=f i+(if dark I i then L p i*u i else 0):=by
            by_cases ht:dark I i
            · unfold f; rw [if_pos ht,if_neg (fun (hh:T p=i)=> ht (hh ▸ p.1.property)),zero_add]
            rw [hp i (Classical.not_not.mp ht),if_neg ht,add_zero]; unfold f; split <;> first|rfl|apply zero_mul
       rw [show u (T p)=∑ i:Iζ,f i from ?_, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=>hx i
       unfold f; simp
end
end YM.OPE.Limn
