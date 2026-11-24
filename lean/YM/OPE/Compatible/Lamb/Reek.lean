import YM.OPE.Compatible.Porch.Halt
/-! # chart-specific rates through two orders -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Push Push.AbsoluteSums
variable {G:Gauge}{X:Type}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin Set
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local
variable {t r R B b ε C k':ℝ}{m:ℕ}
variable {S:StepData c f} {F: Forest S.ratio} {k:S.Choices}
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
open Dew
section
variable {P:ChartRatio G} (N: LocalRatio P)
include N
lemma fade_fee (x:G.Color)(h: x∈ ball (0:G.Color) P.radius): ContDiffAt ℝ ω (rake P) x:= (N.germ x h).log (N.pos _ h|>.ne')
structure StackP (P:ChartRatio G) (r R t:ℝ):Prop where
       sweep : Sweep P r R
       pays : 0 ≤ t ∧ ∀ x∈ ball (0:G.Color) r,∀ i:ℕ,i≤ 3 → ‖iteratedFDeriv ℝ i (rake P) x‖ ≤ t
lemma LiftFee:∃ r R t:ℝ,StackP P r R t:=by
       choose c hc h using fun i:Fin 4=> ceilingD (rake P) (Chart.small G P) (fun x hx=> fade_fee N x (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact lt_of_le_of_lt (le_trans hx (min_le_left ..)) (half_lt_self N.patch)))) i
       let v:= ∑ i:Fin 4,c i; obtain ⟨r,R,hS,hA⟩:=request (p:=fun _=>True) N (Eventually.of_forall fun _=> trivial); refine ⟨r,R,v,⟨hS, sum_nonneg (s:=Finset.univ) (fun i _=>zero_le_one.trans (hc i)), fun x hx i hi=>?_⟩⟩; let p:Fin 4:=⟨i,by omega⟩; rw [mem_ball,dist_zero_right] at hx; exact (h p x (hx.le.trans hS.small.le)).trans (single_le_sum (fun i _=>zero_le_one.trans (hc i)) (mem_univ _))
lemma levy [Fintype X](x:Keys G X) (j:ℕ) : jet (feeX P) j x=∑ i:X, jet (rake P) j (x i):=by
       have h(i:X): ContDiffAt ℝ ω (fun x:Keys G X=>rake P (x i)) 0:= (jet_trunk N).1.comp (f:=fun x:Keys G X=>x i) 0 (contDiffAt_apply ..)
       unfold feeX jet; rw [iteratedFDeriv_fun_sum_apply (f:=fun i (x:Keys G X)=> rake P (x i)) (u:=univ) (fun i _=> (h i).of_le le_top),_root_.sum_apply,mul_sum]; apply sum_congr rfl; intro i _; apply congr_arg; let S:Keys G X→L[ℝ] G.Color:= ContinuousLinearMap.proj i; exact lin_rate_at (rake P) S 0 (jet_trunk N).1 j _
-- tax j at 0
omit N in lemma jetNull {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{P:E→ℝ}(hp:fderiv ℝ P 0=0)(x:E): jet P 1 x=0:=by simp[jet,iteratedFDeriv_one_apply,hp]
lemma feeTime [Fintype X](S:StackP P r R t)(x:Keys G X)(hε:0<ε)(hp:ε•x∈ball (0: Keys G X) r)(hv:‖x‖≤B): ‖feeX P (ε • x) - ε^2*jet (feeX P) 2 x‖ ≤ (Fintype.card X:ℝ)*(t*B^3*ε^3):=by
       let f:=rake P; have ht:= S.pays.1
       have he(i:X)(t':ℝ)(ht':t'∈Icc 0 ε): t' • x i ∈ ball (0:G.Color) r:=by
            rw [mem_ball,dist_zero_right,norm_smul, Real.norm_of_nonneg ht'.1]; have he':ε*‖x‖<r:= by rwa [mem_ball,dist_zero_right,norm_smul, Real.norm_of_nonneg hε.le] at hp
            exact lt_of_le_of_lt (mul_le_mul ht'.2 (norm_le_pi_norm ..) (norm_nonneg _) hε.le) he'
       rw [levy N, mul_sum,feeX, ← sum_sub_distrib]; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> t*B^3*ε^3) (fun i _=>?_)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul]));
       have hP := toll_W (x i) f hε 2 (t*B^3) (mul_nonneg ht (pow_nonneg ((norm_nonneg _).trans hv) _)) (fun j hj=> fade_fee N _ (ball_subset_ball (S.sweep.small.le.trans ((min_le_left ..).trans (half_le_self N.patch.le))) (he i j hj))) (fun j hj=>?_)
       · have h0:jet f 0 (x i)=0:=by simp [jet,f,rake,N.anchored]
         have h1:jet f 1 (x i)=0:=jetNull (jet_trunk N).2 _
         simpa only [sum_range_succ,sum_range_zero,mul_zero,h0,h1,zero_add,Nat.reduceAdd] using! hP -- cast
       apply (ContinuousMultilinearMap.le_opNorm ..).trans ((mul_le_mul (S.pays.2 _ (he i j hj) _ (le_refl 3)) ?_ (prod_nonneg (fun _ _=>norm_nonneg _)) ht)); rw [prod_const,card_univ,Fintype.card_fin]; exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm x _).trans hv) _
lemma feeCapital [Fintype X](S: StackP P r R t)(x:Keys G X){i:ℕ}(hi:i ≤ 3): ‖jet (feeX P) i x‖ ≤ (Fintype.card X:ℝ)*(t*‖x‖^i):=by
       rw [levy N]; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> t*‖x‖^i) (fun j _=>?_)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])); unfold jet; rw [norm_mul]; refine (mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr i.factorial_pos))).trans ?_
       apply (ContinuousMultilinearMap.le_opNorm ..).trans ((mul_le_mul (S.pays.2 _ (mem_ball_self S.sweep.sizes.1) _ hi) ?_ (prod_nonneg (fun _ _=> norm_nonneg _)) S.pays.1)); rw [prod_const,card_univ,Fintype.card_fin]; gcongr; exact norm_le_pi_norm ..
end
end YM.OPE.Zeph
