import YM.OPE.Compatible.Squalls.Tower
/-! # common field signs from node coordinates -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
abbrev cross (i:Edge Cover)(s:Signed):= ((posDir i.2).rotate s).used (affine s 0 i.1)
def tide (i:Edge Cover)(s:Signed) : fieldX (Shade G) →ₗ[ℝ] G.Color:= if ((posDir i.2).rotate s).neg then -(indexS (cross i s)) else indexS (cross i s)
lemma tide_pose (U:fieldX (Shade G))(i:Edge Cover)(s:Signed): pull s 0 (lotU U) i= G.lieExp (tide i s U):=by
    unfold pull Step.read; split
    next h=> unfold tide; erw [if_pos h]; exact (Work.F03.exp_neg_color _).symm
    next h=> unfold tide; rw [if_neg h];rfl
lemma spin_flat (s:Signed)(x: fieldX (Shade G))(h:Low x 0)(a b:Cover)(k:Axis): tide (a,k) s x=tide (b,k) s x:=by
    unfold tide cross Step.used; simp only; cases e: ((posDir k).rotate s).neg
    · simp only [Bool.false_eq_true,if_false]; rw [idleX x h _ _ _]
    simp only [if_true,LinearMap.neg_apply]; rw [idleX x h _ _ _]
lemma spin_shear (s:Signed)(x:fieldX (Shade G))(h:Low x 1)(a b c:Cover)(k:Axis): tide (a+c,k) s x-tide (a,k) s x=tide (b+c,k) s x-tide (b,k) s x:=by
    unfold tide cross Step.used; simp only; simp only [affine, Signed.act_add, add_zero]; cases e: ((posDir k).rotate s).neg
    · simp only [Bool.false_eq_true,if_false]; exact cuddle h ..
    simp only [if_true, LinearMap.neg_apply]; rw [add_sub_right_comm (s.act a),add_sub_right_comm (s.act b)]; simp only [show ∀ x y:G.Color, -x- -y= -(x-y) from fun x y=> by abel]; exact congr_arg Neg.neg (cuddle h ..)
variable [Fintype I] {k:I→ℕ}
def idleStem (x:I→fieldX (Shade G))(k:I→ℕ)(s:Signed)(b:Axis) := ∑ i, if k i=0 then tide (0,b) s (x i) else 0
def stemDer (x:I→fieldX (Shade G))(k:I→ℕ)(s:Signed)(b:Axis)(d:Cover):= ∑ i, if k i=1 then tide (0+d,b) s (x i)-tide (0,b) s (x i) else 0
abbrev vows (k:ℕ)(p:ℝ→E) [SMul ℝ E](t:ℝ):=(t^k)⁻¹ • p t
variable {x:I→fieldX (Shade G)}
lemma spoutX_lil (a:Edge Cover)(s:Signed): lil fun t=>tide a s (spout x k t):=by
    unfold spout; simp_rw [map_sum,map_smul]; have hh(i:I): Tendsto (fun t:ℝ=> t^(k i+1) • tide a s (x i)) Hemi (𝓝 0):=by simpa using ((show Tendsto (fun t:ℝ=>t) Hemi (𝓝 0) from tendsto_id.mono_left nhdsWithin_le_nhds).pow (k i+1) |>.smul_const (tide a s (x i)))
    convert! tendsto_finsetSum univ (fun i _=> hh i) using 1; simp
lemma spoutShape (h:radiantX x k)(s:Signed)(b:Cover)(j:Axis): sideLimit (fun t=>t⁻¹ • tide (b,j) s (spout x k t)) (idleStem x k s j):=by
    unfold spout idleStem; simp_rw [map_sum,map_smul,Finset.smul_sum]; apply tendsto_finsetSum; intro i _; have he := (show Tendsto (fun t:ℝ=> t) Hemi (𝓝 0) from tendsto_id.mono_left nhdsWithin_le_nhds).pow (k i) |>.smul_const (tide (b,j) s (x i))
    have hp : (0:ℝ)^(k i) • tide (b,j) s (x i)= if k i=0 then tide (0,j) s (x i) else 0:=by
       by_cases ht:k i=0; · rw [ht,if_pos rfl,pow_zero,one_smul,spin_flat s _ (ht ▸ h i) b 0]
       rw [zero_pow ht,if_neg ht,zero_smul]
    rw [hp] at he; apply he.congr'; filter_upwards [show ∀ᶠ x in Hemi,0<x from self_mem_nhdsWithin] with t ht; rw [smul_smul,pow_succ',inv_mul_cancel_left₀ ht.ne']
lemma spoutShift (h:radiantX x k)(s:Signed)(b c:Cover)(j:Axis): sideLimit (fun t:ℝ=>(t^2)⁻¹ •(tide (b+c,j) s (spout x k t)-tide (b,j) s (spout x k t))) (stemDer x k s j c):=by
    unfold spout stemDer; simp_rw [map_sum,map_smul,← Finset.sum_sub_distrib,← smul_sub,Finset.smul_sum]; apply tendsto_finsetSum univ; intro i _; by_cases he:k i=0
    · simp_rw [spin_flat s _ (he ▸ h i) (b+c) b,sub_self,smul_zero]; rw [if_neg (by omega : ¬ k i=1)]; exact tendsto_const_nhds
    let J:=tide (b+c,j) s (x i)-tide (b,j) s (x i); let n:= k i-1
    have ht:= (show Tendsto (fun t:ℝ=> t) Hemi (𝓝 0) from tendsto_id.mono_left nhdsWithin_le_nhds).pow n|>.smul_const J
    have hv : k i=n+1:= by unfold n; omega
    rw [show (0:ℝ)^n • J= if k i=1 then tide (0+c,j) s (x i)-tide (0,j) s (x i) else 0 from by
       split
       next hp=> rw [show n=0 by omega,pow_zero,one_smul]; exact spin_shear s _ (hp ▸ h i) b 0 c j
       next hp=> rw [zero_pow (by omega),zero_smul]] at ht
    apply ht.congr'; filter_upwards [show ∀ᶠ x in Hemi,0<x from self_mem_nhdsWithin] with t ht; change t^n • J= (t^2)⁻¹ •t^(k i+1) • J; rw [smul_smul,show k i+1=2+n by omega,pow_add,inv_mul_cancel_left₀ (pow_ne_zero _ ht.ne')]
end Script
end YM.OPE.Flume
