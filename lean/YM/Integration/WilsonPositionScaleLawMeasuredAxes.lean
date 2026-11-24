import YM.XSpace.Passage
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredAxes
open Filter Function Set
open scoped ContDiff Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrix (D:E×ℝ→E×ℝ) (smooth:ContDiff ℝ ω D)
    (left:HasFDerivAt (fun x:E=>D (x,0)) (ContinuousLinearMap.inl ℝ E ℝ) 0)
    (right:HasFDerivAt (fun t:ℝ=>D (0,t)) (ContinuousLinearMap.inr ℝ E ℝ) 0) :
    fderiv ℝ D 0=1 := by
  let K:=fderiv ℝ D 0
  have h:HasFDerivAt D K 0 := (smooth.differentiable (by simp) 0).hasFDerivAt
  let a:=ContinuousLinearMap.inl ℝ E ℝ
  let b:=ContinuousLinearMap.inr ℝ E ℝ
  have ka:K.comp a=a := (h.comp (0:E) a.hasFDerivAt).unique left
  have kb:K.comp b=b := (h.comp (0:ℝ) b.hasFDerivAt).unique right
  apply ContinuousLinearMap.ext
  intro z
  have l:K (z.1,0)=(z.1,0) := congrArg (fun T:E→L[ℝ](E×ℝ)=>T z.1) ka
  have r:K (0,z.2)=(0,z.2) := congrArg (fun T:ℝ→L[ℝ](E×ℝ)=>T z.2) kb
  change K z=z
  calc K z=K ((z.1,0)+(0,z.2)) := by simp
       _=K (z.1,0)+K (0,z.2) := map_add K _ _
       _=z := by rw [l,r];simp

theorem coercive (K:E→L[ℝ]E) (close:‖K-1‖<1/2) (v:E) : ‖v‖≤2*‖K v‖ := by
  have p:=((K-1).le_opNorm v).trans (mul_le_mul_of_nonneg_right close.le (norm_nonneg v))
  change ‖K v-v‖≤1/2*‖v‖ at p
  have triangle:=norm_sub_le (K v) (K v-v)
  rw [sub_sub_cancel] at triangle
  linarith

theorem quantitative [CompleteSpace E] (D:E→E) (s:ContDiff ℝ ω D) (b:E) (ground:fderiv ℝ D b=1) :
    ∀ᶠz in 𝓝 b, ∃A:E≃L[ℝ]E,A.toContinuousLinearMap=fderiv ℝ D z ∧ ‖A.symm.toContinuousLinearMap‖≤2 := by
  have t:Tendsto (fderiv ℝ D) (𝓝 b) (𝓝 1) := ground ▸ (s.continuous_fderiv (by simp)).continuousAt
  have units:=t.eventually (Units.isOpen.mem_nhds (show IsUnit (1:E→L[ℝ]E) from isUnit_one))
  have close:=t.eventually (Metric.ball_mem_nhds (1:E→L[ℝ]E) (by norm_num : (0:ℝ)<1/2))
  filter_upwards [units,close] with z traded near
  have bij:=ContinuousLinearMap.isUnit_iff_bijective.mp traded
  let A:=ContinuousLinearEquiv.ofBijective (fderiv ℝ D z) (LinearMap.ker_eq_bot.mpr bij.1) (LinearMap.range_eq_top.mpr bij.2)
  refine ⟨A,rfl,ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v=>?_)⟩
  have paid:=coercive (fderiv ℝ D z) (by simpa only [Metric.mem_ball,dist_eq_norm] using near) (A.symm v)
  change ‖A.symm v‖≤2*‖A (A.symm v)‖ at paid
  change ‖A.symm v‖≤2*‖v‖
  simpa only [A.apply_symm_apply] using paid
end YM.Integration.WilsonPositionScaleLawMeasuredAxes
