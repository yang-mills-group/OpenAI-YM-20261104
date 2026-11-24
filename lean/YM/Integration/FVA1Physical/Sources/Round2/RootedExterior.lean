import YM.Integration.FVA1Physical.Sources.Round2.PhysicalFieldKernel
import YM.Integration.FVA1Physical.Wilson.CylinderOscillation
import YM.MSbar.Bakery.Glance

/-! A change at arbitrarily many distant retained links is priced by the full
anchored derivative row. The bound uses the sup norm of the change and the
original spatial weight, with no factor for the size of the torus. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Set Filter MeasureTheory Lattice RG YM.Wilson Precision Tree Exterior
open MSbar MSbar.Bakery MSbar.Cacao MSbar.Whisk MSbar.Measuring MSbar.Rolling MSbar.Bulk MSbar.Midpoint
open MSbar.Heath.Cottage MSbar.Mosaic MSbar.Bakery.Film RGComparison.Core16 RGComparison.Core16.Spool
open Push.Uniform YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators ContDiff
variable {σ : Type} [Fintype σ] {n : Side}

theorem rooted_differential (loc : σ → Site n) (b : Site n) (s R : ℕ) {a B : ℝ} (ha : 0 ≤ a)
    (f : Pot σ) (x v : View σ) (far : ∀ i, v i ≠ 0 → R ≤ separation b (loc i))
    (fund : Vault loc {b} a s 1 x f B) :
    ‖fderiv ℝ (fun z => MvPolynomial.eval z f) x v‖ ≤ ‖v‖*B/liftW a s R := by
  let D:=fderiv ℝ (fun z => MvPolynomial.eval z f) x
  let w:=liftW a s R
  let ξ:=fun i=>rate loc {b} a s x f [i]
  have row : (∑ i,ξ i) ≤ B := fund.2 1 le_rfl
  have entry (i) : D (bolt i)=read x [i] f := by
    simpa only [glance,YM.Analysis.D,bolt,D] using (glance_jet (x:=x) f [i])
  have bound (i) : ‖v i • D (bolt i)‖*w ≤ ‖v‖*ξ i := by
    by_cases h : v i=0
    · rw [h,zero_smul,norm_zero,zero_mul]
      exact mul_nonneg (norm_nonneg v) (liquid loc {b} x)
    have radius : w ≤ spread loc {b} a s [i] :=
      (w_more (far i h) ha s).trans (radius_go loc (List.mem_singleton.mpr rfl) (mem_singleton_self b) ha s)
    rw [norm_smul,entry,Real.norm_eq_abs,mul_right_comm]
    change ‖v i‖*w*|read x [i] f| ≤ ‖v‖*(spread loc {b} a s [i]*|read x [i] f|)
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (norm_le_pi_norm v i) radius (wpos a s R).le (norm_nonneg v)) (abs_nonneg _)
  apply (le_div_iff₀ (wpos a s R)).mpr
  change ‖D v‖*w ≤ ‖v‖*B
  have norm : ‖D v‖ ≤ ∑ i,‖v i • D (bolt i)‖ := by
    nth_rw 1 [Lis.spiral v]
    rw [map_sum]
    simp only [map_smul]
    exact norm_sum_le ..
  calc ‖D v‖*w ≤ (∑ i,‖v i • D (bolt i)‖)*w := mul_le_mul_of_nonneg_right norm (wpos ..).le
       _ = ∑ i,‖v i • D (bolt i)‖*w := Finset.sum_mul ..
       _ ≤ ∑ i,‖v‖*ξ i := Finset.sum_le_sum fun i _=>bound i
       _ = ‖v‖*∑ i,ξ i := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left row (norm_nonneg _)

theorem rooted_exterior_motion (loc : σ → Site n) (b : Site n) (s R : ℕ) {a B : ℝ} (ha : 0 ≤ a)
    (f : Pot σ) (x v : View σ) (far : ∀ i, v i ≠ 0 → R ≤ separation b (loc i))
    (fund : ∀ t ∈ Set.Icc (0:ℝ) 1, Vault loc {b} a s 1 (x+t • v) f B) :
    |MvPolynomial.eval (x+v) f-MvPolynomial.eval x f| ≤ ‖v‖*B/liftW a s R := by
  let D:=fun t:ℝ=>fderiv ℝ (fun z=>MvPolynomial.eval z f) (x+t • v) v
  have along (t : ℝ) : HasDerivAt (fun t:ℝ=>MvPolynomial.eval (x+t • v) f) (D t) t := by
    apply ((vent f).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
    simpa using ((hasDerivAt_id' t).smul_const v).const_add x
  have q := norm_image_sub_le_of_norm_deriv_le_segment_01' (f:=fun t:ℝ=>MvPolynomial.eval (x+t • v) f) (f':=D)
    (fun t _=>(along t).hasDerivWithinAt)
    (fun t ht=>rooted_differential loc b s R ha f _ v far (fund t (Set.Ico_subset_Icc_self ht)))
  simpa only [one_smul,zero_smul,add_zero,Real.norm_eq_abs] using q

end YM.Integration.FVA1Physical.Round2.Curvature
