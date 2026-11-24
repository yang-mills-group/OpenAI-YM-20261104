import YM.Pert.First.Transfer
/-! First interaction order: only the scaled action cubic. Vanishing of Haar/FP linear terms uses constant conjugation and no invariant linear color directions. Does not omit determinants at higher orders. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.Pert.First
open Orb Lattice Filter Matrix Function Topology
open scoped Topology ContDiff
variable {G : Gauge} {N : Side}
lemma detParam (u : G.El) : LinearMap.det (paramCol (N:=N) u) ≠ 0 := by
  have he := param_cancel (N:=N) u
  have hi : paramCol (N:=N) u⁻¹ ∘ₗ paramCol u = 1 := LinearMap.ext he
  intro h
  apply one_ne_zero (α:=ℝ)
  rw [← map_one (LinearMap.det (M:=Parameter G N) (A:=ℝ)),←hi,LinearMap.det_comp,h,mul_zero]
lemma fp_matrix_det (a : Potential G N) : FP a=LinearMap.det (resetFP a).toLinearMap := by
  let B := Module.finBasis ℝ (Parameter G N)
  rw [FP, ←LinearMap.det_toMatrix B]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]; rfl
lemma fp_invariant (u : G.El) : (fun a : Potential G N=> FP (linkCol u a)) =ᶠ[𝓝 0] FP := by
  filter_upwards [reset_colored (N:=N) u] with a ha
  have he : (resetFP (linkCol u a)).toLinearMap ∘ₗ paramCol u = paramCol u ∘ₗ (resetFP a).toLinearMap := congrArg ContinuousLinearMap.toLinearMap ha
  apply mul_right_cancel₀ (detParam (N:=N) u)
  rw [fp_matrix_det,fp_matrix_det, ←LinearMap.det_comp, he,LinearMap.det_comp,mul_comm]
lemma invariant_null (hg : G.Simple) (f : Potential G N→ₗ[ℝ] ℝ) (h : ∀ u a, f ((linkCol u) a)=f a) : f=0 := by
  let g := f ∘ₗ balance G N
  have he (i : Edge (Site N)) : g ∘ₗ LinearMap.single ℝ (fun _=>G.Color) i= (0:G.Color→ₗ[ℝ] ℝ) := by
    apply UVNext.FreeStress.no_linear hg
    intro u l; simp only [LinearMap.comp_apply, LinearMap.single_apply]; unfold g; simp only [LinearMap.comp_apply]
    nth_rw 2 [← h u (balance G N _)]; rw [←color_bal]; apply congrArg _ (congrArg _ ?_)
    ext1 j; by_cases hj : j=i
    · subst j; simp
    simp [Pi.single_eq_of_ne hj]
  apply LinearMap.ext; intro a; conv_lhs => rw [←balance_same a]
  let A := a.val
  have hw : ∑ i,Pi.single i (A i)=A := by ext1 i; simp
  change g A = (0:ℝ)
  rw [← hw,map_sum]; exact Finset.sum_eq_zero (fun i _ => LinearMap.congr_fun (he i) (A i))
lemma derivative_null (hg : G.Simple) (f : Potential G N→ℝ) (hf : ContDiffAt ℝ ω f 0) (h : ∀ u, f ∘ (linkCol u) =ᶠ[𝓝 0] f) : fderiv ℝ f 0=0 := by
  suffices (fderiv ℝ f 0).toLinearMap = 0 by exact ContinuousLinearMap.ext (LinearMap.congr_fun this)
  apply invariant_null hg; intro u a
  let L := LinearMap.toContinuousLinearMap (linkCol (N:=N) u)
  have he : f ∘ L =ᶠ[𝓝 0] f := h u
  have hs : HasFDerivAt f (fderiv ℝ f 0) (L 0) := by simpa using (hf.differentiableAt (by simp)).hasFDerivAt
  exact congrArg (fun h : Potential G N →L[ℝ] ℝ=> h a) ((hs.comp (0: Potential G N) L.hasFDerivAt).fderiv.symm.trans (he.fderiv_eq))

local notation "coef" => PowerSeries.coeff (R:=ℂ)
lemma no_unmark_one (hg : G.Simple) (x : Coords G N) : coef 1 (unmarked G N x)=0 := by
  simp only [unmarked,PowerSeries.coeff_mk,scaleJet,iteratedFDeriv_one_apply, derivative_null hg (fun a=> Orb.Jacob a * FP a) (Orb.jacobian_smooth.mul FP_diff) (fun u=> (fp_invariant u).mono fun a ha => congrArg₂ (·*·) (jacobian_invariant u a) ha), ContinuousLinearMap.zero_apply,smul_zero,Complex.ofReal_zero]
lemma unmarked_zero (x : Coords G N) : PowerSeries.constantCoeff (unmarked G N x)=1 := by rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [unmarked,scaleJet_zero]
lemma exp_one {p : JetArray (Coords G N)} (x : Coords G N) : coef 1 (expR p x) = coef 1 (p x) := by
  simp only [expR, PowerSeries.coeff_mk, Finset.sum_range_succ,Finset.sum_range_zero,pow_zero, pow_one,PowerSeries.coeff_one]; simp
def cubic (x : Coords G N) : ℂ := - ↑(scaleJet (action G N) 3 x)
lemma has_first (hg : G.Simple) (x : Coords G N) : coef 1 (weight G N x) = cubic x := by
  simp only [weight,Pi.mul_apply,PowerSeries.coeff_one_mul,unmarked_zero,exp_one,no_unmark_one hg,zero_mul,mul_one,add_zero,actionR,cubic,PowerSeries.coeff_mk,show (1:ℕ)≠0 from by decide,if_false,Complex.ofReal_neg]
lemma vacuum_one : coef 1 (vacuum G N)=0 := by
  have he := congrArg (coef 1) (Parity.vacuum_reflect (G:=G) (n:=N))
  rw [PowerSeries.coeff_rescale] at he; linear_combination -(1/2:ℂ) * he

lemma vacuum_inv_one : coef 1 (vacuum G N)⁻¹=0  := by
  have he := congrArg (coef 1) (Parity.inv_vac (G:=G) (n:=N)); rw [PowerSeries.coeff_rescale] at he; linear_combination -(1/2:ℂ) * he
end YM.Pert.First
