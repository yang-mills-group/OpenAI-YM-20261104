import YM.Integration.WilsonEmittedRootRecovery
import YM.Integration.WilsonEmittedLocatedCensus

/-! Pin the original running coupling only after the joint Taylor
cancellation. Only the bounded number of retained angular coefficients
pay for undoing a dilation. The moving regularity order remains available. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedCouplingSlice
open Function Comparison.RG02 Comparison.Density AnalyticBridge.SectorAffine.Offset
open scoped ContDiff Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fixed {m : ℕ} {C t : ℝ} {x : E} {f : ℝ × E → F}
    (h : Through m f (t,x) C) : Through m (fun y => f (t,y)) x C := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one fun a => by simp [L,Prod.norm_def]
  let F₁ := fun z : ℝ × E => f ((t,0)+z)
  have smooth : ContDiffAt ℝ m F₁ (L x) := by
    apply ContDiffAt.comp (g:=f) (f:=fun z : ℝ × E => (t,0)+z)
    · simpa [L] using h.smooth
    · exact contDiffAt_const.add contDiffAt_id
  have H : Through m F₁ (L x) C := ⟨smooth, fun i hi => by
    rw [show iteratedFDeriv ℝ i F₁ (L x)=iteratedFDeriv ℝ i f ((t,0)+L x) from
      iteratedFDeriv_comp_add_left (𝕜:=ℝ) (f:=f) i (t,0) (L x)]
    simpa [L] using h.pay i hi⟩
  simpa [F₁,Function.comp_def,L] using Transport.through_pull L hL H

theorem low (f h : ℝ × E → F) {J m r : ℕ} {g D : ℝ}
    (hf : ContDiffAt ℝ ω f 0) (hh : ContDiffAt ℝ ω h 0)
    (read : ∀ i < J, ∀ A : E, Assembly.jet f i (1,A) = Assembly.jet h i (1,A))
    (hD : 0 ≤ D) (hg : 0 < g) (hg' : g ≤ 1) (hJ : J ≤ m) (hr : r ≤ J)
    (fund : ∀ z : ℝ × E, ‖z‖ ≤ g → Through m (f-h) z D) :
    ∀ i < r, ‖iteratedFDeriv ℝ i (fun y : E => (f-h) (g,y)) 0‖ ≤ D*g^(J-r) := by
  let sliced := fun y : E => (f-h) (g,y)
  let scaled := fun y : E => sliced (g • y)
  have cut := WilsonEmittedRootRecovery.tested f h hf hh read hD hg.le hg' hJ
    fund ((1:ℝ), (0:E)) (by simp [Prod.norm_def])
  have hold : Through m scaled 0 (D*g^J) := by
    simpa [scaled,sliced,Function.comp_def,Prod.smul_mk,smul_eq_mul] using fixed cut
  have undo : sliced = scaled ∘ Transport.dilation E g⁻¹ := by
    funext y
    simp [scaled,Transport.dilation_eval,smul_smul,hg.ne']
  intro i hi
  have him : i ≤ m := hi.le.trans (hr.trans hJ)
  change ‖iteratedFDeriv ℝ i sliced 0‖ ≤ _
  rw [undo]
  have hh' : ContDiffAt ℝ i scaled (g⁻¹ • (0:E)) := by
    simpa using (Transport.through_le hold him).smooth
  have pay : ‖iteratedFDeriv ℝ i scaled (g⁻¹ • (0:E))‖ ≤ D*g^J := by
    simpa using hold.pay i him
  apply (Transport.dil_cost (inv_nonneg.mpr hg.le) scaled 0 hh' pay).trans
  have ee : J = (J-i)+i := by omega
  rw [pow_add_apply g ee,inv_pow, mul_assoc, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hg.ne'),mul_one]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg.le hg' (by omega)) hD
where
  pow_add_apply (g : ℝ) {J k i : ℕ} (h : J=k+i) : g^J = g^k*g^i := h ▸ pow_add g k i

end YM.Integration.WilsonEmittedCouplingSlice
