import YM.RGComparison.Core16.Forge.Splint
/-! # Deployed witness inputs for volume-uniform top seam estimate

All admitted parameters before p. Can post-delay for any stipulated growth over the required
powers, later payments only prove it at a specified invoice. `skin` report concerns actual
normalized posterior on tree links, with global V constraint. Full chart, operators may reuse
for Taylor by Hölder or test-poly. Never change kinematic calibration to call this.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge.Hut
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Pressure
open Precision Push.BetaTransport Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {c f : Side}{S:StepData c f} (T:Forest S.ratio){g Q:ℝ} (hS:Bid.Larger (G:=G) S)
    {V:Config G c}(hg:0≤g)(hQ:0<Q)(hv:∀ i,G.chord (V i)≤Q*g)
local notation "B"=> seam S T V

def survey (G:Gauge) (P:Patch)(K:KernelChoices)(Q:ℝ): Prices := ⟨width P, quota, max (lowClip G P K Q) (upstairs P K Q),floor_pos,(up_pos P K Q).trans_le (le_max_right ..)⟩
include hS hg hQ hv

lemma grants : (B).Admits (survey G S.patch S.kernel Q) g:=by
    refine ⟨fun _ _=> S.likelihood_pos ..,fun _=> S.chosen hS.1 _,fun t=>?_, fun x t j=>cooks S T V ..,?_,pad_price S T,root_price S,?_,?_, local_tags hS.1 T V⟩
    · exact (S.likelihood_meas hS.1 t).comp T.continuous_drape.measurable
    · intro t j; cases j with
      | inl j => exact (show Continuous (fun x:T.Free→G.El=> G.price (faceValue (T.drape x) j)) from G.continuous_price.comp ((show Continuous (fun U:Config G f=>faceValue U j) by unfold faceValue; fun_prop).comp T.continuous_drape)).measurable
      | inr j => exact (link_estimate S).measurable.comp (measurable_const.mul ((measurable_pi_apply j).comp ((S.prediction_meas hS.1 t).comp T.continuous_drape.measurable)).inv)
    · intro x t i he
      exact (lower T t hS hg hQ hv x i he).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (add_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => cooks ..)))
    intro x t i _
    exact (upper T t hS hg hQ hv x i).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (add_nonneg (sq_nonneg _) (threat_nonneg ..)))
omit hS hg hQ hv

-- Keep EXACT S.penaltyZ, denominator only cancels in ratios. All fields formula.
variable (V g)
lemma bill (x:Sky G T.Free): S.density (g^2)⁻¹ (T.drape x) V * bare (g^2)⁻¹ (T.drape x) = Next.Fluctuations.Sector.prefactor S G (g^2)⁻¹ * (B).output g x:=by
    unfold StepData.density Base.output
    rw [sum_mul,mul_sum]; apply sum_congr rfl; intro i _
    rw [noise_factor,Base.cash, action_eq]
    unfold bare Gibbs.factor; unfold tagEnergy; dsimp only [seam]
    rw [neg_add,add_div, Real.exp_add]; simp only [div_eq_mul_inv,neg_mul, mul_comm ((g^2)⁻¹)]
    ring

lemma skin (G:Gauge)(P:Patch)(K:KernelChoices)(hQ:0<Q) : ∀ᶠ s:ℝ in atTop, ∀ (c f:Side) (S:StepData c f), S.patch=P→ S.kernel=K→Bid.Larger (G:=G) S→ ∀ (T:Forest S.ratio) (V:Config G c), (∀ i,G.chord (V i)≤Q*dollar s)→∀ i:T.Free,
     let W := fun x:Sky G T.Free=> S.density ((dollar s)^2)⁻¹ (T.drape x) V * bare ((dollar s)^2)⁻¹ (T.drape x)
     (∫ x in breach i s, W x∂T.order G) ≤ ruin s * ∫ x, W x ∂T.order G := by
    filter_upwards [shield (survey G P K Q) G] with x hx c f S hP hK h T V hv i
    intro W
    subst P; subst K
    let g:=dollar x
    let Z:=Next.Fluctuations.Sector.prefactor S G (g^2)⁻¹
    have hz:=show 0 < Z from pow_pos (inv_pos.mpr (S.penaltyZ_pos ..)) _
    have hu:= grants T h (dollar_pos x|>.le) hQ hv
    rw [show W=fun y=> Z * (seam S T V).output g y from funext (bill T (dollar x) V), integral_const_mul, integral_const_mul,mul_left_comm (ruin x)]
    refine mul_le_mul_of_nonneg_left ?_ hz.le; exact hx _ _ _ _ _ _ _ _ hu i
end YM.RGComparison.Core16.Forge.Hut
