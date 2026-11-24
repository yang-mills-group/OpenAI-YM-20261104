import YM.MSbar.RawP.Bust
import YM.MSbar.DeltaM.Town
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
open Set Metric
structure Hat (k:ℕ)(c d:ℝ) (f:ℝ→ℝ): Prop where
    value : ∀ x, |f x| ≤ |x| ∧ |f x|≤ c
    honest : ∀ x, |x|< c/2→f x=x
    smooth : ContDiff ℝ (k:ℕ) f
    head (x:ℝ)(i:ℕ) : i ≤k→ ‖iteratedFDeriv ℝ i f x‖ ≤ d
noncomputable def plug : ContDiffBump (0:ℝ) := ⟨2⁻¹,1,by norm_num,by norm_num⟩
noncomputable def sea :ℝ→ℝ:= fun x=> plug x * x
lemma top_hat (k:ℕ) : ∃ c:ℝ,1≤c∧Hat k 1 c sea:=by
     let f:=sea; have hv : ContDiff ℝ k f:= (plug.contDiff).mul contDiff_id; have hz(x:ℝ):|sea x|≤ |x| :=by unfold sea; rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg x) (by rw [abs_of_nonneg plug.nonneg]; exact plug.le_one); -- end
     have he : HasCompactSupport sea:= plug.hasCompactSupport.mul_right
     choose c hc using fun i:Fin (k+1)=> (hv.continuous_iteratedFDeriv (Nat.cast_le (α:=ℕ∞ω)|>.mpr (Nat.lt_succ_iff.mp i.is_lt))).norm.bddAbove_range_of_hasCompactSupport ((he.iteratedFDeriv (𝕜:=ℝ) i).norm)
     let C:= 1+ ∑ j:Fin (k+1),|c j|; have hC : (1:ℝ)≤C:= le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=> abs_nonneg _)
     refine ⟨C,hC,⟨fun x=>⟨hz x,?_⟩,fun x hx=>?_,hv,fun x i hi=>?_⟩⟩
     · by_cases hg:|x|<1; exact hz x|>.trans hg.le; unfold sea; rw [show plug x=0 from ?_];simp
       by_contra! hx; have hv:(x∈Function.support plug):=hx; rw [plug.support_eq] at hv; apply hg; simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,plug] using hv
     · unfold sea; rw [plug.one_of_mem_closedBall, one_mul]; simpa [plug] using hx.le -- simp type abs
     let j:Fin (k+1):=⟨i,(Nat.lt_succ_iff.mpr hi)⟩; have hx: ‖iteratedFDeriv ℝ i sea x‖ ≤ c j:= hc j ⟨x,rfl⟩
     exact hx.trans ((le_abs_self _).trans ((Finset.single_le_sum (f:=fun j:Fin (k+1)=> |c j|) (fun j _=>abs_nonneg _) (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)))
variable {c d B K w θ:ℝ}{q k:ℕ}{f:ℝ→ℝ}(h:Hat k 1 d f)(hw:1≤w)
noncomputable def masking (w:ℝ)(f:ℝ→ℝ)(x:ℝ):= w*f (w⁻¹*x)
local notation "V"=>masking w f
include h hw
lemma cool : Hat k w (w*d) (masking w f) :=by
   have hv:0<w:=zero_lt_one.trans_le hw; let L:=w⁻¹ • ContinuousLinearMap.id ℝ ℝ; have hL:‖L‖ ≤1:=by unfold L; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le)]; exact (mul_le_of_le_one_right (inv_nonneg.mpr hv.le) ContinuousLinearMap.norm_id_le).trans (inv_le_one_of_one_le₀ hw)
   refine ⟨fun x=>?_,fun x hz=>?_,(h.smooth.comp L.contDiff).const_smul w,fun x i hi=>?_⟩
   · unfold masking; rw [abs_mul,abs_of_pos hv]; have hz:=h.value (w⁻¹*x); exact ⟨(mul_le_mul_of_nonneg_left hz.1 hv.le).trans_eq (by rw [abs_mul,abs_of_pos (inv_pos.mpr hv), mul_inv_cancel_left₀ hv.ne']), (mul_le_of_le_one_right hv.le hz.2)⟩
   · unfold masking; rw [h.honest (w⁻¹*x) ?_, mul_inv_cancel_left₀ hv.ne']; rw [abs_mul,abs_of_pos (inv_pos.mpr hv), mul_comm,←div_eq_mul_inv]; rw [div_lt_iff₀ hv]; linarith only [hz]
   have hc:ContDiffAt ℝ (↑i) f (L x):=h.smooth.contDiffAt.of_le (Nat.cast_le.mpr hi); change ‖iteratedFDeriv ℝ i (w • (f ∘ L)) x‖ ≤ _; rw [iteratedFDeriv_const_smul_apply (hc.comp _ L.contDiff.contDiffAt),norm_smul,Real.norm_of_nonneg hv.le, iter_lin_at hc]; apply mul_le_mul_of_nonneg_left _ hv.le
   apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (h.head (L x) i hi); rw [prod_const,card_univ,Fintype.card_fin]; exact pow_le_one₀ (norm_nonneg _) hL
end YM.MSbar.Lodge
