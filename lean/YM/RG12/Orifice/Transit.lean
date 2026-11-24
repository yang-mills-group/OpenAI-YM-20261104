import Mathlib.Analysis.Calculus.LHopital
import YM.RG12.Orifice.Links
/-! Pop by bounds rather than differentiating hard companions. The transmitted real
matin is already C² at 1 (according to Books), so may re-read second order at puncture. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Orifice.CashCond
open Filter Function Set MeasureTheory
open scoped Topology ContDiff BigOperators Classical
local notation "σ" => 𝓝[≠] (0:ℝ)
variable {f:ℝ→ℝ}{C:ℝ}
lemma juvenile (h:ContDiffAt ℝ 2 f 0)(hf:f 0=0)(hd:deriv f 0=0) : Tendsto (fun x:ℝ=>f x / x^2) σ (𝓝 ((iteratedDeriv 2 f 0)/2)):=by
  have hg : DifferentiableAt ℝ (deriv f) 0:= (ContDiffAt.derivWithin h (m:=1) (by exact le_rfl)).differentiableAt one_ne_zero
  have hx:=hg.hasDerivAt.tendsto_slope; unfold slope at hx; simp only [hd,sub_zero,smul_eq_mul] at hx
  rw [show iteratedDeriv 2 f=deriv (deriv f) by simp only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]]
  refine HasDerivAt.lhopital_zero_nhdsNE (Eventually.filter_mono nhdsWithin_le_nhds ?_ : ∀ᶠ x in σ,HasDerivAt f (deriv f x) x) (Eventually.of_forall fun x=> show HasDerivAt _ (2*x) x from by simpa using! (hasDerivAt_id' x).pow 2) ?_ ?_ ?_ ?_
  
  · exact (h.eventually (by norm_num)).mono fun i hi=> (hi.differentiableAt (by norm_num)).hasDerivAt
  · filter_upwards [self_mem_nhdsWithin] with i hi; exact mul_ne_zero (by norm_num) (show i≠0 from hi)
  · simpa only [hf] using h.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : σ ≤ 𝓝 (0:ℝ))
  · have he:Tendsto id σ (𝓝 0):= tendsto_id.mono_left nhdsWithin_le_nhds; simpa using he.pow 2
  · convert! (hx.div_const (2:ℝ)) using 1; ext x; simp [vsub_eq_sub,div_eq_mul_inv]; ring --field_simp; ring -- replace
lemma tenderApprox (h:ContDiffAt ℝ 2 f 0)(hf:f 0=0)(hd:deriv f 0=0) {c:ℝ}(ht:‖iteratedDeriv 2 f 0‖ ≤ C)(hc:0<c) : ∀ᶠ z in 𝓝 (0:ℝ), |f z| ≤ (C/2+c)*z^2:=by
  have hx:= (juvenile h hf hd).abs
  have hz : |iteratedDeriv 2 f 0/2| < C/2+c:=by rw [abs_div, abs_of_pos (show (0:ℝ)<2 by norm_num)]; rw [Real.norm_eq_abs] at ht; linarith
  have hh:=hx.eventually (ge_mem_nhds hz)
  rw [eventually_nhdsWithin_iff] at hh
  filter_upwards [hh] with x hx; rcases eq_or_ne x 0 with rfl|h; · rw [hf]; simp
  specialize hx h; rw [abs_div,abs_of_nonneg (sq_nonneg x)] at hx; exact (div_le_iff₀ (sq_pos_of_ne_zero h)).1 hx
lemma collect (h:ContDiffAt ℝ 2 f 0)(hf:f 0=0)(hd:deriv f 0=0) (he:∀ᶠ x in σ, |f x| ≤ C*x^2): ‖iteratedDeriv 2 f 0‖ ≤ 2*C := by
   have hh:= (juvenile h hf hd).abs
   have hk:∀ᶠ x in σ,x≠0:= self_mem_nhdsWithin
   have ht : _ ≤ C:= le_of_tendsto hh (by filter_upwards [he, hk] with x hx hk; rw [abs_div,abs_of_nonneg (sq_nonneg x)]; exact (div_le_iff₀ (sq_pos_of_ne_zero hk)).2 hx)
   rw [abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)] at ht; rw [Real.norm_eq_abs]; linarith
lemma smoothDividend (h:ContDiffAt ℝ (2:ℕ∞ω) f 0)(he:∀ᶠ x in 𝓝 (0:ℝ), |f x| ≤ C*x^2): ‖iteratedDeriv 2 f 0‖ ≤ 2*C:=by
  have hh: |f 0| ≤0:= by simpa using Eventually.self_of_nhds he
  have hf:f 0=0:= abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)); apply collect h hf _ (he.filter_mono nhdsWithin_le_nhds)
  apply HasDerivAt.deriv; apply hasDerivAt_iff_tendsto_slope.mpr
  unfold slope; rw [hf]; simp only [smul_eq_mul,vsub_eq_sub,sub_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let g(t:ℝ):= t⁻¹*f t
  change Tendsto (fun i=> ‖g i‖) σ (𝓝 0); have hi:Tendsto (fun x:ℝ=> C*|x|) σ (𝓝 0):=by simpa using! ((show Continuous (fun x:ℝ=> C*|x|) from continuous_const.mul continuous_abs).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds : σ ≤ 𝓝 (0:ℝ))
  refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ hi
  filter_upwards [show ∀ᶠ x in σ,x≠0 from self_mem_nhdsWithin,he.filter_mono (show σ ≤ 𝓝 0 from nhdsWithin_le_nhds)] with x hx he
  rw [Real.norm_eq_abs]; unfold g; rw [abs_mul,abs_inv]; refine (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (abs_nonneg _))).trans_eq ?_; have hh: |x| ≠ 0 := (abs_pos.mpr hx).ne'; rw [← sq_abs x,pow_two]; field_simp
end YM.RG12.Orifice.CashCond
