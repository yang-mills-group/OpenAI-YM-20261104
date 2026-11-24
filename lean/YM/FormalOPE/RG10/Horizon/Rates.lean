import YM.FormalOPE.RG10.Horizon.Twin
/-!
# Inventory arithmetic: power gain even with chosen smaller ζ

Supports for promoting into longer apertures while tracking a certificate constant. Use
as global ℝ formal ages, nonnegative durations in statements where explicit. The quantitative
repayments DO deteriorate with order r, all-order = every fixed r. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger
namespace Rates
variable {ξ μ v s t α β M:ℝ}{j p:ℕ}
lemma tilt_pos : 0<tilt s ξ:=Real.exp_pos _
lemma tilted : tilt s (α+β)= tilt s α*tilt s β:= by unfold tilt; rw [mul_add,Real.exp_add]
lemma duration : tilt (s+t) α=tilt s α*tilt t α:= by unfold tilt; rw [neg_add,add_mul,Real.exp_add]
lemma invariant : tilt s (-α)= (tilt s α)⁻¹:=by simp [tilt,Real.exp_neg]
lemma no_tilt : tilt s 0=1:=by simp [tilt]
lemma shade (he:α≤β)(hs:0 ≤ s) : tilt s β ≤ tilt s α:=Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left he (by linarith))
lemma cooling (he:s ≤ t)(hs:0 ≤ α) : tilt t α ≤ tilt s α:= Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hs)
lemma arrival (p:ℕ) (u:ℝ) (h:0<ξ) : Tendsto (fun s=> cash s u p ξ) atTop (𝓝 0):=by
 let k t:=(1+t)*ξ; have hk:Tendsto k atTop atTop:= (tendsto_atTop_add_const_left atTop 1 tendsto_id).atTop_mul_const h
 have hu(t:ℝ)(ht:0≤ t): cash t u p ξ= u*(ξ^p)⁻¹*Real.exp ξ*((k t)^p*Real.exp (-k t)):= by
   have hf : -t*ξ=ξ + -(k t):=by unfold k; ring
   rw [cash, tilt,hf,Real.exp_add, legUp,abs_of_nonneg ht]; unfold k; rw [mul_pow]; field_simp
 exact (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp hk).const_mul (u * (ξ^p)⁻¹ * Real.exp ξ) |>.mono_right (le_of_eq (by rw [mul_zero]))).congr' ((eventually_ge_atTop 0).mono fun t ht=> (hu t ht).symm)
lemma fade_out (h:0<ξ) : Tendsto (fun s => tilt s ξ) atTop (𝓝 0):=by simpa only [cash,legUp,pow_zero,mul_one,one_mul] using! arrival 0 1 h
lemma absorbed (h:α < ξ) : ∀ᶠ s:ℝ in atTop,cash s M p ξ ≤ tilt s α := by
 filter_upwards [(arrival p M (sub_pos.mpr h)).eventually (ge_mem_nhds (by exact (zero_lt_one' ℝ)))] with t ht
 have he : cash t M p ξ=cash t M p (ξ-α)*tilt t α:=by rw [cash,cash,mul_assoc,← tilted, sub_add_cancel]
 rw [he]; exact mul_le_of_le_one_left tilt_pos.le ht

-- turn point budgets into series-magnitudes on any fixed coefficient demand
lemma earn {f : ℝ → fps}{r : ℕ} (h : ∀ j≤r, Polys (fun s=> tilt s (-α) * coeff j (f s))) : Polys (fun s=> tilt s (-α)*coin r (f s)) := by
 have hv i : (fun s=> tilt s (-α)*‖coeff i (f s)‖)=(fun s=> ‖tilt s (-α)*coeff i (f s)‖):=by ext s; rw [norm_mul,Real.norm_of_nonneg tilt_pos.le]
 simp_rw [cstate,Finset.mul_sum];
 apply Polys.sum; intro i hi; rw [hv];
 obtain ⟨d,C,hc,hx⟩:= h i (by simpa using hi); exact ⟨d,C,hc,fun x=> by simpa using! hx x⟩

lemma discount {x: ℝ→fps} {r : ℕ}(h:∀ i≤r, Polys (fun s=> tilt s (-α)*coeff i (x s)))(he: ξ<α): ∀ᶠ s:ℝ in atTop, coin r (x s) ≤ tilt s ξ:= by
 obtain ⟨d,C,hc,hK⟩:=earn h
 filter_upwards [absorbed (p:=d) he (M:=C)] with s ht
 apply le_trans ?_ ht; unfold cash legUp
 rw [mul_comm (C * _)]; apply (mul_le_mul_of_nonneg_left (hK s) tilt_pos.le).trans'; rw [Real.norm_of_nonneg (mul_nonneg tilt_pos.le (coined _)),← mul_assoc, ← tilted,add_neg_cancel,no_tilt,one_mul];

end Rates
end YM.FormalOPE.RG10.Clearing
