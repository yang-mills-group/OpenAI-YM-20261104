import YM.PhysMS.Foundation.Estimates

/-! # Relative-length iteration for frames

Compact step bounds, with constant loss at the strict homogeneity exponent *independent* of
step size, pay arbitrary small exponential losses in negative log length. Needn't assume regular
frames in the continuous RG time, or convenient spacing of a comparison path. Keep the ability
to estimate all the way from one UV length to another *arbitrary* one. Initial price on a compact
annulus likewise follows from comparing within a compact ratio range in the UV (with *eventual*
threshold in r depending on the least ratio).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Filter Set Trace.Pilot OPE
open scoped Topology BigOperators Classical

/-- `K` independent of least ratio. ζ is weight (thus larger means strictly smaller). P may
    be a seminorm (doesn't require P r positive). Quantitative estimate retains ratio gain, so
    initial cost for integration can be taken anywhere in UV. -/
theorem shell_iteration (K ζ ε : ℝ) (hK : 1 ≤ K) (he : 0 < ε)
    (P : ℝ → ℝ) (hP : ∀ r : ℝ, 0 ≤ P r)
    (h : ∀ c : ℝ, 0 < c → c < 1 → ∀ᶠ r in trail, ∀ a∈Icc c 1,
          P (a*r) ≤ K*a^ζ*P r) :
    ∀ᶠ r in trail, ∀ a : ℝ, a∈Ioc 0 1 → P (a*r) ≤ K*a^(ζ-ε)*P r := by
  -- Choose a step small enough to already absorb K in the exponent.
  obtain ⟨c,hc0,hc,hε⟩ := ((show ∀ᶠ c : ℝ in trail, 0 < c from self_mem_nhdsWithin).and
    (((gt_mem_nhds (show (0:ℝ)<1 from by norm_num)).filter_mono (@nhdsWithin_le_nhds ℝ _ (0:ℝ) (Ioi (0:ℝ)))) |>.and
    ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr he)).eventually_ge_atTop K))).exists
  change c<1 at hc
  change K ≤ c^(-ε) at hε
  obtain ⟨s,hs,hρ⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp (h c hc0 hc)
  have hsmall : ∀ᶠ r in trail, r∈ Ioc 0 s:= mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨s,hs,subset_refl _⟩
  filter_upwards [hsmall] with r hr a ha
  have hR : 0 < r:= hr.1
  have haken : K*c^ζ ≤ c^(ζ-ε):=by
     rw [sub_eq_add_neg,Real.rpow_add hc0,mul_comm]; exact mul_le_mul_of_nonneg_left hε (Real.rpow_nonneg hc0.le _)
  have hincl (b : ℝ) (hb : b∈Ioc (0:ℝ) 1) : b*r∈Ioc 0 s:=
    ⟨mul_pos hb.1 hr.1,le_trans (mul_le_of_le_one_left hr.1.le hb.2) hr.2⟩
  -- for every a >= c^m. recurse until scale back to r, use same m cost if needed
  have go(m : ℕ) (b : ℝ) (hb : b∈Ioc 0 1) (hstep : c^m ≤ b) :
      P (b*r) ≤ K*b^(ζ-ε)*P r := by
    induction m generalizing b with
    | zero =>
      rw [pow_zero] at hstep; obtain rfl : b = (1:ℝ) := le_antisymm hb.2 hstep
      simpa using (le_mul_of_one_le_left (hP r) hK)
    | succ m ih =>
      have h0 : 0 < b:= hb.1
      by_cases hp : c ≤ b
      · calc _ ≤ K*b^ζ*P r:= hρ hr b ⟨hp,hb.2⟩
             _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                      (Real.rpow_le_rpow_of_exponent_ge h0 hb.2 (by linarith only [he])) (zero_le_one.trans hK)) (hP r)
      have hu : b / c∈ Ioc 0 1 := ⟨div_pos h0 hc0,(div_le_one hc0).mpr (not_le.mp hp).le⟩
      specialize ih (b / c) hu (by rw [le_div_iff₀ hc0]; exact hstep)
      calc
        _ = P (c*((b/c)*r)) := by congr 1; field_simp
        _ ≤ K*c^ζ * P (b/c * r) := hρ (hincl (b/c) hu) c ⟨le_rfl,hc.le⟩
        _ ≤ c^(ζ-ε) * (K*(b/c)^(ζ-ε)*P r) := mul_le_mul haken ih (hP _) (Real.rpow_nonneg hc0.le _)
        _ = _:=by
          have hx : c^(ζ-ε) * (b/c)^(ζ-ε) = b^(ζ-ε):=by rw [← Real.mul_rpow hc0.le hu.1.le, mul_div_cancel₀ _ hc0.ne']
          linear_combination K*P r*hx
  obtain ⟨m,hm⟩:= exists_pow_lt_of_lt_one ha.1 hc
  exact go m a ha hm.le

lemma compact_event (U : Type*) {Y : Type*} [TopologicalSpace Y] {l : Filter U} {V : Set Y}
    (h : IsCompact V) (P : U → Y → Prop) (hp : ∀ y∈V,∀ᶠ z : U × Y in l ×ˢ 𝓝 y, P z.1 z.2) :
    ∀ᶠ i : U in l, ∀ y ∈ V, P i y := by
  have hx : ∀ᶠ z : U × Y in l ×ˢ 𝓝ˢ V, P z.1 z.2 := h.mem_prod_nhdsSet_of_forall hp
  exact hx.curry.mono fun _ hy=> hy.self_of_nhdsSet

-- Exponential ledger version. OK without frame continuity/measurability.
lemma shell_rate {Y : Type*} [SeminormedAddCommGroup Y] (P : ℝ → Y) {K ζ : ℝ} (hK : 1 ≤ K)
    (h : ∀ c : ℝ, 0 < c → c < 1 → ∀ᶠ r in trail, ∀ a∈Icc c 1,
          ‖P (a*r)‖ ≤ K*a^ζ*‖P r‖) : RateLE trail LogV P (-ζ) := by
  intro e he; obtain ⟨u,hu,hU⟩:= exists_between he
  obtain ⟨s,⟨hx,hw⟩⟩:= ((show ∀ᶠ s : ℝ in trail, 0 < s from self_mem_nhdsWithin).and
    (shell_iteration K ζ (u + ζ) hK (by linarith only [hu]) (fun r=> ‖P r‖) (fun _=> norm_nonneg _) h)).exists
  let A := K / s^(-u) * ‖P s‖
  have hz := RateLE.const A to_log_zoom |>.mul ((length_rate.rpow (-u)).pays to_log_zoom)
  rw [zero_add, neg_mul_neg, mul_one] at hz
  filter_upwards [hz e hU,(gt_mem_nhds hx).filter_mono
    (@nhdsWithin_le_nhds ℝ _ (0:ℝ) (Ioi (0:ℝ))),self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with r hr hs hp
  replace hp : 0 < r:= hp
  replace hs : r<s:= hs
  specialize hw (r/s) ⟨div_pos hp hx,(div_le_one hx).mpr hs.le⟩
  rw [div_mul_cancel₀ _ hx.ne', Real.div_rpow hp.le hx.le, show ζ-(u+ζ)=-u by ring] at hw
  calc
    ‖P r‖ ≤ A*r^(-u) := hw.trans (le_of_eq (by unfold A; ring))
    _ ≤ Real.exp (e*LogV r):= (Real.le_norm_self _).trans hr
end YM.PhysMS.Frame
