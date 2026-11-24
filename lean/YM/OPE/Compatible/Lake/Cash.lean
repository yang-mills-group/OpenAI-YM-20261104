import YM.OPE.Compatible.Maestro.Lanes
/-!
# Second-order costs

Currency here is log of hatted inverse square; powers consumed are those of actual logs, not of length. Every k on the clock; gaps paid with their exact log. This file and descendants neither precede E Final nor feed the foundational nesting. Don't export the conditional procurement below as a result on the choices unless its inputs are met.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}{T:Final C Λ S}
variable (C)
abbrev hill (m:ℕ):ℝ:= Real.log (β C m)
def levy (m:ℕ):ℝ := hill C (m+1)-hill C m
abbrev freight (n i:ℕ):ℝ:= extent C i^n
lemma hill_pos (m):0 < hill C m:= Real.log_pos (β_one C m)
variable {C} (h:G.Simple)
include h
lemma hill_high : Tendsto (hill C) atTop atTop:= Real.tendsto_log_atTop.comp (β_ascent h)
lemma levy_pos (m):0 < levy C m := sub_pos.mpr (Real.log_lt_log (β_pos C m) ((β_increases h) (lt_add_one m)))
omit h in
lemma mount_rate : Tendsto (fun i => β C i/C.S.scale i) atTop (𝓝 G.slopeConstant):=by
    let W:= C.path.levels.clock.bar
    have hp : Tendsto (fun i:ℕ=> W/C.S.scale i) atTop (𝓝 0):= tendsto_const_nhds.div_atTop C.S.divergent
    have hx:=hp.add_const G.slopeConstant; rw [zero_add] at hx; apply hx.congr'; filter_upwards [C.S.divergent.eventually_gt_atTop 0] with i hi
    change _=(W+G.slopeConstant*C.S.scale i)/_; rw [add_div,mul_div_cancel_right₀ _ hi.ne']
-- shifted.
lemma next_rate : Tendsto (fun i => β C (i+1)/β C i) atTop (𝓝 1):=by
    let L:= C.S; have hs : L.Gentle:= C.path.levels.fits.mesh
    have ht := (mount_rate (C:=C)); have hV:= ((ht.comp (tendsto_add_atTop_nat 1)).mul ((show Tendsto (fun i:ℕ=>L.scale (i+1)/L.scale i) atTop (𝓝 1) from ?_))).div ht (G.slopeConstant_pos h).ne'
    · rw [mul_one,div_self (G.slopeConstant_pos h).ne'] at hV; apply hV.congr'; filter_upwards [L.divergent.eventually_gt_atTop 0, (tendsto_add_atTop_nat 1).eventually (L.divergent.eventually_gt_atTop 0)] with i hi hy
      change β C (i+1)/L.scale (i+1) * (L.scale (i+1)/L.scale i) / (β C i/L.scale i)=_ ; change 0 < L.scale (i+1) at hy; have := β_pos C i; field_simp
    have hx: Tendsto (fun i=> 1+Real.log (extent C i)/L.scale i) atTop (𝓝 1):=by simpa only [add_zero] using! (hs.const_add 1)
    refine hx.congr' ((L.divergent.eventually_gt_atTop 0).mono ?_); intro i hi
    dsimp only; rw [L.scale_succ,add_div,div_self hi.ne']
lemma taxes : Tendsto (levy C) atTop (𝓝 0):=by
    have hp := (next_rate (C:=C) h).log one_ne_zero; rw [Real.log_one] at hp; exact hp.congr (fun i=> Real.log_div (β_pos ..|>.ne') (β_pos ..|>.ne'))
omit h in
lemma speck : RateIs atTop (hill C) (β C) 1:= by
    refine ⟨Eventually.of_forall fun _=> β_pos ..,tendsto_const_nhds.congr fun i=> (div_self (hill_pos C i).ne').symm⟩
lemma plateau : RateIs atTop C.S.scale (β C) 0:=by
    have hv := ((show Tendsto (fun i => Real.log (β C i) / β C i) atTop (𝓝 0) from (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp (β_ascent h)).mul (mount_rate (C:=C))); rw [zero_mul] at hv
    refine ⟨(speck (C:=C)).pos,hv.congr fun i=>?_⟩; have h := (β_pos C i).ne'; change Real.log (β C i)/β C i * (β C i / C.S.scale i) = _; rw [← mul_div_assoc, div_mul_cancel₀ _ h]
omit h in
lemma reap (k:ℕ):∀ i,β C (i+1)^k = Real.exp ((k:ℝ)*levy C i) *β C i^k:=by
    intro i; unfold levy; rw [mul_sub,Real.exp_sub,← Real.log_pow,← Real.log_pow,Real.exp_log (pow_pos (β_pos C _) _),Real.exp_log (pow_pos (β_pos C _) _), div_mul_cancel₀ _ (by have := β_pos C i; positivity)]
lemma raises : ∀ᶠ i:ℕ in atTop, levy C i * β C i ≥ G.slopeConstant*Real.log 2 /4 := by
    -- coarse exact increment; lower from log >= (x-1)/x
    filter_upwards [(next_rate (C:=C) h).eventually (ge_mem_nhds (by norm_num: (1:ℝ)<4))] with i hi
    let a:= β C (i+1); let b:= β C i; have hb:0 < b:= β_pos ..;have ha:0<a:= β_pos ..;have hc: a/b ≤ 4:= hi
    have hp := Real.log_le_sub_one_of_pos (show 0 < b/a from div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at hp
    have hk:= (G.slopeConstant_pos h)
    have he : G.slopeConstant*Real.log 2 ≤ a-b:=by
       change _ ≤ (_+G.slopeConstant*C.S.scale _)-(_+G.slopeConstant*C.S.scale _); rw [Schedule.scale_succ]
       have hh:= Real.log_le_log (by norm_num: (0:ℝ)<2) (extent_two C i); linarith [mul_le_mul_of_nonneg_left hh hk.le] -- levels defeq?
    change _ ≤ (Real.log a-Real.log b) * b
    have hy : (Real.log a-Real.log b)*a ≥ a-b:=by
       have ht: b/a*a=b:=div_mul_cancel₀ _ ha.ne'; linarith only [mul_le_mul_of_nonneg_right hp ha.le,ht]
    have hh: a ≤ 4*b:= (div_le_iff₀ hb).1 hc
    linarith only [hy,he,mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.log a-Real.log b from (levy_pos (C:=C) h i).le)]
end YM.OPE.Lake
