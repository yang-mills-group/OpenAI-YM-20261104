import YM.FormalBulk08.First.Pave

/-! moving level normalization coefficient. Not derivative in any trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.First
open Function Filter Set MeasureTheory Lattice RG Exterior Wilson Precision
open Stationary hiding shine Rays
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine Dove North
open Next.Foundations PhysicalNext.Repeat.Legato Pert.Flow Pert.Asymptotics
variable {G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{A:Levels G}{C:Family G}
variable (L:∀ i,Lodge ((C.path.levels.clock.op i 0).patch))
variable (h:LocalRatio ρ)(p:Provenance G C ρ)(hG:G.Simple)(a:hue G)
section beta
variable {N:ℕ→ℕ}(hp:∀ᶠ i in atTop,i<N i)
include hG h p hp
lemma lambda_step : Tendsto (fun i=>coeff 2 (stride C.path.levels L ρ a (N i) i)/logStride C i) atTop (𝓝 (-G.slopeConstant)) := by
    refine Metric.tendsto_nhds.mpr fun ε he=> ?_
    filter_upwards [hp,(drift_price (C:=C)).eventually (gt_mem_nhds he)] with i hx hv
    let d:= logStride C i; let Z:= coeff 2 (stride _ L ρ a (N i) i)
    change dist (Z / d) _< ε; have hd:0<d:=stride_pos i;rw [Real.dist_eq,sub_neg_eq_add,show Z/d + G.slopeConstant= (Z+G.slopeConstant*d)/d from (by field_simp),abs_div,abs_of_pos hd]; have he : |Z+G.slopeConstant*d|+1≤ (C.path.levels.params (i+1)).drift := (beta_point hG p h _ 0 _ hx L a).2; exact lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith only [he]: |Z+G.slopeConstant*d|≤(C.path.levels.params (i+1)).drift) hd.le) hv
lemma first_step : Tendsto (fun i=>coeff 3 (wake (stride C.path.levels L ρ a (N i) i))/logStride C i) atTop (𝓝 (b0 G)):=by
    have H:= (lambda_step L h p hG a hp).neg.div_const 2;rw [neg_neg, show G.slopeConstant / 2= b0 G by rw [←b0_normalizes];ring] at H
    refine H.congr' (hp.mono ?_); intro i hv; obtain ⟨h₁,h₂⟩:= gains L a h hG _ _ hv; dsimp only; rw [(spin_price _ h₁ h₂).apex, _root_.map_add,coeff_C_mul]; norm_num [coeff_X_pow,coeff_X]; ring
end beta
section
variable {ℓ:ℕ} (k:ℕ) (O:Borough.Window G C.path.levels.clock.kernel) (Q:Spigot.Herald)
-- plan on single C, choose its labels. lifts defined elsewhere. Post statement after preparation from income(W).
abbrev cbook (t:Aster.Time ℕ) := Borough.register G C.path.levels.clock.kernel (I_ C L) O (fun _=> k) (fun _=> t) where
    I_ (C:Family G) (L:∀ i,Lodge ((C.path.levels.clock.op i 0).patch)):Empire G C.path.levels.clock.kernel PUnit.{1} :=⟨fun _=>C.path.levels,fun _=>rfl,fun _=>L⟩
variable {L k O}
open Dove.Lab
include h hG
lemma delta_p (t:Aster.Time ℕ)(i:ℕ)(he:k ≤ i)(u:Use (cbook (C:=C) L k O t) ρ ℓ)(ht:2≤ ℓ): Tendsto (fun n : ℕ=> coeff 2 (stride C.path.levels L ρ a n i)) atTop (𝓝 (coeff 2 (haloO (W:=cbook L k O t) ρ a ⟨PUnit.unit,i,(show (cbook L k O t).scrolls.ell _ ≤ i from he)⟩))) := by let x : Leaf (cbook L k O t).scrolls:= ⟨PUnit.unit,i,he⟩; exact divisionC a u h hG x ht
include p
lemma kinetic_at (t:Aster.Time ℕ)(i:ℕ)(he:k ≤ i)(u:Use (cbook (C:=C) L k O t) ρ ℓ)(ht:2≤ ℓ) :
     let x:Leaf (cbook L k O t).scrolls:=⟨PUnit.unit,i,he⟩
     let Z:= coeff 2 (haloO ρ a x); |Z + G.slopeConstant*Real.log ((C.S.block i).val:ℝ)|+1 ≤ (C.path.levels.params (i+1)).drift := by
   intro x Z; apply le_of_tendsto (((delta_p (k:=k) (L:=L) h hG a t i he u ht).add_const _).abs.add_const 1)
   filter_upwards [eventually_gt_atTop i] with j hj; exact (beta_point hG p h _ 0 i hj L a).2
end
end YM.FormalBulk08.First
