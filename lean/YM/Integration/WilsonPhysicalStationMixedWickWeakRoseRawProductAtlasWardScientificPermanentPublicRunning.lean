import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMicroscopicShift

noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicRunning
open Filter Function Set RG Lattice Table Spec
open scoped Topology

set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

theorem increase (S:Schedule)(n:ℕ):(n:ℝ)*Real.log 3≤S.scale n:=by
  induction n with
  | zero => simp [Schedule.scale,Schedule.a,Schedule.denominator]
  | succ i previous =>
    rw [S.scale_succ]
    have large:(3:ℝ)≤((S.block i).val:ℝ):=by exact_mod_cast S.block_large i
    have step:=Real.log_le_log (by norm_num : (0:ℝ)<3) large
    push_cast
    linarith

theorem large (S:Schedule):Tendsto S.scale atTop atTop:=by
  refine Filter.tendsto_atTop.2 ?_
  intro w
  have pos:0<Real.log (3:ℝ):=Real.log_pos (by norm_num)
  obtain ⟨n,hn⟩:=exists_nat_ge (w/Real.log 3)
  filter_upwards [eventually_ge_atTop n] with m hm
  have v:w/Real.log 3≤(m:ℝ):=hn.trans (by exact_mod_cast hm)
  exact ((div_le_iff₀ pos).mp v).trans (increase S m)

theorem original {G:Gauge}(C:Family G)(paid:C.Makes)(simple:G.Simple):
    0<Trace.Over.b0 G ∧
    ∀ε:ℝ,0<ε→∀ᶠN:ℕ in atTop,∀p:ℕ,
      |C.beta N p/Real.log (C.S.a N)⁻¹-2*Trace.Over.b0 G|<ε:=by
  have slope:G.slopeConstant=2*Trace.Over.b0 G:=by
    unfold Gauge.slopeConstant Trace.Over.b0
    ring
  refine ⟨by linarith [Gauge.slopeConstant_pos simple],?_⟩
  intro ε hp
  have third:0<ε/3:=by positivity
  filter_upwards [paid.wilson.running (ε/3) third,
    (large C.S).eventually_gt_atTop (max 0 (C.path.levels.clock.bar/(ε/3)))] with N chosen date
  intro p
  have price:=chosen N p le_rfl
  change |C.beta N p-(C.path.levels.clock.bar+G.slopeConstant*C.S.scale N)|≤(ε/3)*(C.S.scale N) at price
  have positive:0<C.S.scale N:=(le_max_left _ _).trans_lt date
  have old:C.path.levels.clock.bar<(C.S.scale N)*(ε/3):=(div_lt_iff₀ third).mp ((le_max_right _ _).trans_lt date)
  obtain ⟨lower,upper⟩:=abs_le.mp price
  change |C.beta N p/C.S.scale N-2*Trace.Over.b0 G|<ε
  rw [←slope,abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ positive]
    nlinarith [C.path.levels.clock.bar_pos,mul_pos hp positive]
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ positive]
    nlinarith [mul_pos hp positive]

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicRunning
end
