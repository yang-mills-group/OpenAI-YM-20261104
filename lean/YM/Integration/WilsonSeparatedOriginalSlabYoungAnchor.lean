import YM.Integration.WilsonSeparatedOriginalProfileAnchor
import YM.Integration.WilsonSeparatedOriginalSlabActiveWeights
import YM.Integration.WilsonMacroscopicRichReportingRate

/-! On the actual finer capture mesh the full compact parent radius grows at most by one original block. These true parents still fit the purchased mortar for all periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabYoungAnchor
open Function Filter Finset MeasureTheory Lattice Wilson RG Source MergeProof RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabActiveWeights WilsonSeparatedOriginalProfileAnchor
open scoped BigOperators Classical Topology
variable {G:Gauge}(C:Family G)

theorem clock (hG:G.Simple)(pace:∀b:ℕ,((C.S.block b).val:ℝ)≤Real.log (RG16.Lambda C.path.levels b))
    {cap:ℝ}(cp:0≤cap):∀ᶠb:ℕ in atTop,∀r:ℝ,0≤r → r≤C.S.a b → 
      2*range C (b+1) r cap ≤ (C.path.levels.budget (b+1)).B:=by
  let A:=C.path.levels
  have late:∀ᶠb:ℕ in atTop,8*cap+12≤Real.log (A.clock.hatBeta (b+1)):=
    (tendsto_add_atTop_nat 1).eventually ((Real.tendsto_log_atTop.comp (RG01.Physical.hats hG A)).eventually_ge_atTop _)
  filter_upwards [late] with b mature
  intro r rp room
  let y:=Real.log (A.clock.hatBeta (b+1))
  have yp:0≤y:=Real.log_nonneg (A.fits.delayed _).le
  have step:Real.log (A.clock.hatBeta b)≤y:=Real.log_le_log (zero_lt_one.trans (A.fits.delayed _))
    (WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos hG).le (Nat.le_succ b))
  have cpos:0<2+Real.log (A.clock.hatBeta b):=by positivity [Real.log_nonneg (A.fits.delayed b).le]
  have factor:((C.S.block b).val:ℝ)≤y+1:=by
    apply (pace b).trans;change Real.log (2+Real.log (A.clock.hatBeta b))≤_
    linarith [Real.log_le_sub_one_of_pos cpos]
  have ap:=C.S.a_pos (b+1)
  have Npos:0<((C.S.block b).val:ℝ):=by exact_mod_cast (C.S.block b).property
  have mesh:C.S.a (b+1)*((C.S.block b).val:ℝ)=C.S.a b:=by rw [C.S.a_step,div_mul_cancel₀ _ Npos.ne']
  have quotient:r/C.S.a (b+1)≤((C.S.block b).val:ℝ):=(div_le_iff₀ ap).2 (by rwa [mul_comm,mesh])
  have positive:0≤(r*cap+2*C.S.a (b+1))/C.S.a (b+1):=by positivity
  have J:(range C (b+1) r cap:ℝ)≤(y+1)*cap+3:=by
    have ceil: (range C (b+1) r cap:ℝ) < (r*cap+2*C.S.a (b+1))/C.S.a (b+1)+1:=Nat.ceil_lt_add_one positive
    have cut:(r*cap+2*C.S.a (b+1))/C.S.a (b+1)=(r/C.S.a (b+1))*cap+2:=by field_simp
    rw [cut] at ceil
    linarith [mul_le_mul_of_nonneg_right (quotient.trans factor) cp]
  have square:y^2 ≤ ((A.budget (b+1)).B:ℝ):=Nat.le_ceil _
  have ym:8*cap+12≤y:=mature
  have high:2*((y+1)*cap+3)≤y^2:=by nlinarith [mul_nonneg (show 0≤y-2*cap-6 from by linarith) (show 0≤y-1 from by linarith)]
  exact_mod_cast (show (2:ℝ)*(range C (b+1) r cap:ℝ) ≤ ((A.budget (b+1)).B:ℝ) by linarith)

theorem original (hG:G.Simple)(pace:∀b:ℕ,((C.S.block b).val:ℝ)≤Real.log (RG16.Lambda C.path.levels b))
    {cap:ℝ}(cp:0≤cap):∀ᶠb:ℕ in atTop,∀r:ℝ,0≤r → r≤C.S.a b → ∀per (o:Fin 3 → Site (C.side (b+1) per)),
      o∈Pulse.area (C:=C) (range C (b+1) r cap) → ∀shift:Site (C.side (b+1) per),∀i,
        coverNumber ((C.path.levels.budget (b+1)).B) ({o 0+shift,o i+shift}:Support (C.side (b+1) per)) ≤
          Ribbons.peepers C.path.levels (b+1):=by
  filter_upwards [clock C hG pace cp] with b paid
  intro r rp room per o eligible shift i
  let B:=(C.path.levels.budget (b+1)).B
  let x:=o 0+shift
  let y:=o i+shift
  have B0:0<B:=(C.path.levels.budget (b+1)).B_pos
  have apart:separation x y≤(1024*B)*B:=by
    change separation (o 0+shift) (o i+shift)≤_
    rw [separation_translate];apply (separation_of_area C eligible 0 i).trans
    apply (paid r rp room).trans; nlinarith [Nat.mul_le_mul_left B (show 1≤B from B0)]
  have cover:({x,y}:Support (C.side (b+1) per))⊆halo ((1024*B)*B) {x}:=by
    intro z hz;rcases Finset.mem_insert.mp hz with h|h
    · subst z;exact halo_spec.mpr ⟨x,mem_singleton_self _,by simp⟩
    · rw [mem_singleton.mp h];exact halo_spec.mpr ⟨x,mem_singleton_self _,apart⟩
  exact (Corona.cover_mono cover B).trans (by simpa only [Ribbons.peepers,two_mul] using Corona.tile x (1024*B) B (C.path.levels.budget (b+1)).B_pos)

end YM.Integration.WilsonSeparatedOriginalSlabYoungAnchor
