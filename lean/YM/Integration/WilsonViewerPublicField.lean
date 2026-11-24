import YM.Integration.WilsonMacroscopicViewerCharge
import YM.RG12.Kintsugi.Spot
import YM.PhysMS.Frame.Apply
import YM.Trace2.Transfer

/-! Forward physical position-frame price at every finite horizon.
Positive-weight coordinates vanish. The surviving unit is determined by the
same unselected one-point function, before the exterior or viewer is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonViewerPublicField
open Function Filter Set Table Spec Trace.Pilot OPE OPE.Orbits Climb PhysMS
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
  (F:Final C f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J:ℝ→tower S)(lead:Leading F J)(simple:G.Simple)

private def sample (d:ℕ):S.Field d →L[ℂ] ℂ:=
  ((S.classMoment S (fun _:Fin 1=>d) (points fun _=>0)).toLinearMap (fun _=>0) 0).toContinuousLinearMap

include F in
private theorem seesUnit (d:ℕ):sample (S:=S) d (S.unit d)=1:=by
  have sees:=Trace.oneToken_scalar S S F.room.kernel.laws (spectate_respects F none) 0 d
    (C.book.scalar d) (1:ℂ) (by rw [one_smul];rfl)
  rw [Trace.oneToken_class F.room.kernel.laws.toSymmetric (spectate_respects F none),
    Trace.oneToken_linear] at sees
  exact sees

include F Q lead simple in
theorem limit (d:ℕ)(v:(Bel C.book).Field d):
    Tendsto (fun r=>J r d v) trail (𝓝 (WickGoal (C:=C) (d:=fun _:Fin 1=>d) (fun _=>v) 0 • S.unit d)):=by
  let part (i:Fin (d+1))(r:ℝ):S.Field d:=F.sector.derivatives.rise (Nat.le_of_lt_succ i.isLt) (Q.cutTest i.val d (J r d v))
  let upper (r:ℝ):S.Field d:=∑ i:Fin d,part i.succ r
  have totals (r:ℝ):J r d v=part 0 r+upper r:=by
    have rebuilt:=Q.reconstruct d d le_rfl (J r d v)
    rw [F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts] at rebuilt
    exact rebuilt.symm.trans (Fin.sum_univ_succ _)
  have dies (i:Fin d):Tendsto (part i.succ) trail (𝓝 0):=by
    let T: S.Field i.succ.val→L[ℂ] S.Field d:=
      (F.sector.derivatives.rise (Nat.le_of_lt_succ i.succ.isLt)).toContinuousLinearMap
    have row:=Frame.entrust F Q J lead (r:=id) tendsto_id d i.succ.val (Nat.le_of_lt_succ i.succ.isLt) v
    have hp : -(i.succ.val:ℝ)<0:=by exact neg_lt_zero.mpr (by exact_mod_cast Nat.zero_lt_succ _)
    have low:=row.tends hp (to_log_zoom.comp tendsto_id)
    have hT:Tendsto T (𝓝 0) (𝓝 0):=by simpa only [map_zero] using T.continuous.tendsto 0
    exact hT.comp low
  have tail:Tendsto upper trail (𝓝 0):=by
    have st:=tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun i _=>dies i)
    simpa only [Finset.sum_const_zero] using st
  let B:=WickGoal (C:=C) (d:=fun _:Fin 1=>d) (fun _=>v) 0
  have base:Tendsto (fun r=>sample (S:=S) d (J r d v)) trail (𝓝 B):=by
    have lim:=leading_at F lead (r:=id) (x:=fun _:ℝ=>(0:Points 1)) (v:=fun _:Fin 1=>v) (d:=fun _=>d)
      tendsto_id tendsto_const_nhds (fun _ _ _=>Subsingleton.elim ..)
    apply lim.congr'
    exact Eventually.of_forall fun r=>by simp only [measured,smul_zero]; exact Trace.oneToken_linear S S 0 d _
  have l0:Tendsto (fun r=>sample (S:=S) d (upper r)) trail (𝓝 0):=by
    have hs:Tendsto (sample (S:=S) d) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using (sample (S:=S) d).continuous.tendsto 0
    exact hs.comp tail
  have payable:=((base.sub l0).smul (tendsto_const_nhds (x:=S.unit d))).add tail
  apply (show Tendsto (fun r=>(sample (S:=S) d (J r d v)-sample (S:=S) d (upper r)) • S.unit d+upper r)
    trail (𝓝 (B • S.unit d)) by simpa only [sub_zero,add_zero] using payable).congr'
  apply Eventually.of_forall
  intro r
  obtain ⟨c,unit⟩:=RG12.Kintsugi.Spot.unit_desc (C:=C) (S:=S) simple (show 0<4 by decide) (Q.cutTest 0 d (J r d v))
  have p0:part 0 r=c • S.unit d:=by
    change F.sector.derivatives.rise (Nat.zero_le d) (Q.cutTest 0 d (J r d v))=_
    rw [unit,map_smul,F.sector.derivatives.fixs Q.lifts Q.continuum.laws]
  change (sample (S:=S) d (J r d v)-sample (S:=S) d (upper r)) • S.unit d+upper r=J r d v
  rw [totals r,p0,map_add,map_smul,seesUnit F,smul_eq_mul,mul_one,add_sub_cancel_right]

include F Q lead simple in
theorem bounded (d:ℕ):∃ D:ℝ,0≤D ∧ ∀ᶠ r in trail,∀ v:(Bel C.book).Field d,‖J r d v‖≤D*‖v‖:=by
  let B:=Module.finBasis ℂ ((Bel C.book).Field d)
  let L (i:Fin (Module.finrank ℂ ((Bel C.book).Field d))):=
    ‖WickGoal (C:=C) (d:=fun _:Fin 1=>d) (fun _=>B i) 0 • S.unit d‖+1
  have pos i:0≤L i:=by dsimp only [L];positivity
  have paid i:∀ᶠr in trail, ‖J r d (B i)‖≤L i:=
    ((limit F Q J lead simple d (B i)).norm.eventually (ge_mem_nhds (lt_add_one _)))
  refine ⟨∑i,‖(B.coord i).toContinuousLinearMap‖*L i,Finset.sum_nonneg (fun i _=>
    mul_nonneg (B.coord i).toContinuousLinearMap.opNorm_nonneg (pos i)),?_⟩
  filter_upwards [eventually_all.mpr paid] with r held v
  rw [Finset.sum_mul]
  nth_rw 1 [←B.sum_repr v]
  rw [map_sum]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
  rw [map_smul,norm_smul,mul_right_comm]
  exact mul_le_mul ((B.coord i).toContinuousLinearMap.le_opNorm v) (held i) (norm_nonneg _)
    (mul_nonneg (B.coord i).toContinuousLinearMap.opNorm_nonneg (norm_nonneg _))

end YM.Integration.WilsonViewerPublicField
end
