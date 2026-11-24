import YM.Integration.WilsonMovingForkOwnRadiusHearing
import YM.Integration.WilsonIndependentCapturedPages

/-! Cofinality of the earlier stop chosen on the original finite coupling calendar. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 380000
noncomputable section
namespace YM.Integration.WilsonMovingForkCofinalStops
open Function Filter Set Lattice Wilson RG Extraction Table OPE OPE.Owl
open Source Spec Climb Trace.Pilot Maxwell Maxwell.Free FVA2 FVA2.Register MS MS.Land GapsContact GapsContact.Seams
open PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonPositionProgramReporterBand (Band)
open WilsonIndependentCapturedPages (Stop)
open WilsonMovingForkOwnRadiusSites (capture size)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open scoped Classical Topology
variable {G:Gauge}(R:Run G){D:XSpace.Run}{stage u depth:ℕ}{B:Band R D stage}

theorem original (v:Stop R D B u depth):Tendsto v.date atTop atTop:=by
  let c:=fun t=>B.reporter+t
  let s:=fun t=>R.family.S.scale (c t)
  let C:=max 1 (2*b0 G+1)
  let L:ℝ:=4*(2*(depth:ℝ)+1)
  have cp:0<C:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have lp:0<L:=by dsimp [L]; positivity
  have ct:Tendsto c atTop atTop:=tendsto_atTop_mono (fun t=>Nat.le_add_left t B.reporter) tendsto_id
  have st:Tendsto s atTop atTop:=R.family.S.divergent.comp ct
  have small:Tendsto (fun t=>Real.log (s t)/s t) atTop (𝓝 0):=Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp st
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [v.heard,ct.eventually (zeroUp_bound R.family R.makes (ε:=1) one_pos),
    st.eventually_ge_atTop 1,st.eventually_gt_atTop (4*(L*|Real.log C|+|R.family.S.scale k|+1)),
    small.eventually_lt_const (show (0:ℝ)<1/(4*L) by positivity)] with t heard running big paid logPay
  obtain ⟨pos,_,_,late⟩:=heard.2 (c t) 0 le_rfl
  have sp:0<s t:=zero_lt_one.trans_le big
  have cg:1≤C*s t:=one_le_mul_of_one_le_of_one_le (le_max_left ..) big
  have engine:R.family.path.β (c t) 0 (c t)≤C*s t:=by
    apply (div_le_iff₀ sp).mp
    exact (show R.family.path.β (c t) 0 (c t)/s t≤2*b0 G+1 from by
      have close:=(abs_lt.mp (running (c t) 0 le_rfl)).2
      linarith).trans (le_max_right ..)
  have scaled:(regulatorRun R.family (c t) 0 (c t))⁻¹≤C*s t:=by
    simp only [regulatorRun,inv_inv]
    apply Real.sqrt_le_iff.mpr
    exact ⟨zero_le_one.trans cg,engine.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr cg) (le_trans zero_le_one cg)])⟩
  have gain:=Real.log_le_log (inv_pos.mpr pos) scaled
  rw [Real.log_mul cp.ne' sp.ne'] at gain
  have reserve:Real.log (s t)*(4*L)<s t:=by
    simpa only [one_mul] using (div_lt_div_iff₀ sp (show 0<4*L by positivity)).mp logPay
  have actual:s t-R.family.S.scale (v.date t)≤L*(Real.log C+Real.log (s t)):=
    late.trans (mul_le_mul_of_nonneg_left gain lp.le)
  apply (OPE.scale_mono R.family.S).le_iff_le.mp
  linarith only [actual,reserve,paid,mul_le_mul_of_nonneg_left (le_abs_self (Real.log C)) lp.le,
    le_abs_self (R.family.S.scale k),mul_nonneg lp.le (abs_nonneg (Real.log C)),abs_nonneg (R.family.S.scale k)]

theorem previous (v:Stop R D B u depth):Tendsto (fun t=>v.date t-1) atTop atTop:=by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [(original R v).eventually_ge_atTop (k+1)] with t live using by omega

theorem moving {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
    (simple:G.Simple)(bliss:Bliss F l z H)(A:ℕ){M:ℝ}(mp:0≤M)(v:Stop R D B u depth):
    let index:=fun r=>capture R.family.S M r (outer z A r)-B.reporter
    Tendsto (fun r=>v.date (index r)-1) trail atTop ∧
    ∀ᶠr in trail,B.reporter+index r=capture R.family.S M r (outer z A r):=by
  intro index
  have approach:=longer F simple bliss A
  have near:Tendsto (fun r:ℝ=>r) trail (𝓝 0):=nhdsWithin_le_nhds
  have far:Tendsto (outer z A) trail (𝓝 0):=approach.mono_right nhdsWithin_le_nhds
  have actual:Tendsto (fun r=>size M r (outer z A r)) trail trail:=by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have exactSize:Tendsto (fun r=>16*(r+M*outer z A r)) trail (𝓝 0):=by
        simpa only [mul_zero,add_zero] using (near.add (far.const_mul M)).const_mul 16
      apply exactSize.congr'
      filter_upwards [show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin] with r hr
      exact (WilsonMovingForkOwnRadiusSites.expanded M hr _).symm
    · filter_upwards [show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin,
        approach.eventually (show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin)] with r hr ht
      change 0<size M r (outer z A r)
      rw [WilsonMovingForkOwnRadiusSites.expanded M hr _]
      positivity
  have grows:Tendsto (fun r=>capture R.family.S M r (outer z A r)) trail atTop:=(WilsonCloseCaptureDate.height R).grows.comp actual
  have reached:Tendsto index trail atTop:=by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [grows.eventually_ge_atTop (B.reporter+k)] with r plenty
    change k≤capture R.family.S M r (outer z A r)-B.reporter
    omega
  refine ⟨(previous R v).comp reached,?_⟩
  filter_upwards [grows.eventually_ge_atTop B.reporter] with r arrive
  dsimp only [index]
  omega

end YM.Integration.WilsonMovingForkCofinalStops
end
