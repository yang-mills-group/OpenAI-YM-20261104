import YM.Integration.WilsonViewerPositionJets
import YM.Integration.WilsonOneFramePhysicalPivot
import YM.Pert.FirstTarget

/-! The true metric stress on the same final frame as the signed matching law. -/
set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace YM.Integration.WilsonOneFrameMeasuredStress
open Function Filter Set Spec Climb OPE OPE.Orbits PhysMS PhysMS.Frame Trace Trace.Pilot
open Trace.Pith Table Next.UVStress TraceExtension
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMacroscopicRichTwoDatePivot (active)
open WilsonViewerElectedHierarchy (Selected)
open scoped Topology BigOperators Classical
section UnitTerm
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S)
private theorem unit_term (H : (Bel C.book).Hierarchy) {s a d e : ℝ} (P : Spin.change S 4)
    (angle : AlignV F.room.kernel F.sector H P) (m : Measures F s P a d e) :
    (4 : ℝ) • (e : ℂ) = s^4 • expectation S 4 (stressTrace F.sector.energy) := by
  let v := stressTrace F.sector.energy
  have form : P.symm (s^4 • v) =
      (4:ℝ) • (d • stepField C + e • (Bel C.book).unit 4) := by
    calc
      _ = ∑ k : Axis, (a • standard4 C k k + (d • stepField C + e • (Bel C.book).unit 4)) := by
        unfold v stressTrace
        rw [Finset.smul_sum, map_sum]
        apply Finset.sum_congr rfl
        intro k _
        simpa [Trace.Pith.erase, add_assoc] using m.reads k k
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.smul_sum, trace_none, smul_zero, zero_add,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_cast
  let E := (expectation (Bel C.book) 4).restrictScalars ℝ
  have val := congrArg E form
  have vev : E (P.symm (s^4 • v)) = s^4 • expectation S 4 v := by
    change expectation (Bel C.book) 4 _ = _
    rw [← angle.cent, P.apply_symm_apply]
    exact ((expectation S 4).restrictScalars ℝ).map_smul ..
  rw [vev, map_smul, map_add, map_smul, map_smul,
    show E (stepField C) = 0 from sceneV H,
    show E ((Bel C.book).unit 4) = 1 from mean_unit H.laws,smul_zero,zero_add] at val
  simpa using val.symm


end UnitTerm
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    {F:Spec.Final R.family f S}{J:ℝ→PhysMS.tower S}{Z0:Trace.Terrace.Arch R.family}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {L:EveryPhase.Almanac F}{Y:(Bel R.family.book).Hierarchy}{ℓ:Ultrafilter (ℕ×ℕ)}
    {simple:G.Simple}{cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:Selected.{u} F L Q J Y Z0 ℓ simple cohort)(Z:WilsonPrescription G)
local notation "RFam" => R.family

include run in
theorem original (i j : Axis) :
    Tendsto (fun r : ℝ => (homogeneous F J Z r 4).symm (r^4 • F.sector.energy i j))
      trail (𝓝 (Pert.freeStress R.family.labels i j)) := by
  obtain ⟨T,P,χ,a,d,e,same,_,comp⟩ := run.calibration
  have drops (g k : ℝ → ℝ) (coupled : Coupling G g) {c : ℝ}
      (rated : Tendsto (fun r => k r / (g r)^2) trail (𝓝 c)) : Tendsto k trail (𝓝 0) := by
    have zero := (coupled.conforms simple).pow 2
    have result : Tendsto (fun r => (k r / (g r)^2) * (g r)^2) trail (𝓝 0) := by
      simpa using rated.mul zero
    apply result.congr'
    filter_upwards [coupled.positive] with r hg
    exact div_mul_cancel₀ _ (pow_ne_zero _ hg.ne')
  have small : Tendsto d trail (𝓝 0) := drops _ _ comp.coupling (comp.leading.measures _ comp.coupling)
  have e4 : Tendsto (fun r : ℝ => (4:ℝ) • (e r : ℂ)) trail (𝓝 0) := by
    have z : Tendsto (fun r : ℝ => r^4 • expectation S 4 (stressTrace F.sector.energy))
        trail (𝓝 0) := by
      have hr : Tendsto (fun r : ℝ => r) trail (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (hr.pow 4).smul_const
        (expectation S 4 (stressTrace F.sector.energy))
    apply z.congr'
    filter_upwards [comp.alignment.spun, comp.measures] with r hi hme
    exact (unit_term F Y (P r) hi hme).symm
  have ec : Tendsto (fun r : ℝ => (e r : ℂ)) trail (𝓝 0) := by
    simpa [smul_smul, inv_mul_cancel₀ (by norm_num : (4:ℝ) ≠ 0)] using e4.const_smul (4:ℝ)⁻¹
  have er : Tendsto e trail (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] using (Complex.continuous_re.tendsto (0:ℂ)).comp ec
  have name : standard4 RFam = Pert.freeStress R.family.labels := by
    rw [show standard4 RFam = _ from Trace.Over.canonical_meter (C := RFam)]
    change UVNext.FreeStress.torch R.family.labels (-1) = -Maxwell.Free.original R.family.labels
    rw [← Pert.common_stress, UVNext.FreeStress.torch, UVNext.FreeStress.torch, neg_one_smul, one_smul]
  have lim := ((comp.spinTwo.smul_const (standard4 RFam i j)).add
    (small.smul_const (erase (C:=RFam) (stepField RFam) i j))).add
      (er.smul_const (erase (C:=RFam) ((Bel R.family.book).unit 4) i j))
  have enrolled : Tendsto (fun r => (J r 4).symm (r^4 • F.sector.energy i j)) trail (𝓝 (Pert.freeStress R.family.labels i j)) := by
    rw [←name]
    simpa only [one_smul,zero_smul,add_zero] using lim.congr' (show ∀ᶠ r in trail, _ =
      (J r 4).symm (r^4 • F.sector.energy i j) from by
      filter_upwards [same,comp.measures] with r hJ hme
      rw [hJ]
      exact (hme.reads i j).symm)


  let v := Pert.freeStress R.family.labels i j
  have atV := WilsonMacroscopicRichTwoDatePivot.field F J Z run.leading run.obeys simple 4 v
  have van : Tendsto (fun r => ‖(J r 4).symm (r^4 • F.sector.energy i j) -
      active F J Z r 4 v‖) trail (𝓝 0) := by
    simpa [v] using (enrolled.sub atV).norm
  obtain ⟨_,_,room⟩ := WilsonOneFramePhysicalPivot.original F J Z run.leading run.obeys simple 4
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa using (tendsto_const_nhds (x:=(2:ℝ))).mul van)
  filter_upwards [room] with r use
  let A := active F J Z r 4
  have cost := (use ((J r 4).symm (r^4 • F.sector.energy i j) - A v)).2
  rw [map_sub,A.symm_apply_apply] at cost
  have paid : A.symm ((J r 4).symm (r^4 • F.sector.energy i j)) =
      (homogeneous F J Z r 4).symm (r^4 • F.sector.energy i j) := by
    change (homogeneous F J Z r 4).symm (J r 4 ((J r 4).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
  rwa [paid] at cost

end YM.Integration.WilsonOneFrameMeasuredStress
end
