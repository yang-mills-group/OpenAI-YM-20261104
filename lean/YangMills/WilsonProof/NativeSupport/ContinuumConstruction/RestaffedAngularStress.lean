import YM.TraceExtension.Pith.Orders
import YM.Pert.FirstTarget
set_option maxHeartbeats 850000
set_option maxRecDepth 8192
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.RestaffedAngularStress
open Function Filter Set Spec Climb Trace Trace.Pilot
open Trace.Pith Table Next.UVStress TraceExtension
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (simple : G.Simple)

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


theorem calibrated {U : ℝ → ∀ k : ℕ, Spin.change S k} (H : (Bel C.book).Hierarchy)
    {Z : Trace.Terrace.Arch C} {l : Ultrafilter (ℕ × ℕ)} (bliss : Bliss F l Z H)
    (angle : PlotX F H l simple (fun r => U r 4))
    (choresU : ∀ m, ∀ᶠ r in trail, chores r (U r 4) m) (coupling : Coupling G (Trace.Pilot.wilson Z)) (i j : Axis) :
    Tendsto (fun r : ℝ => (U r 4).symm (r^4 • F.sector.energy i j))
      trail (𝓝 (Pert.freeStress C.labels i j)) := by
  obtain ⟨d, hd⟩ := margaret F simple bliss (fun r => U r 4) angle
  obtain ⟨a, e, hm, ha, _, _⟩ := formed H F simple coupling hd angle choresU
  have small := postd H F simple coupling hd angle
  have e4 : Tendsto (fun r : ℝ => (4:ℝ) • (e r : ℂ)) trail (𝓝 0) := by
    have z : Tendsto (fun r : ℝ => r^4 • expectation S 4 (stressTrace F.sector.energy))
        trail (𝓝 0) := by
      have hr : Tendsto (fun r : ℝ => r) trail (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (hr.pow 4).smul_const
        (expectation S 4 (stressTrace F.sector.energy))
    apply z.congr'
    filter_upwards [angle, hm] with r hi hme
    exact (unit_term F H (U r 4) hi.1.frame hme).symm
  have ec : Tendsto (fun r : ℝ => (e r : ℂ)) trail (𝓝 0) := by
    simpa [smul_smul, inv_mul_cancel₀ (by norm_num : (4:ℝ) ≠ 0)] using e4.const_smul (4:ℝ)⁻¹
  have er : Tendsto e trail (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] using (Complex.continuous_re.tendsto (0:ℂ)).comp ec
  have name : standard4 C = Pert.freeStress C.labels := by
    rw [show standard4 C = _ from Trace.Over.canonical_meter (C := C)]
    change UVNext.FreeStress.torch C.labels (-1) = -Maxwell.Free.original C.labels
    rw [← Pert.common_stress, UVNext.FreeStress.torch, UVNext.FreeStress.torch, neg_one_smul, one_smul]
  rw [← name]
  have lim := ((ha.smul_const (standard4 C i j)).add
    (small.smul_const (erase (C:=C) (stepField C) i j))).add
      (er.smul_const (erase (C:=C) ((Bel C.book).unit 4) i j))
  simpa only [one_smul, zero_smul, add_zero] using
    lim.congr' (hm.mono fun r he => (he.reads i j).symm)


end YM.RestaffedAngularStress
end
