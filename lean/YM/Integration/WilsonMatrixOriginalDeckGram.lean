import YM.Integration.WilsonMatrixOriginalDeckColumns
import YM.Integration.MSSeparatedSmearedTreeGram
import YM.RG17.Layout

/-! The full physical and independently calculated matrices on the same compact test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckGram
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set OPE OPE.Orbits PhysMS MeasureTheory
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (B : Deck G) {O : Booked B}
variable (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S)

def bank (h : ℕ) (g : Test 2) (r : ℝ) : Matrix (Glyph B h) (Glyph B h) ℂ :=
  fun a b=>g.applyTo (PhysMS.measured F none (J r) (d:=fun _ : Fin 2=>h)
    (WilsonMatrixOriginalDeckColumns.basis C B h ∘ ![a,b]) r)

private theorem regular {h : ℕ} (a b : Glyph B h) {r : ℝ} (hr : 0<r) :
    ContinuousOn (PhysMS.measured F none (J r) (d:=fun _ : Fin 2=>h) (WilsonMatrixOriginalDeckColumns.basis C B h ∘ ![a,b]) r) (conf 2) := by
  let z (i : Fin 2) : S.Tag := ⟨h,J r h (WilsonMatrixOriginalDeckColumns.basis C B h (![a,b] i))⟩
  intro x hx
  exact (((S.class_smooth (spectator F none) (spectate F none).smooth z).contDiffAt
    ((conf_open _).mem_nhds (Work.A05.smul_conf hr hx))).continuousAt.comp
    (continuousAt_id.const_smul r)).continuousWithinAt

theorem entry (L : PhysMS.Leading F J) (M : MS_Data G O) {h : ℕ} (a b : Glyph B h) (g : Test 2) (μ : ℝ) :
    Tendsto (fun r=>bank B F J h g r a b) Trace.Pilot.trail (𝓝 (MSSeparatedTestGram.matrix M h μ 0 g a b)) := by
  let v : MaxwellSlots C (fun _ : Fin 2=>h) := WilsonMatrixOriginalDeckColumns.basis C B h ∘ ![a,b]
  let f₀ (x : Points 2) := MSDeckProbeGram.raw M ![a,b] x μ 0
  have free : ContinuousOn (WickGoal (C:=C) v) (conf 2) := fun x hx=>(WickGoal_tied v hx).continuousAt.continuousWithinAt
  have native : ContinuousOn f₀ (conf 2) := free.congr fun x hx=>WilsonMatrixOriginalDeckColumns.free C B M ![a,b] x hx μ
  have A := WilsonMatrixOriginalDeckColumns.on_profile C B F J L M ![a,b] μ g.hasCompactSupport g.tsupport_subset
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := ∫ x,‖g x‖
  have ht : 0≤t := integral_nonneg fun _=>norm_nonneg _
  let δ := ε/(t+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  have exactPrice : t*δ<ε := calc
    _ < (t+1)*δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by dsimp [δ];field_simp
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp A δ hδ,RG17.positiveLength] with r priced rp
  let a₁ := PhysMS.measured F none (J r) v r
  change dist (g.applyTo a₁) (g.applyTo f₀)<ε
  rw [dist_eq_norm,←OPETreeTests.difference g a₁ f₀ (fun x hx => (regular B F J a b rp x (g.tsupport_subset hx)).continuousAt ((conf_open _).mem_nhds (g.tsupport_subset hx))) (fun x hx => (native x (g.tsupport_subset hx)).continuousAt ((conf_open _).mem_nhds (g.tsupport_subset hx)))]
  refine (OPETreeTests.bound g (a₁-f₀) δ ?_).trans_lt exactPrice
  intro x hx
  have p := priced x hx
  rw [dist_comm,dist_eq_norm] at p
  exact p.le

theorem original (L : PhysMS.Leading F J) (M : MS_Data G O) (h : ℕ) (g : Test 2) (μ : ℝ) :
    Tendsto (bank B F J h g) Trace.Pilot.trail (𝓝 (MSSeparatedTestGram.matrix M h μ 0 g)) :=
  tendsto_pi_nhds.mpr fun a=>tendsto_pi_nhds.mpr fun b=>entry B F J L M a b g μ

/-- An independently priced rich tree Gram buys the corresponding genuine
finite numerical two-field inverse, on the same profile. -/
theorem invertible (L : PhysMS.Leading F J) (M : MS_Data G O) (h : ℕ) (g : Test 2) (μ : ℝ)
    (live : IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) :
    (∀ᶠ r in Trace.Pilot.trail,IsUnit (bank B F J h g r)) ∧
      Tendsto (fun r=>(bank B F J h g r)⁻¹) Trace.Pilot.trail (𝓝 (MSSeparatedTestGram.matrix M h μ 0 g)⁻¹) := by
  let K := MSSeparatedTestGram.matrix M h μ 0 g
  have seen := original B F J L M h g μ
  have det : K.det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp live)
  have stable : ContinuousAt Inv.inv K := continuousAt_matrix_inv K (by rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ det)
  have dets := ((continuous_id.matrix_det).continuousAt (x:=K)).tendsto.comp seen
  refine ⟨?_,stable.tendsto.comp seen⟩
  filter_upwards [dets.eventually_ne det] with r nonzero
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nonzero)

end YM.Integration.WilsonMatrixOriginalDeckGram
