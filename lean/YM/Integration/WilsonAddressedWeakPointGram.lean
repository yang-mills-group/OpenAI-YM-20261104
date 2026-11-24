import YM.Integration.WilsonAddressedWeakPointCells
import YM.Integration.MSSeparatedSmearedTreeGram

/-! Stability of the signed physical weak detector sampled at genuine fine
sites. Its tolerance and mathematical test are fixed before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakPointGram
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Next.Rank Edition Baler Value Glyph Thirst Alarm
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonAddressedWeakPointCells
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) {B : Local.Physical.Deck G} {O : Booked B}
variable (M : MS_Data G O) {D : ℕ} {k N p : ℕ}

private theorem smooth (a b : Glyph B D) (μ : ℝ) :
    ContinuousOn (fun z : Points 2 => MSDeckProbeGram.raw M ![a,b] z μ 0) (conf 2) := by
  intro z hz
  have chart : Continuous (Fountain.metric (m:=2)) := by
    apply continuous_pi
    intro i
    exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2=>E4)).continuous)
  have legal : Injective (Fountain.metric z) := Theater.out.injective.comp hz
  exact ((Dial.contin M (labelAt B ∘ ![a,b]) (Fountain.metric z) legal Finset.univ 0 μ).1.comp
    chart.continuousAt).continuousWithinAt

variable (d : Fin 2 → ℕ) (live : k ≤ N)
variable (Y : Glyph B D → Glyph B D → PointSites R N p → (i : Fin 2) → Palette R.family (d i))
variable (U : Glyph B D → Glyph B D → PointSites R N p → (i : Fin 2) → Emblems R.family (d i))
variable (face : (Stock.census (Fin 2)).Mode)

def measured (φ : Test 2) (ρ : ℝ) : Matrix (Glyph B D) (Glyph B D) ℂ := fun a b =>
  matrixEntry R d live (Y a b) (U a b) φ ρ face

theorem tariff (φ : Test 2) (ρ μ δ : ℝ) (hδ : 0 ≤ δ)
    (actual : ∀ (a b : Glyph B D) (x : Points 2), φ x ≠ 0 →
      let o := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
      ‖reading R d o (Y a b o) (U a b o) live face - MSDeckProbeGram.raw M ![a,b] x μ 0‖ ≤ δ) :
    ∀ a b, ‖measured R d live Y U face φ ρ a b - MSSeparatedTestGram.matrix M D μ 0 φ a b‖ ≤
      (∫ x, ‖φ x‖) * δ := by
  intro a b
  exact WilsonAddressedWeakPointCells.charged R d live (Y a b) (U a b) φ ρ face _ δ hδ
    (φ.smearing (smooth M a b μ)) (actual a b)

theorem original (V : Warehouse G) (D : ℕ) (μ : ℝ) {v : E4} (away : (0:E4) ≠ v)
    (nearSet : Set (Points 2)) (near : nearSet ∈ 𝓝 (Extra.FD.couple 0 v))
    (ε : ℝ) (he : 0 < ε) :
    ∃ (φ : Test 2) (δ : ℝ), tsupport φ ⊆ nearSet ∧ (∫ x, φ x)=1 ∧ 0 < δ ∧
      let K := MSSeparatedTestGram.matrix M D μ 0 φ
      IsUnit K ∧ ∀ (d : Fin 2 → ℕ) (k N p : ℕ) (live : k ≤ N)
        (Y : Glyph B D → Glyph B D → PointSites R N p → (i : Fin 2) → Palette R.family (d i))
        (U : Glyph B D → Glyph B D → PointSites R N p → (i : Fin 2) → Emblems R.family (d i))
        (face : (Stock.census (Fin 2)).Mode) (ρ : ℝ),
        (∀ (a b : Glyph B D) (x : Points 2), φ x ≠ 0 →
          let o := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
          ‖reading R d o (Y a b o) (U a b o) live face - MSDeckProbeGram.raw M ![a,b] x μ 0‖ ≤ δ) →
        let A := measured R d live Y U face φ ρ
        IsUnit A ∧ ∀ a b, ‖A⁻¹ a b - K⁻¹ a b‖ < ε := by
  obtain ⟨φ,support,_,_,mass,good⟩ := MSSeparatedTestGram.localized V M D μ away nearSet near
  let ι := Glyph B D
  let assemble (s : (ι × ι) → ℂ) : Matrix ι ι ℂ := fun a b => s (a,b)
  let K := MSSeparatedTestGram.matrix M D μ 0 φ
  let z₀ : (ι × ι) → ℂ := fun t => K t.1 t.2
  have regular : Continuous assemble := continuous_matrix fun a b => continuous_apply (a,b)
  have det : (assemble z₀).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp good)
  have stable := regular.matrix_det.continuousAt (x:=z₀)
  have invert : ContinuousAt Inv.inv K :=
    continuousAt_matrix_inv K (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ det)
  have invs : ContinuousAt (fun s => (assemble s)⁻¹) z₀ :=
    invert.comp regular.continuousAt
  have entries : ∀ᶠ s in 𝓝 z₀, ∀ a b : ι, ‖(assemble s)⁻¹ a b - K⁻¹ a b‖ < ε := by
    apply Filter.eventually_all.mpr
    intro a
    apply Filter.eventually_all.mpr
    intro b
    have entry := (continuous_apply b).continuousAt.comp ((continuous_apply a).continuousAt.comp invs)
    have nearEntry : ∀ᶠ s in 𝓝 z₀, (assemble s)⁻¹ a b ∈ Metric.ball (K⁻¹ a b) ε :=
      entry.tendsto (Metric.ball_mem_nhds (K⁻¹ a b) he)
    filter_upwards [nearEntry] with s hs
    simpa only [Metric.mem_ball,dist_eq_norm] using hs
  obtain ⟨η,hη,within⟩ := Metric.mem_nhds_iff.mp ((stable.tendsto.eventually_ne det).and entries)
  let mass₁ : ℝ := ∫ x, ‖φ x‖
  have pos : 0 < max 1 mass₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ := (η/2)/(max 1 mass₁)
  have hδ : 0 < δ := div_pos (half_pos hη) pos
  refine ⟨φ,δ,support,mass,hδ,good,?_⟩
  intro grades k N p enough rows paths sector ρ actual
  let A := measured R grades enough rows paths sector φ ρ
  let s : (ι × ι) → ℂ := fun t => A t.1 t.2
  have paid : ∀ a b, ‖A a b - K a b‖ ≤ η/2 := by
    intro a b
    apply (tariff R M grades enough rows paths sector φ ρ μ δ hδ.le actual a b).trans
    calc mass₁ * δ ≤ max 1 mass₁ * δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      _ = η/2 := by dsimp only [δ]; field_simp
  have ball : s ∈ Metric.ball z₀ η := by
    rw [Metric.mem_ball,dist_eq_norm]
    exact lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (half_pos hη).le).mpr (fun j => paid j.1 j.2)) (half_lt_self hη)
  obtain ⟨admit,price⟩ := within ball
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr admit),price⟩

end YM.Integration.WilsonAddressedWeakPointGram
