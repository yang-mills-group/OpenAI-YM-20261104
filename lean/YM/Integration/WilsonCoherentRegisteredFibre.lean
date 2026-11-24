import YM.Integration.WilsonCoherentRegisteredCut
import YM.Integration.WilsonCoherentPivotContinuity
import YM.Integration.WilsonIncidentChartTaylorRate

/-! Signed price on the true angular chart with all original compact pivots
and the complete integrable exterior in one measure. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentRegisteredFibre
open Function Filter Finset Set Lattice Wilson RG Tree RG16 Precision PertExtension Metric MeasureTheory
open PhysicalNext.Repeat.Legato OPE.Therm MSbar.Heath Pert.Asymptotics
open WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction
open WilsonCoherentReportingForest
open scoped Classical Topology

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] (d : I→ℕ)

theorem purchased (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (p : ℕ) {ε : ℝ} (he : 0<ε) : ∀ᶠ m : ℕ in atTop,
    ∀N,m<N → ∀per (o : I→Site (R.family.side (m+1) per))
    (T : Forest (R.family.path.levels.clock.op m per).ratio),
    let B := incident R T d o
    let E := moving T B
    let θ := (R.family.path.rep N per (m+1)).p.threshold
    ∀ (y : ∀i,R.family.label (d i)) (c : ℂ) (χ : ℂ→L[ℝ]ℝ)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (s : Set Ω), MeasurableSet s →
    ∀(v : Ω → ({i:T.Free|i∉E}:Set T.Free) → G.El) (X : Ω → ↥E → G.Color),
    let U := fun a => restored T B (v a) (Chart.expLinks G (↥E) (X a))
    (∀a∈s, X a∈ball 0 r ∧ U a∈cold R m per d o) →
    ∀ H : Ω→ℝ, IntegrableOn H s μ →
      ‖∫ a in s, H a *
        (χ (c*∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) (U a)) -
          χ (c*WilsonCoherentReportingPivot.row R d θ y o (restored T B (v a) 1) (drift T B (X a)) p 1)) ∂μ‖ ≤
        (‖χ‖*‖c‖*WilsonCoherentReportingPivot.mass R d θ y*(ε*regulatorRun R.family N per (m+1)^p)) *
          ∫ a in s,‖H a‖ ∂μ := by
  obtain ⟨C,pos,receipt⟩ := WilsonCoherentRegisteredCut.purchased R d simple p
  filter_upwards [receipt,WilsonIncidentChartTaylorRate.purchased R simple slow J clear P pr sr d p C pos he]
    with m mark price N live per o T
  dsimp only
  intro y c χ Ω inst μ s hs v X att H hH
  let B:=incident R T d o
  let E:=moving T B
  let θ:=(R.family.path.rep N per (m+1)).p.threshold
  let g:=regulatorRun R.family N per (m+1)
  have m0 : 0≤WilsonCoherentReportingPivot.mass R d θ y:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  rw [←integral_const_mul]
  apply norm_integral_le_of_norm_le (hH.norm.const_mul _)
  filter_upwards [ae_restrict_mem hs] with a ha
  have ⟨ball,cold⟩:=att a ha
  have ⟨small,hot⟩ := price N per live o T (v a) (X a) ball cold
  have main := (mark N live per o T (v a) (X a) small cold y).trans
    (mul_le_mul_of_nonneg_left hot m0)
  rw [norm_mul,mul_comm (‖H a‖),←map_sub,←mul_sub]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [mul_assoc (‖χ‖*‖c‖)]
  apply (χ.le_opNorm _).trans
  rw [norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left main (norm_nonneg _)) (norm_nonneg _)

end YM.Integration.WilsonCoherentRegisteredFibre
