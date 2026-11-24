import YM.Integration.FVA1Physical.Wilson.RawLedger

/-! The absolute coefficients of the first inherited FVA2 vacuum ticket are
the independently constructed RG02 vacuum Feynman coefficients. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Function Filter Set MeasureTheory RG Lattice YM.Wilson Tree Precision Marker
open FVA2.CityHistory FVA2.RayScatter FormalOPE.RG10.MultiGauge
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open PertExtension PertExtension.Series PertExtension.Series.Tested Comparison.RG02
open scoped Classical Topology ContDiff

private theorem trial_map {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : E →L[ℝ] H)
    {A : ℕ → E} {f : ℝ → E} {r : ℕ} (h : Laplace.Trial A f r) :
    Laplace.Trial (L ∘ A) (L ∘ f) r := by
  obtain ⟨C,hC,bound⟩ := h
  refine ⟨‖L‖*C,mul_nonneg (norm_nonneg _) hC,bound.mono fun g hg => ?_⟩
  change ‖L (f g) - peval (L ∘ A) r g‖ ≤ _
  rw [WilsonXLocal.eval_map L g,← map_sub]
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hg (norm_nonneg _)).trans_eq
    (mul_assoc ..).symm)

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} (W : Bulk.Colors R G f)

def rawWilson (u : Pins G c) (r i : ℕ) : ℝ :=
  (Laplace.detail (Bulk.Fk K F t W (axesP G c u) r) R.quiet i).re

variable (D : BudgetPoint) (hW : Bare.Witnessed W K) (Z : ChartRatio G)
    (hZ : LocalRatio Z) (h : Bid.Larger (G := G) S) (v : (Descent.nil (top := f)).Tags)
local notation "d₀" => Descent.nil (top := f)
include D hW hZ

/-- Absolute equality at every coarse ray, through any requested order.
The spatially constant terms are included. -/
theorem raw_ledger_coefficient (u : Pins G c) {i r : ℕ} (hi : i ≤ r) :
    rawWilson K F t W u r i = PowerSeries.coeff i
      (Stack.read u (μLedger (Descent.push S F d₀) Z (t,v) ⟨h,True.intro⟩ 1)) := by
  obtain ⟨P₀⟩ := Oven.builtafter S.patch
  obtain ⟨X,H,hX,cap⟩ := Spot.enough S F h P₀ u
  let A := Laplace.detail (Bulk.Fk K F t W (axesP G c u) r) R.quiet
  let Y (g : ℝ) := (Bare.realMoment K F W t (axesP G c u) g).part R.quiet
  let scale := rawScale K F t u
  let L : ℂ →L[ℝ] ℝ := scale • Complex.reCLM
  let B := μLedger (Descent.push S F d₀) Z (t,v) ⟨h,True.intro⟩ 1
  let s := basePower (gateQ S F t (retained d₀ v True.intro)) (useful S F d₀ v t h True.intro)
    u (Chart.tangent G F.Free) 1 * Stack.overhead Z F.Free
  have hRG : Laplace.Trial A Y r := (Bare.wilson_step_test K F W t (axesP G c u) r D hW).1 R.quiet
  have ray : (L ∘ Y) =ᶠ[Laplace.along] Fk.phaseAmt (Spool.lens (S := S) u X F) univ 1 := by
    filter_upwards [Tested.eventually_pos] with g hg
    change scale * ((Bare.realMoment K F W t (axesP G c u) g).part R.quiet).re = _
    rw [Bare.vacancy,Complex.ofReal_re,raw_phase_scalar K F t X u hg]
  have gift : Visible X (fun _ : Empty → G.Color => 1) (1 : Melody G F.Free) Fk.vacant 0 1 :=
    ⟨fun _ _ => RG.Envelope.const (1 : ℝ),fun _ _ _ => (abs_one (α := ℝ)).le,∅,
      by simp,fun j => Empty.elim j,fun _ _ _ _ _ => rfl⟩
  have hFk := Fk.aspirant hX hZ gift contDiffAt_const r
  have eqn (k : ℕ) (hk : k ≤ r) :
      scale * rawWilson K F t W u r k = s * PowerSeries.coeff k (Stack.read u B) := by
    have eq₁ := Laplace.trial_gap (Laplace.trial_congr ray (trial_map L hRG)) hFk k hk
    have eq₂ := congrArg (PowerSeries.coeff k) (first_ledger_birth S F Z t h v hZ u X H cap)
    change scale * rawWilson K F t W u r k = Fk.birth (Spool.lens (S:=S) u X F) Z k at eq₁
    exact eq₁.trans (by simpa only [firstLedger,PowerSeries.coeff_mk,PowerSeries.coeff_C_mul] using eq₂)
  have A₀ : rawWilson K F t W u r 0 = 1 := by
    unfold rawWilson
    rw [Laplace.tests_origin _ (Bulk.fk_unit ..),Complex.one_re]
  have B₀ : PowerSeries.coeff 0 (Stack.read u B) = 1 := by
    rw [Stack.reading_term,PowerSeries.coeff_zero_eq_constantCoeff_apply,
      show PowerSeries.constantCoeff B = 1 from marketZ _ Z _ _ _ hZ]
    rfl
  have eqScale : scale = s := by simpa only [A₀,B₀,mul_one] using eqn 0 (Nat.zero_le _)
  have hscale : 0 < scale := by
    apply mul_pos (Real.exp_pos _)
    exact mul_pos (mul_pos (Next.SectorChange.Gaussian.coat_pos (K.positive F t))
      (pow_pos K.ratio.scale _)) (Real.exp_pos _)
  exact mul_left_cancel₀ hscale.ne' (by simpa only [← eqScale] using eqn i hi)

end YM.Integration.FVA1Physical.Wilson
