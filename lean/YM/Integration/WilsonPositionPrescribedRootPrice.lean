import YM.Integration.WilsonPositionPrescribedFormalResidual
import YM.Integration.WilsonPositionPrescribedStability

/-! Quantitative identification of the nonlinear position calibration with
the genuine named MS formal root at arbitrary order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedRootPrice
open Function PowerSeries Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize FVA2 FVA2.Arrival MS MS.Land
open WilsonPositionPrescribedFormalTest WilsonPositionPrescribedTariff
open scoped Topology BigOperators Classical
variable {G : Gauge} (V : Store G) (ν : ℝ)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (d q : ℕ)

/-- The displayed coefficients are the authentic `Reg.State.root` on this
prescription, with their actual real signed coordinates, in every grade. -/
def native (t : ℝ) : MoveSpace G d :=
  ∑ i∈range q,t^(i+1) • guide G d (Reg.State.root ν V T d (i+1))

theorem published (t : ℝ) : guide G d (turn V ν T d q t) = native V ν T d q t := by
  simp only [turn,native,map_sum,map_smul]

private theorem tiny : Tendsto (native V ν T d q) (𝓝 0) (𝓝 0) := by
  have c : Continuous (native V ν T d q) := by unfold native; fun_prop
  have z : native V ν T d q 0=0 := by simp [native]
  simpa only [z] using c.tendsto 0

theorem normalized : ∃ C : ℝ,0≤C ∧ ∀ᶠ t : ℝ in 𝓝 0,
    ‖reading V ν T d q t - native V ν T d q t‖ ≤ C*|t|^(q+1) := by
  have htarget := (smooth V ν T d q).continuous.tendsto 0
  rw [anchored] at htarget
  obtain ⟨L,hL,fit⟩ := WilsonPositionPrescribedStability.residual (V.survey d) (V.prepared d)
    htarget (tiny V ν T d q)
  obtain ⟨C,hC,bills⟩ := WilsonPositionPrescribedFormalResidual.paid V ν T d q
  refine ⟨L*C,mul_nonneg hL hC,?_⟩
  filter_upwards [fit,Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with t h u
  have unit : |t|≤1 := by simpa [dist_eq_norm] using (Metric.mem_ball.mp u).le
  rw [←published] at h
  calc ‖reading V ν T d q t-native V ν T d q t‖ ≤ L*‖(V.survey d).itinerary
          (target V ν T d q t,guide G d (turn V ν T d q t))-(V.survey d).itinerary (V.survey d).opening‖ := by
            rw [←published]
            exact h
    _ ≤ L*(C*|t|^(q+1)) := mul_le_mul_of_nonneg_left (bills t unit) hL
    _ = (L*C)*|t|^(q+1) := (mul_assoc ..).symm

variable {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J : ℝ→PhysMS.tower S)

/-- True physical normalization at the exact selected screen, against the
independently named simultaneous formal root. The one unpaid invoice is the
signed raw physical test vector versus its specified MS kernel polynomial. -/
theorem physical (lead : PhysMS.Leading F J) {t : ℝ→ℝ} (small : Tendsto t Trace.Pilot.trail (𝓝 0)) :
    ∃ L A : ℝ,0≤L ∧ 0≤A ∧ ∀ᶠ r in Trace.Pilot.trail,
      ‖guide G d (WilsonPositionPrescribedScreen.correction F J V d r) - native V ν T d q (t r)‖
      ≤ L*‖(V.survey d).purse (WilsonPositionPrescribedScreen.hierarchy F J d r)-target V ν T d q (t r)‖
        + A*|t r|^(q+1) := by
  obtain ⟨L,hL,fit⟩ := evaluated V ν T d q F J lead small
  obtain ⟨A,hA,price⟩ := normalized V ν T d q
  refine ⟨L,A,hL,hA,?_⟩
  filter_upwards [fit,small.eventually price] with r h b
  calc _ ≤ ‖guide G d (WilsonPositionPrescribedScreen.correction F J V d r) - reading V ν T d q (t r)‖ +
        ‖reading V ν T d q (t r)-native V ν T d q (t r)‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (guide G d (WilsonPositionPrescribedScreen.correction F J V d r)) (reading V ν T d q (t r))
              (native V ν T d q (t r))
    _ ≤ _ := add_le_add h b

end YM.Integration.WilsonPositionPrescribedRootPrice

