import YM.Integration.WilsonGraphCenteredFarBilinearCauchy
import YM.Integration.WilsonGraphCenteredFarScalarOverflow

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedBilinearPrice

open Function Filter Real PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
  (H : Main.Match N simple M P true)

/-- A literal coordinate of a filed mark, expressed as a continuous functional on the
same chart used to price the operator series. -/
def readCoordinate (h : ℕ) (b : Dime G h) : RowSpace G h →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (((dime G h).coord b).comp (chair G h).symm.toLinearMap)

private theorem coordinate (h : ℕ) (b : Dime G h) (w : Sec G h) :
    readCoordinate h b (chair G h w) = (dime G h).repr w b := by
  change (dime G h).repr ((chair G h).symm (chair G h w)) b = _
  rw [LinearEquiv.symm_apply_apply]

/-- The truncation mass of a filed coordinate is controlled by the mass of the very
same matrix in the actual coordinate chart. -/
theorem fieldMass (p h : ℕ) (A : Guard G h) (u : Sec G h) (b : Dime G h) :
    AppointedScalarOverflow.mass p (tax A u b) ≤
      (‖readCoordinate h b‖ * ‖chair G h u‖) *
        Appointed220.Eval.mass p (Appointed220.Zones.liftSeries (AppointedCenteredSeriesPrice.coordinateChart G h) A) := by
  unfold AppointedScalarOverflow.mass Appointed220.Eval.mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have slot := (readCoordinate h b).le_opNorm (chair G h ((coeff j A) u))
  rw [coordinate, ←appointed] at slot
  have field := (chairs G h (coeff j A)).le_opNorm (chair G h u)
  rw [tax, coeff_mk]
  change _ ≤ (‖readCoordinate h b‖ * ‖chair G h u‖) *
    ‖coeff j (PowerSeries.map (AppointedCenteredSeriesPrice.coordinateChart G h).toRingHom A)‖
  rw [PowerSeries.coeff_map]
  exact slot.trans ((mul_le_mul_of_nonneg_left field (norm_nonneg _)).trans_eq (by change _ = _ * ‖chairs G h (coeff j A)‖; ring))

/-- The same finite kernel table is evaluated at the current far heater. -/
def separatedCrops (h p : ℕ) (x : Scale.Stage 2) (A B : Guard G h) (u v : Sec G h) (t : ℝ) : ℂ :=
  ∑ c : Fin 2 → Dime G h, crop p t (tax A u (c 0)) * crop p t (tax B v (c 1)) *
    crop p t (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i)))

private theorem cropSum {I : Type} [Fintype I] (p : ℕ) (t : ℝ) (F : I → PowerSeries ℂ) :
    crop p t (∑ i, F i) = ∑ i, crop p t (F i) := by
  exact YM.FVA2.GradedFar.crop_sum p t Finset.univ F

/-- The independently evaluated fields and kernel have an exact bilinear crop price
at the two occupied positions, on every nominated degree and choice of filed fields. -/
theorem expense (h p : ℕ) (x : Scale.Stage 2) (A B : Guard G h) (u v : Sec G h)
    (t : ℝ) (ht : |t| ≤ 1) :
    ‖separatedCrops N h p x A B u v t - crop p t (AppointedBilinearCauchy.full N h x A B u v)‖ ≤
      2 * |t|^(p+1) * ∑ c : Fin 2 → Dime G h,
        AppointedScalarOverflow.mass p (tax A u (c 0)) *
        AppointedScalarOverflow.mass p (tax B v (c 1)) *
        AppointedScalarOverflow.mass p (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i))) := by
  unfold separatedCrops AppointedBilinearCauchy.full
  rw [cropSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ =>
    AppointedScalarOverflow.threePrice p t (tax A u (c 0)) (tax B v (c 1))
      (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i))) ht)

include H in
theorem fixedField (h p : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ a : ℕ, ∀ s : ℝ, 0 ≤ s → ∀ (u : Sec G h) (b : Dime G h),
      AppointedScalarOverflow.mass p (tax (Kseries N M h s) u b) ≤
        (‖readCoordinate h b‖ * ‖chair G h u‖) * (D * (1+s)^a) := by
  obtain ⟨D,hD,a,estimate⟩ := AppointedFarHeater.size N M H h p
  refine ⟨D,hD,a,fun s hs u b => (fieldMass p h _ u b).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (estimate s hs) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end YM.FVA2.GradedFar.AppointedBilinearPrice
