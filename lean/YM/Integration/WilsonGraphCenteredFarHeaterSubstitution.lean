import YM.Integration.WilsonGraphCenteredFarSeriesPrice
import YM.GradedFar.Growth.Relay

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedFarHeater

open Filter Real PowerSeries Growth Continuation
open Register MS MS.Book MS.Land Scale
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Jury
open MS.Native MS.Book MS.Menus MS.Tide MS.Book.Program
open scoped Topology Classical BigOperators

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
  {P : MS.Land.Prescription (Press.portDeck G)} (matchData : Main.Match N simple M P true)

include matchData

/-- Changing to the actual far heater spends the measured heater difference and the
finite Cauchy-substitution expense for the complete reverse column. -/
theorem crop (h k : ℕ) (s t v : ℝ) (ht : |t| ≤ 1) (hv : |v| ≤ 1)
    (hw : ‖bend N M s k (t:ℂ)‖ ≤ 1) :
    let chart := AppointedCenteredSeriesPrice.coordinateChart G h
    let A := Appointed220.Zones.liftSeries chart (Kseries N M h s)
    let ψ := GroupS.ψ N.criterion M (Teller.logNu 1) (-s)
    let F := max 1 (Appointed220.Eval.mass k ψ)
    ‖chairs G h (atColumn (Kseries N M h s) k v) -
      chairs G h (atColumn (AppointedCenteredReverse.reverseSeries N M h s) k t)‖ ≤
      Appointed220.Eval.mass k A * ((k:ℝ)*‖(v:ℂ)-bend N M s k (t:ℂ)‖) +
        ((k:ℝ)*F^k) * Appointed220.Eval.mass k A * |t|^(k+1) := by
  intro chart A ψ F
  let w := Appointed220.Eval.value k ψ (t:ℂ)
  have castT : ‖(t:ℂ)‖ = |t| := by rw [Complex.norm_real,Real.norm_eq_abs]
  have castV : ‖(v:ℂ)‖ = |v| := by rw [Complex.norm_real,Real.norm_eq_abs]
  have entered : bend N M s k (t:ℂ) = w := rfl
  have root := ((matchData.dilation (Teller.logNu 1)).check.led (-s)).start
  have record : Appointed220.Zones.liftSeries chart (AppointedCenteredReverse.reverseSeries N M h s) =
      Appointed220.Eval.recompose A ψ := Appointed220.Zones.pulled chart (Kseries N M h s) ψ
  have change := Appointed220.Eval.lipschitz A k (v:ℂ) w (castV.trans_le hv) (entered ▸ hw)
  have overflow := Appointed220.Eval.payCompose A ψ k (t:ℂ) root (castT.trans_le ht)
    (le_max_left (1:ℝ) (Appointed220.Eval.mass k ψ)) (le_max_right (1:ℝ) (Appointed220.Eval.mass k ψ))
  rw [← AppointedCenteredSeriesPrice.evaluated, ← AppointedCenteredSeriesPrice.evaluated,record]
  calc ‖Appointed220.Eval.value k A (v:ℂ) - Appointed220.Eval.value k (Appointed220.Eval.recompose A ψ) (t:ℂ)‖ ≤
      ‖Appointed220.Eval.value k A (v:ℂ) - Appointed220.Eval.value k A w‖ +
        ‖Appointed220.Eval.value k A w - Appointed220.Eval.value k (Appointed220.Eval.recompose A ψ) (t:ℂ)‖ :=
      by simpa only [dist_eq_norm] using (dist_triangle (Appointed220.Eval.value k A (v:ℂ)) (Appointed220.Eval.value k A w) (Appointed220.Eval.value k (Appointed220.Eval.recompose A ψ) (t:ℂ)))
    _ ≤ _ := by rw [entered]; exact add_le_add change (by simpa only [castT] using overflow)

/-- At positive log distance the returning column costs only a polynomial in that
logarithm. The distance, crop and appointed scale law stay on the same series. -/
theorem size (h k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ a : ℕ, ∀ s ≥ 0,
      Appointed220.Eval.mass k (Appointed220.Zones.liftSeries (AppointedCenteredSeriesPrice.coordinateChart G h)
        (Kseries N M h s)) ≤ D*(1+s)^a := by
  obtain ⟨D,hD,a,fee⟩ := Appointed220.Zones.pricePrint (matchData.dilation (Teller.logNu 1)).check
    (AppointedCenteredSeriesPrice.coordinateChart G h) k
  refine ⟨D,hD,a,fun s hs => ?_⟩
  have upper : exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  simpa only [Appointed220.Zones.carry, Appointed220.transfer, Kseries, max_eq_left upper, one_pow, mul_one, abs_of_nonneg hs] using fee s

end YM.FVA2.GradedFar.AppointedFarHeater

