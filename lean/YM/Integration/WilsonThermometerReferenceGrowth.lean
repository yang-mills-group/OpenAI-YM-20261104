import YM.Integration.WilsonThermometerReferenceStation
import YM.Integration.WilsonPositionOriginalDiagnosticCorridor
import YM.Next.RANK.StationMeter

/-! The reference-label fee is subexponential in the actual physical inverse-radius clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerReferenceGrowth
open Function Set Filter Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open scoped BigOperators Classical Topology
open private exp_bills from YM.Next.RANK.StationMeter
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}

theorem original (simple : G.Simple) (construction : C.Makes) (d : ℕ) (η : ℝ) (positive : 0<η) :
    ∀ᶠ k in atTop, ∀ {D : ℕ} (V : Vane C D) (j : Fin (D+1)), j.val=d → V.k=k →
      V.checked f H D → ∀ (w : (Bel C.book).Field j) (N p : ℕ), k<N →
      (C.labels.level j).coeffSize (V.wheel.atCut (N,p) j w) ≤
        Real.exp (η * (-Real.log V.wheel.r)) * (WilsonPositionThermometerStationNorm.cost C d * ‖w‖) := by
  let A := C.path.levels
  have quarter : 0<η/4 := by positivity
  filter_upwards [WilsonThermometerReferenceStation.cutoff (f:=f) (H:=H) simple construction d _ quarter,
    Work.D01.columnLogs_le A _ quarter,exp_bills A 1,
    WilsonPositionOriginalDiagnosticCorridor.upper A simple (show 0<(1/2:ℝ) by norm_num)]
    with k get columns currency upper D V j rank seat checked w N p top
  subst k
  have βpos : 0<A.clock.hatBeta V.k := zero_lt_one.trans (A.fits.delayed V.k)
  have βlog : Real.log (A.clock.hatBeta V.k) ≤ C.S.scale V.k := by
    have cap : A.clock.hatBeta V.k ≤ Real.exp (C.S.scale V.k) := by simpa only [one_mul] using currency
    simpa only [Real.log_exp] using Real.log_le_log βpos cap
  have magpos : 0<Next.Rank.Station.mag A V.b V.k := Next.Rank.Station.mag_pos ..
  have ml := Real.log_le_log magpos (upper V.b checked.high.2)
  rw [Real.log_rpow βpos] at ml
  have radial : C.S.scale V.k ≤ 2 * (-Real.log V.wheel.r) := by
    change C.S.scale V.k ≤ 2 * (-Real.log (C.S.a V.k * Next.Rank.Station.mag A V.b V.k))
    rw [Real.log_mul (C.S.a_pos V.k).ne' magpos.ne']
    have hs : C.S.scale V.k = -Real.log (C.S.a V.k) := Real.log_inv _
    linarith only [hs,ml,βlog]
  have price :
      Real.exp (Work.D01.columnLogs A V.k) * (A.clock.hatBeta V.k)^(η/4) ≤
        Real.exp (η * (-Real.log V.wheel.r)) := by
    rw [Real.rpow_def_of_pos βpos,←Real.exp_add,Real.exp_le_exp]
    nlinarith only [columns,mul_le_mul_of_nonneg_right βlog quarter.le,
      mul_le_mul_of_nonneg_left radial (half_pos positive).le]
  calc
    _ ≤ _ := get V j rank rfl checked w N p top
    _ = (Real.exp (Work.D01.columnLogs A V.k) * (A.clock.hatBeta V.k)^(η/4)) *
          (WilsonPositionThermometerStationNorm.cost C d * ‖w‖) := (mul_assoc ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right price (by unfold WilsonPositionThermometerStationNorm.cost; positivity)

end YM.Integration.WilsonThermometerReferenceGrowth
