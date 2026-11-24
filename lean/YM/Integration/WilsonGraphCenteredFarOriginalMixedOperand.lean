import YM.Integration.WilsonGraphCenteredFarOriginalAllNear
import YM.Integration.WilsonGraphCenteredFarExteriorAtOrigin
import YM.Integration.WilsonGraphCenteredFarSingleExteriorCoefficient
import YM.GradedFar.FormalSecond

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOriginalOperand

open Function Filter Real PowerSeries Finset Continuation
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
  (H : Main.Match N simple M P true)
local notation "ψ" => GroupS.ψ N.criterion M (Teller.logNu 1)

include H in
/-- The one-reversed formal row is the original #309 `Dx` with its complete spectator series at the same cap. -/
theorem mixed (h : ℕ) (y : Points 1) (hy : outgoing y ∈ conf 2) (s : ℝ) (u v : Sec G h) :
    AppointedTwoClocks.pulled N h (center y hy) (ψ (-s))
      (AppointedCenteredReverse.reverseSeries N M h s) 1 u v =
      Dx N M (e := fun _ : Fin 1 => h) y (fun _ => v) s u := by
  let x := Facets.posing (-s) (center y hy)
  have hx : x.val = outgoing (squeeze (-s) y) := location y hy s
  have hp : outgoing (squeeze (-s) y) ∈ conf 2 := hx ▸ x.property
  have he : x = ⟨outgoing (squeeze (-s) y),hp⟩ := Subtype.ext hx
  rw [AppointedExteriorAtOrigin.mixed N M H]
  refine PowerSeries.ext fun j => ?_
  rw [AppointedExteriorAtOrigin.coefficient, Dx_configuration (ℓ := h) H (fun _ : Fin 1 => h) h u y
    (fun _ : Fin 1 => v) s le_rfl (fun _ => le_rfl) hp j]
  change (∑ D ∈ tally j 1, book N h 2 x (D none) ![u,(coeff (D (some 0)) (Kseries N M h (-s))) v]) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro D _
  apply congrArg (Measure.outlook N.scheme N.criterion h 2 ⟨outgoing (squeeze (-s) y),hp⟩ (D none))
  funext i
  fin_cases i
  · rfl
  · exact Kfactor (N := N) (T := M) (-s) v

include H in
/-- Both original #309 scalar forecasts at every crop and every real near heat on the same filed marks. -/
theorem atHeat (h p : ℕ) (y : Points 1) (hy : outgoing y ∈ conf 2) (s t : ℝ) (u v : Sec G h) :
    crop p t (AppointedTwoClocks.pulled N h (center y hy) (ψ (-s))
      (AppointedCenteredReverse.reverseSeries N M h s) (AppointedCenteredReverse.reverseSeries N M h s) u v) =
      crop p t (Continuation.row N (d := fun _ : Fin 1 => h) (e := fun _ : Fin 1 => h)
        (0 : Points 1) (fun _ => u) y (fun _ => v) s) ∧
    crop p t (AppointedTwoClocks.pulled N h (center y hy) (ψ (-s))
      (AppointedCenteredReverse.reverseSeries N M h s) 1 u v) =
      crop p t (Dx N M (e := fun _ : Fin 1 => h) y (fun _ => v) s u) := by
  exact ⟨congrArg (crop p t) (allNear N M H h y hy s u v),
    congrArg (crop p t) (mixed N M H h y hy s u v)⟩

end YM.FVA2.GradedFar.AppointedOriginalOperand
