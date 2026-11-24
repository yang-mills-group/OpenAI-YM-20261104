import YM.Integration.WilsonGraphCenteredFarTwoClocks
import YM.GradedFar.Continuation.Insert

set_option autoImplicit false
set_option maxHeartbeats 900000
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

def center (y : Points 1) (hy : outgoing y ∈ conf 2) : Scale.Stage 2 := ⟨outgoing y,hy⟩

theorem location (y : Points 1) (hy : outgoing y ∈ conf 2) (s : ℝ) :
    (Facets.posing (-s) (center y hy)).val = outgoing (squeeze (-s) y) := by
  apply congrArg (WithLp.toLp 2)
  funext i
  fin_cases i
  · change Real.exp (- -s) • (0 : E4) = 0
    exact smul_zero _ 
  · rfl

theorem restore (x : Scale.Stage 2) (s : ℝ) :
    Facets.posing s (Facets.posing (-s) x) = x := by
  rw [Facets.at_pose, add_neg_cancel]
  apply Subtype.ext
  change Real.exp (- (0 : ℝ)) • x.val = x.val
  simp

include H in
/-- The two reverse fields return to the original #309 (1,1) all-near forecast at the same common cap. -/
theorem allNear (h : ℕ) (y : Points 1) (hy : outgoing y ∈ conf 2) (s : ℝ) (u v : Sec G h) :
    AppointedTwoClocks.pulled N h (center y hy) (ψ (-s))
      (AppointedCenteredReverse.reverseSeries N M h s) (AppointedCenteredReverse.reverseSeries N M h s) u v =
      Continuation.row N (d := fun _ : Fin 1 => h) (e := fun _ : Fin 1 => h)
        (0 : Points 1) (fun _ => u) y (fun _ => v) s := by
  let x := Facets.posing (-s) (center y hy)
  have hx : x.val = outgoing (squeeze (-s) y) := location y hy s
  have hp : outgoing (squeeze (-s) y) ∈ conf 2 := hx ▸ x.property
  have he : x = ⟨outgoing (squeeze (-s) y),hp⟩ := Subtype.ext hx
  have paid := AppointedTwoClocks.original N M H h x s u v
  rw [show Facets.posing s x = center y hy from restore _ _] at paid
  refine paid.trans ?_
  refine PowerSeries.ext fun j => ?_
  rw [Reg.Point.story, coeff_mk, Continuation.coeff_row (ℓ := h) H _ _ _ _ _
    (fun _ => le_rfl) (fun _ => le_rfl) hp j, he]
  apply congrArg (Measure.outlook N.scheme N.criterion h 2 ⟨outgoing (squeeze (-s) y),hp⟩ j)
  funext i
  fin_cases i <;> rfl

end YM.FVA2.GradedFar.AppointedOriginalOperand
