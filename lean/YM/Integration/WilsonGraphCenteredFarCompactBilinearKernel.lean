import YM.Integration.WilsonGraphCenteredFarCoefficientAtPorts
import YM.Integration.WilsonGraphCenteredFarSignedInsertion
import YM.Integration.WilsonGraphSeparatedRegularity

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCompactBilinearKernel
open Function PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphPublishedShapeEstimate WilsonGraphPreElectedShapeEstimates
open scoped BigOperators Classical
universe u
variable (g : GaugeGroup) (hg : g.IsSimple)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev S := _root_.IssuedBridge.PostedAppointedConversion.filed
  (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching (Teller.logNu 1)

/-- A single compact set fixes the entire filed kernel budget before the two arbitrary
occupied marks, the log distance, either heater, and the numerical transfer. -/
theorem onCompact (h p : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (safe : K ⊆ YM.conf 2) : ∃ D : ℝ, 0≤D ∧ ∀ (y : Spacetime) (hy : WithLp.toLp 2 ![0,y] ∈ K),
      AppointedSignedInsertion.budget (Z g hg) h p ⟨WithLp.toLp 2 ![0,y],safe hy⟩ ≤ D := by
  let marks (c : Fin 2 → Dime g.core h) := publicLetters (fun _ : Fin 2 => h)
    ![dime g.core h (c 0),dime g.core h (c 1)]
  choose d nonneg bound using fun (c : Fin 2 → Dime g.core h) (j : Fin (p+1)) =>
    WilsonGraphSeparatedRegularity.compactBound g (Q.{0} g hg).MS (S.{0} g hg) j.val (marks c) compact safe
  let w (c : Fin 2 → Dime g.core h) :=
    ‖AppointedBilinearPrice.readCoordinate h (c 0)‖*‖AppointedBilinearPrice.readCoordinate h (c 1)‖
  have w0 (c) : 0≤w c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨∑ c : Fin 2 → Dime g.core h,w c*∑ j : Fin (p+1),d c j,
    sum_nonneg (fun c _ => mul_nonneg (w0 c) (sum_nonneg (fun j _ => nonneg c j))),?_⟩
  intro y hy
  unfold AppointedSignedInsertion.budget
  apply sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (w0 c)
  unfold AppointedScalarOverflow.mass
  rw [←Fin.sum_univ_eq_sum_range (fun j : ℕ => ‖coeff j
    (Reg.Point.story (book (Z g hg) h 2 ⟨WithLp.toLp 2 ![0,y],safe hy⟩)
      (fun i => dime g.core h (c i)))‖)]
  apply sum_le_sum
  intro j _
  rw [AppointedCoefficientAtPorts.basis.{0} g hg h j.val y (safe hy) c]
  exact bound c j _ hy

end YM.FVA2.GradedFar.AppointedCompactBilinearKernel
