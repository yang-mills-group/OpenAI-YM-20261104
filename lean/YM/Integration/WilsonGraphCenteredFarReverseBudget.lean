import YM.Integration.WilsonGraphCenteredFarEnteredRows
import YM.GradedFar.Growth.Chair
import YM.GradedFar.Continuation.First

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredReverse

open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff
open Continuation
open MS.Book.Program

section Formal

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))

def reverseSeries (h : ℕ) (s : ℝ) : Guard G h :=
  Reg.Point.stepV (GroupS.ψ N.criterion M (Teller.logNu 1) (-s)) (Kseries N M h s)

theorem reverseIdentity {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
    (H : Main.Match N simple M P true) (h : ℕ) (s : ℝ) :
    Kseries N M h (-s) * reverseSeries N M h s = 1 := by
  have key := (Growth.Lframe (d := h) N M H s (-s)).symm
  simpa only [reverseSeries, add_neg_cancel, neg_zero, neg_neg,
    Growth.zero_frame N M H h] using key

end Formal

open YangMills YM.Answer.ContinuumLimit YM.Integration

universe u

variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)

private abbrev prescription := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev pick := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)

def transfer (h : ℕ) (r f : ℝ) : Module.End ℂ (Sec g.core h) :=
  let H := ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg)
  ((H r h).trans (H f h).symm).toLinearMap

theorem returnField (h : ℕ) (r f : ℝ) :
    transfer.{u} g hg periods strict h r f * transfer.{u} g hg periods strict h f r = 1 := by
  ext1 a
  let H := ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg)
  change (H f h).symm ((H r h) ((H r h).symm ((H f h) a))) = a
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

theorem original (h k : ℕ) (r s : ℝ)
    (bound : ‖Growth.chairs g.core h (transfer.{u} g hg periods strict h r (r * Real.exp s))‖ ≤ 2) :
    let Z := prescription g hg
    let Q := WilsonGraphPaperPublication.perspective.{u} g hg
    let t := ElectedMeasurement.clock (pick.{u} g hg periods strict) Z r
    let f := r * Real.exp s
    let L := Growth.chairs g.core h (transfer.{u} g hg periods strict h r f)
    let A := Growth.chairs g.core h (transfer.{u} g hg periods strict h f r)
    let Aq := Growth.chairs g.core h (Continuation.atColumn (Kseries Z Q.MS h (-s)) k t)
    let Uq := Growth.chairs g.core h (Continuation.atColumn (reverseSeries Z Q.MS h s) k t)
    Kseries Z Q.MS h (-s) * reverseSeries Z Q.MS h s = 1 ∧
      ‖L - Uq‖ ≤ 2 * (‖A - Aq‖ * ‖Uq‖ + ‖Aq * Uq - 1‖) ∧
      (‖A - Aq‖ ≤ 1 / 4 → ‖L - Uq‖ ≤ 8 * ‖A - Aq‖ + 4 * ‖Aq * Uq - 1‖) := by
  intro Z Q t f L A Aq Uq
  have inv : L * A = 1 := by
    dsimp only [L, A]
    rw [← Growth.chairs_mul, returnField, Growth.chairs_one]
  have difference : L - Uq = L * (1 - A * Uq) := by
    rw [mul_sub, mul_one, ← mul_assoc, inv, one_mul]
  have split : 1 - A * Uq = (Aq - A) * Uq + (1 - Aq * Uq) := by
    rw [sub_mul]
    abel
  have bill : ‖1 - A * Uq‖ ≤ ‖A - Aq‖ * ‖Uq‖ + ‖Aq * Uq - 1‖ := by
    rw [split]
    calc
      _ ≤ ‖(Aq - A) * Uq‖ + ‖1 - Aq * Uq‖ := norm_add_le _ _
      _ ≤ ‖Aq - A‖ * ‖Uq‖ + ‖1 - Aq * Uq‖ := add_le_add (norm_mul_le _ _) le_rfl
      _ = _ := by rw [norm_sub_rev Aq A, norm_sub_rev 1 (Aq * Uq)]
  have raw : ‖L - Uq‖ ≤ 2 * (‖A - Aq‖ * ‖Uq‖ + ‖Aq * Uq - 1‖) := by
    rw [difference]
    exact (norm_mul_le L _).trans (mul_le_mul bound bill (norm_nonneg _) (by norm_num))
  refine ⟨reverseIdentity Z Q.MS Q.matching h s, raw, ?_⟩
  intro small
  have size : ‖Uq‖ ≤ 2 + ‖L - Uq‖ := by
    calc
      ‖Uq‖ = ‖L + (Uq - L)‖ := by congr 1; abel
      _ ≤ ‖L‖ + ‖Uq - L‖ := norm_add_le _ _
      _ ≤ 2 + ‖L - Uq‖ := by rw [norm_sub_rev Uq L]; exact add_le_add bound le_rfl
  have first := mul_le_mul_of_nonneg_left size (norm_nonneg (A - Aq))
  have second := mul_le_mul_of_nonneg_right small (norm_nonneg (L - Uq))
  nlinarith only [raw, first, second]

end YM.FVA2.GradedFar.AppointedCenteredReverse

