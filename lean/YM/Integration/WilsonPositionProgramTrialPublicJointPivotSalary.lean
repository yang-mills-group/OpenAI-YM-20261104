import YM.Integration.WilsonPositionProgramTrialPublicJointPivotThermometer
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotNorm
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotBudget

/-! The fixed-order cost of both signed original rows on the position screen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotSalary
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPhysicalNormalizedSignedMenu (Row offered docket retag)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionPrescribedScreen (hierarchy)
open WilsonPhysicalRosePositionFace (located predicted)
open WilsonPositionProgramTrialPublicJointPivotRose (Live tested)
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open FVA2.Scale.Jury (Thin fxt)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial


open WilsonPositionProgramTrialPublicJointPivotFitted (debit)
open WilsonPositionProgramTrialPublicJointPivotThermometer (price)

variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))


variable {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b) (ν : ℝ)

def physical {r : ℝ} (rp : 0 < r) : Row G 6 3 :=
  tested (Rose.test Z.criterion) (located F J r) (WilsonPositionProgramTrialPublicJointPivotLocated.live F J _ rp)

def model (Q : Prediction G 6) (T : Change G 6) (q : ℕ) (g : ℝ)
    (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) Q))) : Row G 6 3 :=
  WilsonPositionProgramTrialPublicJointPivotNorm.moved T
    (WilsonPositionProgramTrialPublicJointPivotFitted.undress ((Z.store.survey 6).firstPass (Z.store.prepared 6) Q) hq
      (WilsonPositionProgramTrialPublicJointPivotTarget.row Z M H ν 0 (q+1) g))

def determining (r : ℝ) (Q : Prediction G 6) (T : Change G 6) : ℝ :=
  let D := Z.store.survey 6
  ‖docket D (fun _:Unit => hierarchy F J 6 r) - docket D (retag (fun _:Unit=>T) (fun _:Unit=>Q))‖

def signedError {r : ℝ} (rp : 0 < r) (Q : Prediction G 6) (T : Change G 6) (q : ℕ) (g : ℝ)
    (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) Q))) : ℝ :=
  max ‖rows (physical F J Z rp) - rows (model Z M H ν Q T q g hq)‖ (determining F J Z r Q T)

def capital (q : ℕ) : ℝ := 1 + 3 * WilsonPositionProgramTrialPublicJointPivotBudget.fee Z M ν 0 (q+1)

theorem original {ι : Type} (u : Filter ι) (Q : ι → Prediction G 6) (T : ι → Change G 6)
    (ready : (Z.store.survey 6).Via Q (u:=u)) (near : Tendsto (fun i => guide G 6 (T i)) u (𝓝 0)) :
    ∀ᶠ i in u, ∀ {r : ℝ} (rp : 0 < r)
      (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) (Q i))))
      (q : ℕ) (g : ℝ) (_ : |g| ≤ 1), price F J Z M H ν rp (Q i) (T i) q g hq ≤
        capital Z M ν q * signedError F J Z M H ν rp (Q i) (T i) q g hq := by
  filter_upwards [WilsonPositionProgramTrialPublicJointPivotNorm.original (n:=3) u Z.store Q T ready near]
    with i estimate r rp hq q g hg
  let D := determining F J Z r (Q i) (T i)
  let B := WilsonPositionProgramTrialPublicJointPivotBudget.fee Z M ν 0 (q+1)
  let V := model Z M H ν (Q i) (T i) q g hq
  let E := ‖rows (physical F J Z rp) - rows V‖
  have b := WilsonPositionProgramTrialPublicJointPivotBudget.original Z M H ν 0 (q+1) (g:ℂ) (by simpa using hg)
  have bound : ‖rows V‖ ≤ 3*B := (estimate _ hq).trans (mul_le_mul_of_nonneg_left b (by norm_num))
  have dp : 0 ≤ D := norm_nonneg _
  change E + D*‖rows V‖ ≤ (1+3*B)*max E D
  calc
    E + D*‖rows V‖ ≤ max E D + max E D * (3*B) :=
      add_le_add (le_max_left _ _) (mul_le_mul (le_max_right _ _) bound (norm_nonneg _) (dp.trans (le_max_right _ _)))
    _ = _ := by ring

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotSalary

