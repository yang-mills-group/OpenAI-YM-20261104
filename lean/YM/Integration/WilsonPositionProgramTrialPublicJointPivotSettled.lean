import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRate
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotSalary

/-! The measured thermometer after paying only the two signed physical rows on one bounded inherited stock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotSettled
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


open WilsonPositionProgramTrialPublicJointPivotSalary (capital signedError)
open WilsonPositionProgramTrialPublicJointPivotThermometer (price)

variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    (hG : G.Simple) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))

theorem original (dial : Bool) :
    ∃ σ : Prescription (Press.portDeck G), ∃ H : Main.Match Z hG M σ dial,
      ∀ (ν : ℝ) (q : ℕ) {ι : Type} (u : Filter ι) (age g : ι → ℝ)
        (_ : Tendsto age u trail) (_ : Leading F J)
        (Q : ι → Prediction G 6) (T : ι → Change G 6)
        (_ : (Z.store.survey 6).Via Q (u:=u)) (_ : Tendsto (fun i => guide G 6 (T i)) u (𝓝 0))
        (e : ι → ℝ) (_ : ∀ᶠ i in u, 0 < g i ∧ g i ≤ 1)
        (_ : ∀ᶠ i in u, ∀ (rp : 0 < age i)
          (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) (Q i)))),
          signedError F J Z M H ν rp (Q i) (T i) q (g i) hq ≤ e i)
        (_ : Tendsto (fun i => e i / g i) u (𝓝 0)),
        Tendsto (fun i => WilsonPositionHomogeneousFrame.reading F J Z (age i)/g i) u (𝓝 1) := by
  obtain ⟨σ,H,rate⟩ := WilsonPositionProgramTrialPublicJointPivotRate.original F J Z hG M dial
  refine ⟨σ,H,fun ν q ι u age g limit lead Q T warm near e lives paid small => ?_⟩
  let C := capital Z M ν q
  have cp : 0 ≤ C := by
    apply add_nonneg zero_le_one
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  apply rate ν u age g limit lead Q T warm near (fun _=>q) (fun i=>C*e i) (lives.mono (fun _ h=>h.1)) _ _
  · filter_upwards [WilsonPositionProgramTrialPublicJointPivotSalary.original F J Z M H ν u Q T warm near,
      lives,paid] with i gate atG bought
    intro rp hq
    have size : |g i| ≤ 1 := by simpa only [abs_of_pos atG.1] using atG.2
    exact (gate rp hq q (g i) size).trans (mul_le_mul_of_nonneg_left (bought rp hq) cp)
  · simpa only [mul_div_assoc,mul_zero] using (tendsto_const_nhds (x:=C)).mul small

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotSettled
