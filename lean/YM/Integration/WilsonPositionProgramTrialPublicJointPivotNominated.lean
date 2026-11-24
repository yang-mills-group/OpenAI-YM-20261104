import YM.Integration.WilsonPositionProgramTrialPublicJointPivotSettled
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotPrepositioned

/-! The original positioned thermometer against its elected, independently normalized finite polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotNominated
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

open WilsonPositionProgramTrialPublicJointPivotNorm (moved)
open WilsonPositionProgramTrialPublicJointPivotFitted (undress)
open WilsonPositionProgramTrialPublicJointPivotSalary (physical determining signedError)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionProgramTrialPublicJointPivotTarget (row)

def cost {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b)
    (ν : ℝ) {r : ℝ} (rp : 0<r) (T : Change G 6) (k q : ℕ) (g : ℝ) : ℝ :=
  max ‖rows (physical F J Z rp) - rows (moved T (row Z M H ν 0 (q+1) g))‖
    (determining F J Z r (forecast Z M ν 6 k g) T)

theorem identity (T : Change G 6) (ht : Bijective (stand T)) (none : T=0) (A : Row G 6 3) :
    undress T ht A = A := by
  subst T
  ext1 p
  simpa only [stand0,Module.End.one_apply] using WilsonPositionProgramTrialPublicJointPivotFitted.named (0:Change G 6) ht A p

theorem charged {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b)
    (ν : ℝ) {r : ℝ} (rp : 0<r) (T : Change G 6) (k q : ℕ) (g : ℝ)
    (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) (forecast Z M ν 6 k g))))
    (steady : (Z.store.survey 6).firstPass (Z.store.prepared 6) (forecast Z M ν 6 k g) = 0) :
    signedError F J Z M H ν rp (forecast Z M ν 6 k g) T q g hq = cost F J Z hG M H ν rp T k q g := by
  unfold signedError WilsonPositionProgramTrialPublicJointPivotSalary.model cost
  rw [identity _ hq steady]

theorem original (dial : Bool) :
    ∃ σ : Prescription (Press.portDeck G), ∃ H : Main.Match Z hG M σ dial,
      ∀ (ν : ℝ) (k q : ℕ) {ι : Type} (u : Filter ι) (age g : ι → ℝ)
        (_ : Tendsto age u trail) (_ : Leading F J) (_ : Tendsto g u (𝓝 0))
        (T : ι → Change G 6) (_ : Tendsto (fun i => guide G 6 (T i)) u (𝓝 0))
        (e : ι → ℝ) (_ : ∀ᶠ i in u, 0 < g i)
        (_ : ∀ᶠ i in u, ∀ (rp : 0 < age i), cost F J Z hG M H ν rp (T i) k q (g i) ≤ e i)
        (_ : Tendsto (fun i => e i/g i) u (𝓝 0)),
        Tendsto (fun i => WilsonPositionHomogeneousFrame.reading F J Z (age i)/g i) u (𝓝 1) := by
  obtain ⟨σ,H,settle⟩ := WilsonPositionProgramTrialPublicJointPivotSettled.original F J Z hG M dial
  refine ⟨σ,H,fun ν k q ι u age g limit lead cold T near e positive paid small => ?_⟩
  let Q (i : ι) := forecast Z M ν 6 k (g i)
  have warm := WilsonPositionProgramTrialPublicJointPivotForecast.original Z M H ν u 6 k g cold
  have prepared := WilsonPositionProgramTrialPublicJointPivotPrepositioned.original Z M H ν u 6 k g cold
  have lives : ∀ᶠ i in u, 0 < g i ∧ g i ≤ 1 :=
    positive.and (((tendsto_order.mp cold).2 _ zero_lt_one).mono fun _ h => h.le)
  apply settle ν q u age g limit lead Q T warm near e lives _ small
  filter_upwards [prepared,paid] with i positioned earned
  intro rp hq
  rw [charged F J Z hG M H ν rp (T i) k q (g i) hq positioned]
  exact earned rp

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotNominated
