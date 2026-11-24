import YM.Integration.WilsonPositionProgramTrialPublicJointPivotFitted
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotTarget
import YM.Integration.WilsonPositionScaleLawThermometerOrigin

/-! The prescribed compact thermometer at the origin of the common position gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotThermometer
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
open WilsonPositionProgramTrialPublicJointPivotTarget (row)
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b) (ν : ℝ)

theorem value (q : ℕ) (g : ℝ) :
    (row Z M H ν 0 (q+1) g (Rose.tag G)).re = Rose.cT Z.criterion.cut G Z.criterion.image*g := by
  rw [WilsonPositionProgramTrialPublicJointPivotTarget.original,WilsonPositionScaleLawThermometerOrigin.clock Z M H ν,
    WilsonPositionScaleLawThermometerOrigin.initial,←Complex.ofReal_mul,Complex.ofReal_re]

def price {r : ℝ} (rp : 0 < r) (Q : Prediction G 6) (T : Change G 6) (q : ℕ) (g : ℝ)
    (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) Q))) : ℝ :=
  debit F J Z rp Q T (row Z M H ν 0 (q+1) g) hq

theorem original {ι : Type*} (u : Filter ι) (age : ι → ℝ) (near : Tendsto age u trail)
    (lead : Leading F J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ι → Prediction G 6) (T : ι → Change G 6)
      (_ : (Z.store.survey 6).Via Q (u:=u)) (_ : Tendsto (fun i => guide G 6 (T i)) u (𝓝 0)),
      ∀ᶠ i in u, ∀ (rp : 0 < age i)
        (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) (Q i))))
        (q : ℕ) (g : ℝ) (_ : 0 < g),
        |WilsonPositionHomogeneousFrame.reading F J Z (age i) / g - 1| ≤
          C * price F J Z M H ν rp (Q i) (T i) q g hq / |Rose.cT Z.criterion.cut G Z.criterion.image| / g := by
  obtain ⟨C,cp,issued⟩ := WilsonPositionProgramTrialPublicJointPivotFitted.original F J Z u age near lead
  refine ⟨C,cp,fun Q T ready nearId => ?_⟩
  filter_upwards [issued Q T ready nearId] with i paid rp hq q g gp
  have h := paid rp (row Z M H ν 0 (q+1) g) hq
  rw [value,←mul_sub,abs_mul] at h
  have hc : 0 < |Rose.cT Z.criterion.cut G Z.criterion.image| := abs_pos.mpr Z.criterion.fresh.ne
  have cleared : WilsonPositionHomogeneousFrame.reading F J Z (age i)/g - 1 =
      (WilsonPositionHomogeneousFrame.reading F J Z (age i)-g)/g := by field_simp [gp.ne']
  rw [cleared,abs_div,abs_of_pos gp]
  apply div_le_div_of_nonneg_right _ gp.le
  apply (le_div_iff₀ hc).2
  rwa [mul_comm]

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotThermometer
