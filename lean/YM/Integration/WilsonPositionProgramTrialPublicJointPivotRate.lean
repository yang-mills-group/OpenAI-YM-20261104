import YM.Integration.WilsonPositionProgramTrialPublicJointPivotThermometer

/-! The common before-experiment prescription, and the first positioned thermometer for a paid signed stock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotRate
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
    (hG : G.Simple) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))

theorem original (dial : Bool) :
    ∃ σ : Prescription (Press.portDeck G), ∃ H : Main.Match Z hG M σ dial,
      ∀ (ν : ℝ) {ι : Type} (u : Filter ι) (age g : ι → ℝ)
        (_ : Tendsto age u trail) (_ : Leading F J)
        (Q : ι → Prediction G 6) (T : ι → Change G 6)
        (_ : (Z.store.survey 6).Via Q (u:=u)) (_ : Tendsto (fun i => guide G 6 (T i)) u (𝓝 0))
        (q : ι → ℕ) (e : ι → ℝ) (_ : ∀ᶠ i in u, 0 < g i)
        (_ : ∀ᶠ i in u, ∀ (rp : 0 < age i)
          (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) (Q i)))),
          price F J Z M H ν rp (Q i) (T i) (q i) (g i) hq ≤ e i)
        (_ : Tendsto (fun i => e i / g i) u (𝓝 0)),
        Tendsto (fun i => WilsonPositionHomogeneousFrame.reading F J Z (age i)/g i) u (𝓝 1) := by
  obtain ⟨σ,H⟩ := Main.wilson_to_MS Z hG M dial
  refine ⟨σ,H,fun ν ι u age g near lead Q T warm oriented q e positive earned small => ?_⟩
  obtain ⟨C,cp,fixed⟩ :=
    WilsonPositionProgramTrialPublicJointPivotThermometer.original F J Z M H ν u age near lead
  let c := Rose.cT Z.criterion.cut G Z.criterion.image
  have cpos : 0 < |c| := abs_pos.mpr Z.criterion.fresh.ne
  have shrink : Tendsto (fun i => C / |c| * (e i / g i)) u (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=C / |c|)).mul small
  apply Metric.tendsto_nhds.mpr
  intro ε εp
  have scale : ∀ᶠ i in u, 0 < age i := near.eventually self_mem_nhdsWithin
  filter_upwards [fixed Q T warm oriented, (Z.store.survey 6).stand_sure (Z.store.prepared 6) warm,
    scale,positive,earned,(tendsto_order.mp shrink).2 ε εp] with i bound sure rp gp bought finish
  rw [Real.dist_eq]
  apply lt_of_le_of_lt (bound rp sure (q i) (g i) gp)
  have funded := bought rp sure
  calc
    C * price F J Z M H ν rp (Q i) (T i) (q i) (g i) sure / |c| / g i
        ≤ C * e i / |c| / g i :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left funded cp.le) cpos.le) gp.le
    _ = C / |c| * (e i / g i) := by ring
    _ < ε := finish

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotRate
