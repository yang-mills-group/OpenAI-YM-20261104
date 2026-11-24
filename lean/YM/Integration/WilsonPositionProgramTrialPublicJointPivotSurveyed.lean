import YM.Integration.WilsonPositionProgramTrialPublicJointPivotOrdered

/-! Positioned observables at any grade on the original extracted signed source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotSurveyed
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


open WilsonPhysicalNormalizedSignedMenu (positioned)
open WilsonPositionProgramTrialPublicJointPivotOrdered (Enrolled)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionProgramTrialPublicJointPivotNorm (moved)
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)
variable {d n : ℕ} {τ : Type*}

def Licensed (l : Filter τ) (V : τ → Pin G d → Sec G d) (P Q : Prediction G d) (T : Change G d) (B e : ℝ) : Prop :=
  let D := Z.store.survey d
  ∀ a : Fin D.n, Enrolled l V (P (D.scope a).n (D.scope a).t)
    ((recruit (stand T) Q) (D.scope a).n (D.scope a).t) B e

theorem position (l : Filter τ) [l.NeBot] (V : τ → Pin G d → Sec G d) (P Q : Prediction G d)
    (T : Change G d) {B e : ℝ} (bp : 0≤B) (ep : 0≤e) (tested : Licensed Z l V P Q T B e) :
    ‖docket (Z.store.survey d) (fun _:Unit => P) -
      docket (Z.store.survey d) (retag (fun _:Unit => T) (fun _:Unit => Q))‖ ≤ (2+B)*e := by
  have hi : 0≤(2+B)*e := mul_nonneg (by linarith) ep
  apply (pi_norm_le_iff_of_nonneg hi).2
  intro h
  apply (pi_norm_le_iff_of_nonneg hi).2
  intro a
  exact WilsonPositionProgramTrialPublicJointPivotOrdered.spent l bp ep (tested a)

include H in
theorem original (v : Fin n → Sec G d) {ι : Type*} (u : Filter ι) (age : ι → ℝ)
    (limit : Tendsto age u trail) (lead : Leading F J) :
    ∃ C : ℝ, 0<C ∧ ∀ (k : ℕ) (g : ι → ℝ) (_ : Tendsto g u (𝓝 0)) (T : ι → Change G d)
      (_ : Tendsto (fun i => guide G d (T i)) u (𝓝 0)), ∀ᶠ i in u,
      ∀ (A W : Row G d n) (l : Filter τ) [l.NeBot] (V : τ → Pin G d → Sec G d)
        {B e : ℝ} (_ : 0≤B) (_ : 0≤e)
        (_ : Enrolled l V A (moved (T i) W) B e)
        (_ : Licensed Z l V (hierarchy F J d (age i)) (forecast Z M ν d k (g i)) (T i) B e),
        ‖positioned (Z.store.survey d) (Z.store.prepared d) (fun _:Fin n=>()) v
          (fun _:Unit => hierarchy F J d (age i)) A - W v‖ ≤
          C*((2+B)*e + (2+B)*e*‖rows (moved (T i) W)‖) := by
  let D := Z.store.survey d
  obtain ⟨C,cp,sale⟩ := WilsonPhysicalCommonSignedAperture.original D (Z.store.prepared d) (fun _:Fin n=>()) v u
  refine ⟨C,cp,fun k g cold T near => ?_⟩
  let Q (i : ι) := forecast Z M ν d k (g i)
  have ready := WilsonPositionProgramTrialPublicJointPivotForecast.original Z M H ν u d k g cold
  have zero := WilsonPositionProgramTrialPublicJointPivotPrepositioned.original Z M H ν u d k g cold
  have booked := sale (fun i (_:Unit) => hierarchy F J d (age i)) (fun i (_:Unit) => Q i)
    (fun i (_:Unit) => T i) (fun _ => (WilsonPositionPrescribedScreen.warm F J lead Z.store d).comp limit)
    (fun _ => ready) (fun _ => near)
  filter_upwards [booked,zero] with i priced steady
  intro A W l nl V B e bp ep heard placed
  have account := priced A W
  have exactField : positioned D (Z.store.prepared d) (fun _:Fin n=>()) v (fun _:Unit=>Q i) W = W v := by
    change W (fun j => stand ((Z.store.survey d).firstPass (Z.store.prepared d) (forecast Z M ν d k (g i))) (v j)) = W v
    simp only [steady,stand0,Module.End.one_apply]
  rw [exactField] at account
  apply account.trans
  apply mul_le_mul_of_nonneg_left _ cp.le
  exact add_le_add (WilsonPositionProgramTrialPublicJointPivotOrdered.spent l bp ep heard)
    (mul_le_mul_of_nonneg_right (position Z l V _ _ (T i) bp ep placed) (norm_nonneg _))

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotSurveyed

