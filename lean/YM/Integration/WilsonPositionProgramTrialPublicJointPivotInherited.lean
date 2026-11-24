import YM.Integration.WilsonPositionProgramTrialPublicJointPivotNominated
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotWeights

/-! The positioned thermometer on the same bounded inherited columns in both pivot programs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotInherited
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


open WilsonPositionProgramTrialPublicJointPivotWeights (salary)
variable {G : Gauge} {d n : ℕ}

def Released (V : Pin G d → Sec G d) (M W : Row G d n) (B e : ℝ) : Prop :=
  ∃ P Q : Row G d n,
    (∀ b : Fin n → Pin G d, (∏ j, salary (V (b j))) ≤ B) ∧
    (∀ b, ‖rows M b - P (V ∘ b)‖ ≤ e) ∧
    (∀ a, ‖rows P a - rows Q a‖ ≤ e) ∧
    (∀ b, ‖Q (V ∘ b) - rows W b‖ ≤ e)

theorem spent {V : Pin G d → Sec G d} {M W : Row G d n} {B e : ℝ}
    (bp : 0 ≤ B) (ep : 0 ≤ e) (released : Released V M W B e) :
    ‖rows M - rows W‖ ≤ (2+B)*e := by
  obtain ⟨P,Q,bounded,old,comparison,chart⟩ := released
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) ep)).2
  intro b
  have mid := WilsonPositionProgramTrialPublicJointPivotWeights.paid P Q (V ∘ b) ep comparison
  have high := mul_le_mul_of_nonneg_right (bounded b) ep
  change ‖rows M b - rows W b‖ ≤ _
  calc
    ‖rows M b - rows W b‖ ≤ ‖rows M b - P (V ∘ b)‖ + ‖P (V ∘ b) - rows W b‖ :=
      by simpa only [dist_eq_norm] using dist_triangle (rows M b) (P (V ∘ b)) (rows W b)
    _ ≤ e + (‖P (V ∘ b) - Q (V ∘ b)‖ + ‖Q (V ∘ b) - rows W b‖) :=
      add_le_add (old b) (by simpa only [dist_eq_norm] using dist_triangle (P (V ∘ b)) (Q (V ∘ b)) (rows W b))
    _ ≤ e + (B*e + e) := add_le_add (le_refl e) (add_le_add (mid.trans high) (chart b))
    _ = _ := by ring
open WilsonPositionProgramTrialPublicJointPivotNominated (cost)
open WilsonPositionProgramTrialPublicJointPivotNorm (moved)
open WilsonPositionProgramTrialPublicJointPivotSalary (physical)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionProgramTrialPublicJointPivotTarget (row)
variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    (hG : G.Simple) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial)

def Panel (ν : ℝ) {r : ℝ} (rp : 0<r) (T : Change G 6) (k q : ℕ) (g : ℝ)
    (V : Pin G 6 → Sec G 6) (B e : ℝ) : Prop :=
  let D := Z.store.survey 6
  Released V (physical F J Z rp) (moved T (row Z M H ν 0 (q+1) g)) B e ∧
    ∀ a : Fin D.n, Released V ((hierarchy F J 6 r) (D.scope a).n (D.scope a).t)
      ((recruit (stand T) (forecast Z M ν 6 k g)) (D.scope a).n (D.scope a).t) B e

theorem elected (ν : ℝ) {r : ℝ} (rp : 0<r) (T : Change G 6) (k q : ℕ) (g : ℝ)
    (V : Pin G 6 → Sec G 6) {B e : ℝ} (bp : 0 ≤ B) (ep : 0 ≤ e)
    (paid : Panel F J Z hG M H ν rp T k q g V B e) :
    cost F J Z hG M H ν rp T k q g ≤ (2+B)*e := by
  have pos : 0 ≤ (2+B)*e := mul_nonneg (by linarith) ep
  apply max_le (spent bp ep paid.1)
  apply (pi_norm_le_iff_of_nonneg pos).2
  intro h
  apply (pi_norm_le_iff_of_nonneg pos).2
  intro a
  exact spent bp ep (paid.2 a)

theorem original (branch : Bool) :
    ∃ σ : Prescription (Press.portDeck G), ∃ A : Main.Match Z hG M σ branch,
      ∀ (ν : ℝ) (k q : ℕ) {ι : Type} (u : Filter ι) (age g : ι → ℝ)
        (_ : Tendsto age u trail) (_ : Leading F J) (_ : Tendsto g u (𝓝 0))
        (T : ι → Change G 6) (_ : Tendsto (fun i => guide G 6 (T i)) u (𝓝 0))
        (V : ι → Pin G 6 → Sec G 6) (B : ℝ) (_ : 0 ≤ B) (e : ι → ℝ)
        (_ : ∀ᶠ i in u, 0 < g i ∧ 0 ≤ e i)
        (_ : ∀ᶠ i in u, ∀ (rp : 0 < age i), Panel F J Z hG M A ν rp (T i) k q (g i) (V i) B (e i))
        (_ : Tendsto (fun i => e i/g i) u (𝓝 0)),
        Tendsto (fun i => WilsonPositionHomogeneousFrame.reading F J Z (age i)/g i) u (𝓝 1) := by
  obtain ⟨σ,A,book⟩ := WilsonPositionProgramTrialPublicJointPivotNominated.original F J Z hG M branch
  refine ⟨σ,A,fun ν k q ι u age g limit lead cold T near V B bp e live paid small => ?_⟩
  apply book ν k q u age g limit lead cold T near (fun i => (2+B)*e i) (live.mono fun _ h => h.1) _ _
  · filter_upwards [live,paid] with i placed hired
    intro rp
    exact elected F J Z hG M A ν rp (T i) k q (g i) (V i) bp placed.2 (hired rp)
  · simpa only [mul_div_assoc,mul_zero] using (tendsto_const_nhds (x:=2+B)).mul small

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotInherited
