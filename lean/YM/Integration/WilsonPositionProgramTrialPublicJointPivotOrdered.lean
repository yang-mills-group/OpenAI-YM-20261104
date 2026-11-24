import YM.Integration.WilsonPositionProgramTrialPublicJointPivotInherited

/-! Both finite procedures use the same regulator-dependent deposited pivots throughout the original physical extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotOrdered
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


open WilsonPositionProgramTrialPublicJointPivotInherited (Released)
open WilsonPositionProgramTrialPublicJointPivotNominated (cost)
open WilsonPositionProgramTrialPublicJointPivotNorm (moved)
open WilsonPositionProgramTrialPublicJointPivotSalary (physical)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionProgramTrialPublicJointPivotTarget (row)
variable {d n : ℕ} {ι : Type*}

def Enrolled (l : Filter ι) (V : ι → Pin G d → Sec G d) (M W : Row G d n) (B e : ℝ) : Prop :=
  ∃ P Q : ι → Row G d n,
    (∀ b, Tendsto (fun i => rows (P i) b) l (𝓝 (rows M b))) ∧
    (∀ b, Tendsto (fun i => rows (Q i) b) l (𝓝 (rows W b))) ∧
    ∀ᶠ i in l, Released (V i) (P i) (Q i) B e

theorem spent (l : Filter ι) [l.NeBot] {V : ι → Pin G d → Sec G d}
    {M W : Row G d n} {B e : ℝ} (bp : 0≤B) (ep : 0≤e) (issued : Enrolled l V M W B e) :
    ‖rows M - rows W‖ ≤ (2+B)*e := by
  obtain ⟨P,Q,old,new,early⟩ := issued
  have hi : 0≤(2+B)*e := mul_nonneg (by linarith) ep
  apply (pi_norm_le_iff_of_nonneg hi).2
  intro b
  change ‖rows M b - rows W b‖ ≤ _
  apply le_of_tendsto (((old b).sub (new b)).norm)
  filter_upwards [early] with i fixed
  exact (pi_norm_le_iff_of_nonneg hi).1 (WilsonPositionProgramTrialPublicJointPivotInherited.spent bp ep fixed) b

variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    (hG : G.Simple) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial)

def Panel (ν : ℝ) {r : ℝ} (rp : 0<r) (T : Change G 6) (k q : ℕ) (g : ℝ)
    (l : Filter ι) (V : ι → Pin G 6 → Sec G 6) (B e : ℝ) : Prop :=
  let D := Z.store.survey 6
  Enrolled l V (physical F J Z rp) (moved T (row Z M H ν 0 (q+1) g)) B e ∧
    ∀ a : Fin D.n, Enrolled l V ((hierarchy F J 6 r) (D.scope a).n (D.scope a).t)
      ((recruit (stand T) (forecast Z M ν 6 k g)) (D.scope a).n (D.scope a).t) B e

theorem elected (ν : ℝ) {r : ℝ} (rp : 0<r) (T : Change G 6) (k q : ℕ) (g : ℝ)
    (l : Filter ι) [l.NeBot] (V : ι → Pin G 6 → Sec G 6) {B e : ℝ} (bp : 0 ≤ B) (ep : 0 ≤ e)
    (paid : Panel F J Z hG M H ν rp T k q g l V B e) :
    cost F J Z hG M H ν rp T k q g ≤ (2+B)*e := by
  have hi : 0≤(2+B)*e := mul_nonneg (by linarith) ep
  apply max_le (spent l bp ep paid.1)
  apply (pi_norm_le_iff_of_nonneg hi).2
  intro h
  apply (pi_norm_le_iff_of_nonneg hi).2
  intro a
  exact spent l bp ep (paid.2 a)
open Trace.Terrace Trace.Pilot Trace.Physical Trace.Physical.Germ PhysicalNext
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank
variable {l : Ultrafilter (ℕ×ℕ)} {prior : (Bel R.family.book).Hierarchy} {z : Trace.Terrace.Arch R.family}
theorem original (bliss : Bliss F l z prior) (lead : Leading F J) (branch : Bool) :
    ∃ σ : Prescription (Press.portDeck G), ∃ A : Main.Match Z hG M σ branch,
      ∀ (ν : ℝ) (k q : ℕ) (T : ℝ → Change G 6) (_ : Tendsto (fun r => guide G 6 (T r)) trail (𝓝 0))
        (V : ℝ → (ℕ×ℕ) → Pin G 6 → Sec G 6) (B : ℝ) (_ : 0≤B) (e : ℝ → ℝ)
        (_ : ∀ᶠ r in trail, 0≤e r)
        (_ : ∀ᶠ r in trail, ∀ (rp : 0<r), Panel F J Z hG M A ν rp (T r) k q (wilson z r)
          (l:Filter (ℕ×ℕ)) (V r) B (e r))
        (_ : Tendsto (fun r => e r / wilson z r) trail (𝓝 0)),
        Tendsto (fun r => WilsonPositionHomogeneousFrame.reading F J Z r / wilson z r) trail (𝓝 1) := by
  obtain ⟨σ,A,accept⟩ := WilsonPositionProgramTrialPublicJointPivotNominated.original F J Z hG M branch
  refine ⟨σ,A,fun ν k q T near V B bp e ep financed small => ?_⟩
  have link := wilson_link F hG bliss.budgets bliss.keen bliss.lies
  apply accept ν k q trail id (wilson z) tendsto_id lead (link.conforms hG) T near
    (fun r => (2+B)*e r) link.positive _ _
  · filter_upwards [ep,financed] with r pos bought
    intro rp
    exact elected F J Z hG M A ν rp (T r) k q (wilson z r) (l:Filter (ℕ×ℕ)) (V r) bp pos (bought rp)
  · simpa only [mul_div_assoc,mul_zero] using (tendsto_const_nhds (x:=2+B)).mul small

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotOrdered
