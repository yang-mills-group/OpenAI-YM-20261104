import YM.Integration.WilsonPositionProgramTrialPublicJointPivotSurveyed
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotCompact
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotSalary

/-! The physical cumulant after its common section change and both ordered regulator limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotComparison
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


open Trace.Terrace Trace.Pilot Trace.Physical Trace.Physical.Germ PhysicalNext
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent WilsonMeasuredPublicBank
open WilsonPositionProgramTrialPublicJointPivotEvidence (old independent)
open WilsonPositionProgramTrialPublicJointPivotOrdered (Enrolled)
open WilsonPositionProgramTrialPublicJointPivotSurveyed (Licensed)
open WilsonPositionProgramTrialPublicJointPivotNorm (moved)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionProgramTrialPublicJointPivotCompact (fee)
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)
variable {l : Ultrafilter (ℕ×ℕ)} {prior : (Bel R.family.book).Hierarchy} {z : Trace.Terrace.Arch R.family}
variable {d : ℕ}

def observed (φ : Test 3) (v : Fin 3 → Sec G d) (r : ℝ) : ℂ :=
  if rp : 0<r then old F (WilsonPositionPrescribedFrame.positioned F J Z.store) d φ rp v else 0

def Posted (φ : Test 3) {r : ℝ} (rp : 0<r) (T : Change G d) (k q : ℕ) (g : ℝ)
    (V : (ℕ×ℕ) → Pin G d → Sec G d) (B e : ℝ) : Prop :=
  Enrolled (l:Filter (ℕ×ℕ)) V (old F J d φ rp) (moved T (independent Z M H ν d φ q g)) B e ∧
    Licensed Z (l:Filter (ℕ×ℕ)) V (hierarchy F J d r) (forecast Z M ν d k g) T B e

theorem quoted (bliss : Bliss F l z prior) (lead : Leading F J) (v : Fin 3 → Sec G d) :
    ∃ C : ℝ, 0<C ∧ ∀ (k : ℕ) (T : ℝ→Change G d) (_ : Tendsto (fun r=>guide G d (T r)) trail (𝓝 0)),
      ∀ᶠ r in trail, ∀ (rp : 0<r) (φ : Test 3) (q : ℕ) (V : (ℕ×ℕ) → Pin G d → Sec G d)
        {B e : ℝ} (_ : 0≤B) (_ : 0≤e)
        (_ : Posted F J Z M H ν (l:=l) φ rp (T r) k q (wilson z r) V B e),
        ‖observed F J Z φ v r - independent Z M H ν d φ q (wilson z r) v‖ ≤
          C*((2+B)*e*(1+2*fee Z d φ q)) := by
  obtain ⟨C,cp,account⟩ := WilsonPositionProgramTrialPublicJointPivotSurveyed.original
    (τ:=ℕ×ℕ) F J Z M H ν v trail id tendsto_id lead
  have link := wilson_link F hG bliss.budgets bliss.keen bliss.lies
  have cold := link.conforms hG
  have soon : ∀ᶠ r in trail, wilson z r ≤ 1 := cold.eventually (eventually_le_nhds zero_lt_one)
  refine ⟨C,cp,fun k T near => ?_⟩
  filter_upwards [account k (wilson z) cold T near,
    WilsonPositionProgramTrialPublicJointPivotNorm.drift (n:=3) trail T near,
    (WilsonPositionPrescribedScreen.original F J lead Z.store d).2,soon,link.positive] with r paid drift solid small gp
  intro rp φ q V B e bp ep post
  let W := independent Z M H ν d φ q (wilson z r)
  have joined := paid (old F J d φ rp) W (l:Filter (ℕ×ℕ)) V bp ep post.1 post.2
  dsimp only [id] at joined
  rw [WilsonPositionProgramTrialPublicJointPivotEvidence.actual F J Z φ rp v solid.2.1] at joined
  rw [observed,dif_pos rp]
  apply joined.trans
  apply mul_le_mul_of_nonneg_left _ cp.le
  have bound : ‖rows W‖ ≤ fee Z d φ q :=
    WilsonPositionProgramTrialPublicJointPivotCompact.original Z M H ν d φ q (wilson z r)
      (by simpa [abs_of_pos gp] using small)
  have smallMove : ‖rows (moved (T r) W)‖ ≤ 2*fee Z d φ q := by
    have triangle := norm_le_norm_sub_add (rows (moved (T r) W)) (rows W)
    have slight := drift W
    linarith [norm_nonneg (rows W)]
  have source : 0≤(2+B)*e := mul_nonneg (by linarith) ep
  calc
    _ ≤ (2+B)*e+(2+B)*e*(2*fee Z d φ q) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left smallMove source)
    _ = _ := by ring

theorem original (bliss : Bliss F l z prior) (lead : Leading F J) (φ : Test 3) (v : Fin 3 → Sec G d)
    (k q p : ℕ) (T : ℝ→Change G d) (near : Tendsto (fun r=>guide G d (T r)) trail (𝓝 0))
    (V : ℝ→(ℕ×ℕ)→Pin G d→Sec G d) (B : ℝ) (bp : 0≤B) (e : ℝ→ℝ) (ep : ∀ᶠ r in trail, 0≤e r)
    (issued : ∀ᶠ r in trail, ∀ (rp : 0<r),Posted F J Z M H ν (l:=l) φ rp (T r) k q
        (wilson z r) (V r) B (e r))
    (tiny : Tendsto (fun r=>e r/(wilson z r)^p) trail (𝓝 0)) :
    Tendsto (fun r=>‖observed F J Z φ v r - independent Z M H ν d φ q (wilson z r) v‖ /
      (wilson z r)^p) trail (𝓝 0) := by
  obtain ⟨C,_,account⟩ := quoted F J Z M H ν bliss lead v
  let D := C*(2+B)*(1+2*fee Z d φ q)
  have rhs : Tendsto (fun r=> D*(e r/(wilson z r)^p)) trail (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=D)).mul tiny
  have link := wilson_link F hG bliss.budgets bliss.keen bliss.lies
  apply squeeze_zero' _ _ rhs
  · filter_upwards [link.positive] with r hot
    exact div_nonneg (norm_nonneg _) (pow_nonneg hot.le _)
  · filter_upwards [account k T near,issued,ep,link.positive,RG17.positiveLength] with r pay bought pos gp rp
    calc
      _ ≤ (C*((2+B)*e r*(1+2*fee Z d φ q)))/(wilson z r)^p :=
        div_le_div_of_nonneg_right (pay rp φ q (V r) bp pos (bought rp)) (pow_nonneg gp.le _)
      _ = _ := by dsimp only [D]; ring

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotComparison
