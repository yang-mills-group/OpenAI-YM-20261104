import YM.Integration.WilsonPositionPrescribedLeading
import YM.Integration.WilsonPositionThermometerFreeLimit
import YM.Integration.WilsonPositionThermometerDefect

/-! The genuine position thermometer on the frame solving the independently prescribed
measuring equations. Its constant term vanishes, including its original signed test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedZero
open Function Filter Set Asymptotics MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open XSpace XSpace.Normalize XSpace.Rose WilsonPositionThermometerReading WilsonPositionThermometerPhases
open FVA2 FVA2.Register FVA2.Scale MS MS.Land WilsonIndependentSchemeTruncation
open private average from YM.Integration.WilsonPositionThermometerTest
open scoped Topology Classical ContDiff
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ→PhysMS.tower S) (V : Store G) (lead : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)

include lead paid in
theorem measured (hG : G.Simple) (K : Rose.Pick V) :
    Tendsto (reading F (WilsonPositionPrescribedFrame.positioned F J V) K) Trace.Pilot.trail (𝓝 0) := by
  let P:=WilsonPositionPrescribedFrame.positioned F J V
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let Φ := Rose.test K
  let m := WilsonPositionThermometerTest.mass K
  let c := Rose.cT K.cut G K.image
  have hm : 0 ≤ m := integral_nonneg fun _ => norm_nonneg _
  have hc : 0 < |c| := abs_pos.mpr K.fresh.ne
  let t := min 1 ((ε/2)*|c|/(13*(m+1)))
  have den : 0<13*(m+1) := by linarith
  have pos : 0<t := lt_min one_pos (div_pos (mul_pos (half_pos he) hc) den)
  have charge : m*(13*t)<ε*|c| := by
    have a : t*(13*(m+1)) ≤ (ε/2)*|c| := (le_div_iff₀ den).1 (min_le_right _ _)
    have b : t*(13*m) ≤ t*(13*(m+1)) := mul_le_mul_of_nonneg_left (by linarith) pos.le
    have hh : (ε/2)*|c| < ε*|c| := mul_lt_mul_of_pos_right (half_lt_self he) hc
    linarith only [a,b,hh]
  let zero : Badge→ℂ := fun _=>0
  have hz : WilsonPositionThermometerConnected.value zero=0 := by simp [WilsonPositionThermometerConnected.value,zero]
  have bank := WilsonPositionPrescribedLeading.rose F J V lead paid hG Φ.hasCompactSupport Φ.tsupport_subset pos
  filter_upwards [bank,RG17.positiveLength] with r ready hr
  rw [Real.dist_eq,sub_zero]
  have point (x : Points 3) (hx : x∈tsupport Φ) : ‖raw F P none r x‖ ≤ 13*t := by
    have tiny (s : Badge) (hs : s.Nonempty) : ‖part F P none r x s‖≤t := by
      change ‖sample F P r x s‖≤t
      exact (ready s x hx hs).le
    have a := WilsonPositionThermometerOscillation.difference (A:=part F P none r x) (B:=zero) (δ:=t)
      (fun s hs=>(tiny s hs).trans (min_le_left _ _)) (fun _ _=>by simp [zero])
      (fun s hs=>by simpa only [zero,sub_zero] using tiny s hs)
    simpa only [WilsonPositionThermometerPhases.raw,hz,sub_zero] using a
  have av := average K (WilsonPositionThermometerTest.continuous F P none hr) (continuousOn_const (c:=(0:ℂ)))
    (t:=13*t) (fun x hx=> by simpa only [sub_zero] using point x hx)
  have I : Φ.applyTo (fun _=>0) = 0 := by simp [Test.applyTo]
  change ‖Φ.applyTo (raw F P none r) - Φ.applyTo (fun _=>0)‖ ≤ m*(13*t) at av
  rw [I,sub_zero] at av
  change |(Φ.applyTo (raw F P none r)).re/c| < ε
  rw [abs_div,div_lt_iff₀ hc]
  exact (Complex.abs_re_le_norm _).trans_lt (av.trans_lt charge)

variable (Z : WilsonPrescription G) (ν : ℝ) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))

theorem constant (r t : ℝ) :
    WilsonPositionThermometerDefect.continuum F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z ν M 0 r t =
    reading F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z.criterion r := by
  unfold WilsonPositionThermometerDefect.continuum WilsonPositionThermometerReading.reading WilsonPositionThermometerReading.tested
  simp only [WilsonPositionIndependentIntegral.positive,Finset.range_zero,Finset.sum_empty,sub_zero]
  rfl

include lead paid in
theorem zero (hG : G.Simple) (t : ℝ→ℝ) :
    (fun r=>WilsonPositionThermometerDefect.continuum F (WilsonPositionPrescribedFrame.positioned F J Z.store)
      Z ν M 0 r (t r))=o[Trace.Pilot.trail] (fun _=> (1:ℝ)) := by
  simp only [constant]
  exact (isLittleO_one_iff ℝ).mpr (measured F J Z.store lead paid hG Z.criterion)

theorem first {simple : G.Simple} {Q : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match Z simple M Q dial) {r : ℝ} (hr : 0<r) (t : ℝ) :
    WilsonPositionThermometerDefect.continuum F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z ν M 1 r t =
      reading F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z.criterion r - t := by
  rw [WilsonPositionThermometerDefect.reference F _ Z ν M 1 r t hr,WilsonPositionIndependentIntegral.linear Z ν matched t,Complex.ofReal_re]

include lead paid in
theorem finite (hG : G.Simple) (q : ℕ) (t : ℝ→ℝ) (ht : Tendsto t Trace.Pilot.trail (𝓝 0)) :
    (fun r=>WilsonPositionThermometerDefect.continuum F (WilsonPositionPrescribedFrame.positioned F J Z.store)
      Z ν M q r (t r))=o[Trace.Pilot.trail] (fun _=>(1:ℝ)) := by
  let Y₁:=WilsonPositionPrescribedFrame.positioned F J Z.store
  let a:=WilsonIndependentSchemeTruncation.finite q (Measure.chi Z.criterion ν M)
  let val (v : ℝ) := (a.eval (v:ℂ)).re
  have continuous : Continuous val := by dsimp only [val];fun_prop
  have empty : val 0=0 := by
    change ((WilsonIndependentSchemeTruncation.finite q (Measure.chi Z.criterion ν M)).eval ((0:ℝ):ℂ)).re=0
    rw [WilsonPositionIndependentIntegral.real_polynomial]
    simp [WilsonPositionIndependentIntegral.positive,Test.applyTo]
  have vanish := (continuous.tendsto 0).comp ht
  rw [empty] at vanish
  apply (isLittleO_one_iff ℝ).mpr
  have close:= (measured F J Z.store lead paid hG Z.criterion).sub vanish
  rw [sub_zero] at close
  apply close.congr'
  filter_upwards [RG17.positiveLength] with r hr
  exact (WilsonPositionThermometerDefect.reference F Y₁ Z ν M q r (t r) hr).symm

end YM.Integration.WilsonPositionPrescribedZero
