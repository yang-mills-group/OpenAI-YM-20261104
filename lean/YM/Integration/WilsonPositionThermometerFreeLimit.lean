import YM.Integration.WilsonPositionThermometerTest

/-! The exact physical calibrated position test tends to zero on every
vacuum character. This buys the small-input domain for the independently
computed inverse series, without buying its first slope from a free limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerFreeLimit
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerReading WilsonPositionThermometerPhases
open private average from YM.Integration.WilsonPositionThermometerTest
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S) {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)
variable (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (H : Leading F J)
    (hG : G.Simple) (X : Scaling S) (foundation : Foundation F reader)

include reader H hG X foundation in
theorem small {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in trail,∀ p : Viewers F, |WilsonPositionThermometerTest.read F J K p r| < ε := by
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
  have bank := WilsonPositionThermometerPhases.small F J reader H hG X foundation Φ.hasCompactSupport Φ.tsupport_subset pos
  filter_upwards [bank,RG17.positiveLength] with r ready hr p
  have point (x : Points 3) (hx : x∈tsupport Φ) : ‖raw F J p r x‖ ≤ 13*t := by
    have a := WilsonPositionThermometerOscillation.difference (A:=part F J p r x) (B:=zero) (δ:=t)
      (fun s hs=>(ready s x hx p hs).le.trans (min_le_left _ _)) (fun _ _=>by simp [zero])
      (fun s hs=>by simpa only [zero,sub_zero] using (ready s x hx p hs).le)
    simpa only [WilsonPositionThermometerPhases.raw,hz,sub_zero] using a
  have av := average K (WilsonPositionThermometerTest.continuous F J p hr) (continuousOn_const (c:=(0:ℂ)))
    (t:=13*t) (fun x hx=> by simpa only [sub_zero] using point x hx)
  have I : Φ.applyTo (fun _=>0) = 0 := by simp [Test.applyTo]
  change ‖Φ.applyTo (raw F J p r) - Φ.applyTo (fun _=>0)‖ ≤ m*(13*t) at av
  rw [I,sub_zero] at av
  change |(Φ.applyTo (raw F J p r)).re/c| < ε
  rw [abs_div,div_lt_iff₀ hc]
  exact (Complex.abs_re_le_norm _).trans_lt (av.trans_lt charge)

include reader H hG X foundation in
theorem measured : Tendsto (reading F J K) trail (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [small F J K reader H hG X foundation he] with r paid
  simpa only [Real.dist_eq,sub_zero,←WilsonPositionThermometerTest.unselected] using paid none

end YM.Integration.WilsonPositionThermometerFreeLimit
