import YM.Integration.WilsonCoherentMayerCloseCampus
import YM.Integration.WilsonCloseCaptureCalendar
import YM.QuadraticLocal.Class.HoursCost

/-! The full product of the original per-stage allowances on the actual reporting window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerCaptureRent
open Filter Lattice RG OPE OPE.Log Trace.Pilot PhysicalNext.Repeat.Legato Bandage
open WilsonLimitConstruction RG05Readout Many Halls Records Chalice Address Native
open QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (hG:G.Simple)
local notation "first" => WilsonCloseCaptureCalendar.lower R
local notation "last" => WilsonCloseCaptureCalendar.reported R hG
local notation "β̂" => R.alloy.B.a.clock.hatBeta

theorem span (slow:WilsonWindowReportingPace.Slow R.kit) {cap:ℕ} (wide:4<cap):
    ∀ᶠ r:ℝ in trail,
      let m:=first r+1
      let b:=last cap r
      m<b ∧ CaptureW R.family m b r cap ∧ PaceR.Close R 1 ((cap+2:ℕ):ℝ) m b:=by
  obtain ⟨_,_,dates⟩:=WilsonCloseCaptureCalendar.dates R hG slow wide
  have late:=(PhysMS.length_rate.tends neg_one_lt_zero PhysMS.to_log_zoom).eventually
    (gt_mem_nhds (R.family.S.a_pos 0))
  filter_upwards [PhysMS.length_rate.pos,late,dates] with r positive fine chosen
  change 0<r at positive
  have window:=WilsonCloseCaptureDate.window R slow hG (B:=cap) (by omega) positive fine.le
  refine ⟨chosen.2.1,chosen.2.2,?_⟩
  unfold PaceR.Close
  rw [pow_one,chosen.1]
  exact window.2.2.2.2.2

theorem original (slow:WilsonWindowReportingPace.Slow R.kit) {cap:ℕ} (wide:4<cap)
    (grade shelf pieces degree load:ℕ) {ε:ℝ} (small:0<ε) (room:ε≤1/8):
    ∀ᶠ r:ℝ in trail,
      let m:=first r+1
      let b:=last cap r
      let U:=WilsonCoherentMayerCloseCampus.curriculum grade shelf pieces
      CaptureW R.family m b r cap ∧ Sycamore.Attends R U ε m b degree ∧
      ∀ i : ℕ, m ≤ i → i ≤ b → (PaceR.roof R i b)^load ≤ (β̂ b)^ε:=by
  let U:=WilsonCoherentMayerCloseCampus.curriculum grade shelf pieces
  let Q:ℝ:=(cap+2:ℕ)
  have qp:0≤Q:=by dsimp [Q]; positivity
  have height:=(WilsonCloseCaptureCalendar.dates R hG slow wide).2.1.grows
  have money:=Sycamore.learners R hG small room U (Q:=Q) qp 1 degree
  have roof:=PaceR.gives R hG 1 load Q qp ε small
  filter_upwards [span R hG slow wide,height.eventually money,height.eventually roof] with r date earn full
  exact ⟨date.2.1,earn _ date.1.le date.2.2,fun i lower upper=>full _ i lower upper date.2.2⟩

end YM.Integration.WilsonCoherentMayerCaptureRent
