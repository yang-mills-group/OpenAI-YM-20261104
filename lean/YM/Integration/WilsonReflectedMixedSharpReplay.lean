import YM.Integration.WilsonReflectedMixedSharpSchool
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSharpReplay
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records MergeProof Push.Local Motion
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonMeasuredPublicEntranceGridDebit
open WilsonAddressedMixedEnrolledTrial WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]
local notation "C" => R.family
local notation "H" => (C).path.levels.clock.hatBeta


open WilsonReflectedMixedThermalArms

open Filter Trace.Physical.GermGraph
open scoped Topology


/-- Couple both earnings at the same two actual physical dates. -/
theorem stretch_mono {j K:ℕ}{η η':ℝ}(leg:j≤K)(increase:η≤η'):
    stretch R η j K ≤ stretch R η' j K:=by
  unfold WilsonOriginalMicroscopicGuardedReporters.stretch
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right increase (sub_nonneg.mpr
    (WilsonReflectedRelativeDate.monotone R leg)))

theorem arrived {d j K N p target:ℕ}{η η':ℝ}{A:(C).label d≃ₗ[ℂ](C).label d}
    {y:(C).label d}{leg:j≤K}{top:K≤N}(increase:η≤η')
    (sharp:Arrived R d j K N p target leg top η A y):
    Arrived R d j K N p target leg top η' A y:=by
  exact ⟨sharp.1.trans (mul_le_mul_of_nonneg_right (stretch_mono R leg increase)
    (Work.G08.size_nonneg ..)),sharp.2⟩

/-- At the declared arity and margin the physical pupil can draw its old 1/32
wage directly from the sharper income of the very same Wilson coordinates. -/
theorem regular {d j f K N p target n:ℕ}{before:j≤f}{up:f≤K}{live:K≤N}
    {A:(C).label d≃ₗ[ℂ](C).label d}{y:(C).label d}{W ζ:ℝ}(pos:0<ζ)(npaid:0≤W)
    (sharp:WilsonReflectedMixedSharpAxis.Cash (R:=R) d j f K N p target before up live
      (WilsonReflectedMixedSharpPanel.reserve n ζ) A y W):
    WilsonReflectedMixedSharpAxis.Cash (R:=R) d j f K N p target before up live (1/32) A y W:=by
  have increase:=(WilsonReflectedMixedSharpPanel.margin n pos).2.1
  have healthy:=sharp.2.1.trans (mul_le_mul_of_nonneg_right (stretch_mono R (before.trans up) increase)
    (mul_nonneg zero_le_two (mul_nonneg (pow_nonneg ((C).S.a_pos j).le _) npaid)))
  refine ⟨fun x=>arrived R increase (sharp.1 x),healthy,sharp.2.2.1,?_⟩
  exact fun χ good=>WilsonAddressedPublicGuardFare.cost R good healthy

end YM.Integration.WilsonReflectedMixedSharpReplay
end
