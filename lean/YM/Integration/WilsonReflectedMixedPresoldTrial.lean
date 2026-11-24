import YM.Integration.WilsonReflectedMixedIntrinsicAxis
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedPresoldTrial
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


open WilsonReflectedMixedMasterAxes (Fixed)

/-- The original cutoff field, signed placements, and raw K income on the
coefficient of an already measured independent trial. -/
theorem original {d j target prior N p f K e:ℕ}{η:ℝ}
    {first:j≤f}{up:f≤K}{live:K≤N}{Y:(C).label d}{M ceiling:ℝ}
    {F A:(C).label d ≃ₗ[ℂ] (C).label d}
    (ref:(C).ref d≤j)(paid:Fixed R d j target N p f K e first up live Y M ceiling F)
    (presold:Arrived R d j K N p prior (first.trans up) live η A (fitted R d j N p Y)):
    let w:=A.symm (fitted R d j N p Y)
    ((C).labels.level d).coeffSize ((((C).S.a K:ℂ)^d)⁻¹ • w)≤ceiling ∧
    ∀(s:Signed)(b:Bool)(o:Site ((C).side f p)),∃a:Arm R d N p f K,
      a.Y=Y ∧ a.w=w ∧ a.b=b ∧ a.s=s ∧ a.o=o ∧
      Priced R a (rent R d M*((H f)^(e+1))⁻¹*((C).S.a f)^d) ∧
      ∀c:ℝ,0≤c→c≤1→((C).labels.level d).coeffSize (((c:ℂ)*(((C).S.a K:ℂ)^d)⁻¹) •
        WilsonReflectedPublicGuardedMotion.coords R a)≤orbitCost ((C).labels.level d)*ceiling:=by
  have fixed:=WilsonReflectedMixedIntrinsicAxis.original R ref (first.trans up) live presold paid.1
  dsimp only
  rw [fixed]
  exact ⟨paid.2.1,WilsonReflectedMixedMasterAxes.placed R paid⟩

/-- When the previous calibration was issued on the whole space, the same
purchased status holds verbatim on the preselected matrix. -/
theorem complete {d j target prior N p f K e:ℕ}{η:ℝ}
    {first:j≤f}{up:f≤K}{live:K≤N}{Y:(C).label d}{M ceiling:ℝ}
    {F A:(C).label d ≃ₗ[ℂ] (C).label d}
    (ref:(C).ref d≤j)(paid:Fixed R d j target N p f K e first up live Y M ceiling F)
    (presold:∀x,Arrived R d j K N p prior (first.trans up) live η A x):
    Fixed R d j target N p f K e first up live Y M ceiling A:=by
  rw [WilsonReflectedMixedIntrinsicAxis.unique R ref (first.trans up) live presold paid.1]
  exact paid

end YM.Integration.WilsonReflectedMixedPresoldTrial
end
