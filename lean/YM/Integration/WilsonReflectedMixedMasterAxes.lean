import YM.Integration.WilsonReflectedMixedFundedSeat
import YM.Integration.WilsonReflectedMixedSignedCampus
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedMasterAxes
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

/-- The independently elected fit and all its physical placements are held on
one trial basis. -/
def Fixed (d j target N p f K e:ℕ)(first:j≤f)(up:f≤K)(live:K≤N)(Y:(C).label d)(M ceiling:ℝ)
    (F:(C).label d ≃ₗ[ℂ] (C).label d):Prop:=
  (∀x,Arrived R d j K N p target (first.trans up) live (1/32) F x) ∧
  let w:=F.symm (fitted R d j N p Y)
  ((C).labels.level d).coeffSize ((((C).S.a K:ℂ)^d)⁻¹ • w)≤ceiling ∧
  ∀(s:Signed)(b:Bool)(o:Site ((C).side f p)),∃A:Arm R d N p f K,
    A.Y=Y ∧ A.w=w ∧ A.b=b ∧ A.s=s ∧ A.o=o ∧
    Priced R A (rent R d M*((H f)^(e+1))⁻¹*((C).S.a f)^d)

theorem original (d j target N p f K e:ℕ)(up:f≤K)(live:K≤N)(Y:(C).label d)(M ceiling:ℝ)
    (paid:WilsonReflectedMixedFundedSeat.Seat R d j target N p f K e up live Y M ceiling):
    ∃(first:j≤f)(F:(C).label d ≃ₗ[ℂ] (C).label d),Fixed R d j target N p f K e first up live Y M ceiling F:=paid

theorem placed {d j target N p f K e:ℕ}{first:j≤f}{up:f≤K}{live:K≤N}{Y:(C).label d}{M ceiling:ℝ}
    {F:(C).label d ≃ₗ[ℂ] (C).label d}(fixed:Fixed R d j target N p f K e first up live Y M ceiling F)
    (s:Signed)(b:Bool)(o:Site ((C).side f p)):
    let w:=F.symm (fitted R d j N p Y)
    ∃A:Arm R d N p f K,A.Y=Y ∧ A.w=w ∧ A.b=b ∧ A.s=s ∧ A.o=o ∧
      Priced R A (rent R d M*((H f)^(e+1))⁻¹*((C).S.a f)^d) ∧
      ∀c:ℝ,0≤c→c≤1→((C).labels.level d).coeffSize (((c:ℂ)*(((C).S.a K:ℂ)^d)⁻¹) • WilsonReflectedPublicGuardedMotion.coords R A)
        ≤ orbitCost ((C).labels.level d)*ceiling:=by
  obtain ⟨a,ay,aw,ab,as',ao,price⟩:=fixed.2.2 s b o
  refine ⟨a,ay,aw,ab,as',ao,price,?_⟩
  intro c pos small
  exact WilsonReflectedMixedSignedCampus.rotated R a (bank:=ceiling) c pos small (by rw [aw];exact fixed.2.1)

end YM.Integration.WilsonReflectedMixedMasterAxes
end
