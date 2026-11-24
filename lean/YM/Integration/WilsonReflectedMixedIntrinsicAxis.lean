import YM.Integration.WilsonReflectedMixedMasterAxes
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedIntrinsicAxis
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

/-- A single column measured on the earlier admitted physical site has the same
inverse K-coordinate in any other genuine complete calibration of that site. -/
theorem original {d j K N p old new:ℕ}{η η':ℝ}(ref:(C).ref d≤j)(before:j≤K)(live:K≤N)
    {A F:(C).label d≃ₗ[ℂ](C).label d}{x:(C).label d}
    (previous:Arrived R d j K N p old before live η A x)
    (current:∀u,Arrived R d j K N p new before live η' F u):
    A.symm x=F.symm x:=by
  let w:=A.symm x
  obtain ⟨_,q,hq,priceq,readq,seenq,_⟩:=previous
  obtain ⟨_,v,hv,pricev,readv,seenv,_⟩:=current (F w)
  have eq:value d N p j q=value d N p j v:=by
    exact readq.trans (by simpa only [LinearEquiv.symm_apply_apply] using readv.symm)
  have same:=same_page R.makes (before.trans live) ref (q:=q) (s:=v)
    ⟨hq,priceq⟩ ⟨hv,pricev⟩ (EventuallyEq.of_eq eq)
  have stored:((C).path.rep N p j).p=plank C j:=(R.makes.wilson.represents N p j (before.trans live)).vac
  have coordinate:x=F w:=by
    rw [stored] at seenq seenv
    exact seenq.symm.trans (same.trans seenv)
  apply F.injective
  simpa only [LinearEquiv.apply_symm_apply] using coordinate.symm

/-- The complete calibrated map is intrinsic on this admitted finite history. -/
theorem unique {d j K N p old new:ℕ}{η η':ℝ}(ref:(C).ref d≤j)(before:j≤K)(live:K≤N)
    {A F:(C).label d≃ₗ[ℂ](C).label d}
    (previous:∀x,Arrived R d j K N p old before live η A x)
    (current:∀x,Arrived R d j K N p new before live η' F x):
    A=F:=by
  apply LinearEquiv.ext
  intro v
  have h:=congrArg F (original R ref before live (previous (A v)) current)
  simpa only [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply] using h.symm

end YM.Integration.WilsonReflectedMixedIntrinsicAxis
end
