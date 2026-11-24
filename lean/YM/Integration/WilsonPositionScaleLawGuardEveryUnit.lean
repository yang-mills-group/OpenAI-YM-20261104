import YM.Integration.WilsonPositionScaleLawGuardUnit

/-! The exact unit reading persists even as the positive length ratio itself approaches zero. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardEveryUnit
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawGuardInvoice (issue)
open WilsonPositionScaleLawDressedTransport (guard)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "u"=>(Bel R.family.book).unit

theorem seated (d:ℕ)(r:ℝ):WilsonPositionHomogeneousFrame.homogeneous F J Z r d (u d)=J r d (u d):=by
  change J r d (WilsonPositionPrescribedFrame.change F J Z.store d r (WilsonPositionHomogeneousFrame.change F J Z d r (u d)))=_
  rw [WilsonPositionScaleLawGuardUnit.moving,WilsonPositionScaleLawGuardUnit.positioned]

theorem physical (lead:Leading F J)(d:ℕ):∀ᶠr in trail,∀t:ℝ,∀ht:0<t,t≤1→
    change (WilsonPositionHomogeneousFrame.homogeneous F J Z) d r t ht (u d)=u d:=by
  let T:=WilsonPositionHomogeneousFrame.homogeneous F J Z
  have home:∀ᶠr in trail,T r d (u d)=S.unit d:=(lead.unit d).mono fun r priced=>(seated F J Z d r).trans priced
  obtain ⟨a,ha,draw⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp home
  have near:∀ᶠr in trail,r∈Ioc 0 a:=mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨a,ha,Subset.rfl⟩
  filter_upwards [near] with r hr t ht small
  have htr:t*r∈Ioc 0 a:=⟨mul_pos ht hr.1,(mul_le_of_le_one_left hr.1.le small).trans hr.2⟩
  apply (Pert.Scale.gearIso R.family.labels d t ht).injective
  apply (T r d).injective
  change T r d (Pert.Scale.gear R.family.labels d t (Frame.cocycle d T r t ht (u d)))=T r d (Pert.Scale.gear R.family.labels d t (u d))
  rw [Frame.cocycle_value,Pert.Scale.gear_unit,draw hr,draw htr]

variable {hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
include H in
theorem original (lead:Leading F J)(d:ℕ):∀ᶠr in trail,∀t:ℝ,∀ht:0<t,t≤1→∀q:ℕ,
    change (WilsonPositionHomogeneousFrame.homogeneous F J Z) d r t ht (u d)=
      issue R.family q (guard Z M ν (-Real.log t) d) (kinetic Z F J r:ℂ) (u d):=by
  filter_upwards [physical F J Z lead d] with r paid t ht small q
  exact (paid t ht small).trans (WilsonPositionScaleLawGuardUnit.independent Z R.family M H ν _ d q _).symm

end YM.Integration.WilsonPositionScaleLawGuardEveryUnit
