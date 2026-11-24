import YM.Integration.WilsonPositionScaleLawGuardSmall

/-! Every separately included lower input below weight four is paid exactly at every retained horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardIncludedUnit
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawGuardInvoice (issue)
open WilsonPositionScaleLawDressedTransport (guard dressed)
open WilsonPositionScaleLawKinetic (kinetic)
open Pert.RawLabels (physicalLabel enroll physical_round physical_unit)
open scoped Topology Classical Asymptotics
variable {G:Gauge}

theorem raised (C:Family G){j d:ℕ}(h:j≤d):(scheme C.labels).rise h ((Bel C.book).unit j)=(Bel C.book).unit d:=by
  apply (fields C.labels d).injective
  apply Subtype.ext
  exact (address_rise C.labels d h _).trans ((unit_address C.labels j).trans (unit_address C.labels d).symm)

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
    {hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
set_option quotPrecheck false
local notation "unit"=> (Bel R.family.book).unit

include H in
theorem original (lead:Leading F J)(d:ℕ):∀ᶠr in trail,∀t:ℝ,∀ht:0<t,t≤1→∀q j:ℕ,∀h:j≤d,j<4→∀v:(Bel R.family.book).Field j,
    change (WilsonPositionHomogeneousFrame.homogeneous F J Z) d r t ht ((scheme R.family.labels).rise h v)=
      issue R.family q (guard Z M ν (-Real.log t) d) (kinetic Z F J r:ℂ) ((scheme R.family.labels).rise h v):=by
  filter_upwards [WilsonPositionScaleLawGuardEveryUnit.original F J Z M H ν lead d] with r hit t ht short q j h small v
  obtain ⟨s,rfl⟩:=WilsonPositionScaleLawGuardSmall.scalar R.family hG small v
  rw [map_smul,raised,map_smul,map_smul,hit t ht short q]

end YM.Integration.WilsonPositionScaleLawGuardIncludedUnit
