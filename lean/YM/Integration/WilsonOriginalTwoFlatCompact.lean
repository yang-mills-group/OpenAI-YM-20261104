import YM.Integration.WilsonThermometerPlantedOrdinary
import YM.Integration.WilsonThermometerUnitFilingStops

/-! One independently filed ordinary word at capture, evaluated on its original
Wilson marginal at the fixed and moving flat stops. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatCompact
open Function Filter Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal
open Push.Local Push.AbsoluteSums Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple){N per c u v:ℕ}
local notation "C" => R.family
local notation "rep" => (C).path.rep N per c
local notation "Y" => (C).params
local notation "Sec" => (C).localSection 0
local notation "μ" => price G (max (rep).p.order (rep).p.power)
local notation "κ" => LocalComparison.forcedDivisor C c
local notation "v₀" => R.alloy.B.a.clock.forcedAllowance c

include simple in
theorem original (cu:(C).ref 0 ≤ u)(uv:u ≤ v)(vc:v ≤ c)(cN:c<N)
    (ou:Opened C 0 u per)(ov:Opened C 0 v per)
    (ready:WilsonCenteredCaptureClock.first R simple ≤ c)
    {V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    {o:V→Site ((C).side c per)}{p:BudgetPoint}(L:Lamps X ι G p o J)(same:(rep).p=p)
    (x:X)(s:J.Mode)(Z:Support ((C).side c per))(center:0∈Z)(reside:∀a∈s.val,o a∈Z)
    (rad:ℕ)(near:∀a∈s.val,separation (o a) 0≤rad)(w:V→ℝ)(wp:∀a,0<w a)
    {derivative gross:ℝ}(he:L.Paid w p.B (p.supportExponent+2) derivative)
    (hg:Gross L w p.B (p.supportExponent+2) gross):
    let M:=fun U=>((rep).eval U:ℂ)*(Poly.pass (bare L x U)).part s
    let fee:=WilsonPlantedOrdinary.fare (rep).p Z w derivative gross rad (Sec) (Y) μ v₀ κ s
    ‖reading R (N:=N) M u (uv.trans vc)-reading R (N:=N) M v vc‖ ≤
      2*capital C c fee 1*Real.exp (-((C).S.scale c-(C).S.scale v)/8):=by
  intro M fee
  have phys:=R.makes.wilson.represents N per c cN.le
  have read:=ActualWilsonPrimaryPreparation.original R 0 N per c (cu.trans (uv.trans vc)) cN.le
  obtain ⟨div,positive,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec c ready
  have shape:(rep).p=R.alloy.B.a.budget c:=phys.vac
  have liveRoom:hitWidth (rep).p*v₀ ≤ 1:=by rw [shape];exact room
  have paid:=WilsonPlantedOrdinary.transferred (P:=rep) L same x s 0 Z center reside rad near
    w wp he hg (OriginalForcedAddresses.actual_keeper R simple N c per cN.le) phys.good div positive
    liveRoom (Sec) (Y) read
  exact WilsonThermometerUnitFilingStops.two_stops R simple cu uv vc cN.le ou ov paid

end YM.Integration.WilsonOriginalTwoFlatCompact
end
