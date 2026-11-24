import YM.Integration.WilsonOriginalObservedRoseProbeRead
import YM.Integration.WilsonOriginalTwoFlatRoseCapturedDigits
import YM.Integration.WilsonReceivedChronologicalFixedCellFee
/-! The tape and lift of the enrolled physical source on the original captured cells. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseProbeRoute
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonOlderFreshSoftSocketRestored (degree stopped coin)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding ActualRunPhysicalPages Pert.Asymptotics
open scoped Classical BigOperators

open WilsonOlderFreshSoftFigures (seed stencil)
open WilsonOlderFreshSoftSocketRestored (stopped)
open WilsonOlderFreshSoftSocketMeasuredCash (seats packet)
open WilsonPositionProgramReportedField (entire)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure)
open WilsonOlderFreshSoftFigureReading (reading)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshHybridClock (flat)

open WilsonOriginalTwoFlatRoseCapturedDigits (Rolled)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open WilsonOlderFreshSoftRoseNodes (enrolled TestAt anchor)
open WilsonOlderFreshSoftRoseMarket (Probe row)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonReceivedChronologicalMaterialSites (footprint)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonThermometerAlignedCells (atOrigin)
open ActualRunPhysicalPages
open WilsonCoeffUV.Bank.Realm Pert.Asymptotics Extraction
local notation "FC" => Finset (Fin 3)

open WilsonReceivedChronologicalFixedCellFee (tape)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalMaterialSites (digits footprint physical)
variable {G:Gauge}{q:ℕ}(V:Realm G (q+1) Credit.leanC)
  {f K per c v first:ℕ}(R:Run G)(draw:V.draws=R.family.path.levels)
  (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(vc:v+1≤c)(ck:c≤K)

private theorem reversed {L L':Levels G}(same:L=L')(x:Digits L' (Fin 3)):
    onLevels same (onLevels same.symm x)=x:=by subst L';rfl

private theorem zero_changed {L L':Levels G}(same:L=L')(x:Digits L' (Fin 3))(i:ℕ)(zero:x i=0):
    (onLevels same.symm x) i=0:=by subst L';exact zero

private theorem stayed (cells:Digits V.draws (Fin 3))(b t:ℕ)
    (zero:∀j,b+1≤j→j+1≤b+t+1→cells j=0):homes (V:=V) cells 0 b t=0:=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change chartIn (loose V.draws (b+t+1)) (homes (V:=V) cells 0 b t) (cells (b+t+1))=0
    rw [ih (fun j lo hi=>zero j lo (by omega)),zero (b+t+1) (by omega) (by omega)]
    funext i e
    simp [chartIn]

include V draw in
theorem purchased (old:first≤v)(housed:∀j,∀jc:j≤c,∀a,physical R (pin R fk o) (jc.trans ck) a=0):
    let entry:=tape draw fk o
    let live:=onLevels draw entry
    let fixed:=digits R (pin R fk o)
    let reported:=address R.family.path.levels live (c-(v+1)) (v+1) (homes (V:=V) entry 0 first (v-first))
    let enrolled:=address R.family.path.levels fixed (c-(v+1)) (v+1) (footprint R (pin R fk o) (vc.trans ck))
    live=fixed ∧ reported=enrolled:=by
  intro entry live fixed reported enrolled
  have trace:live=fixed:=reversed draw fixed
  have erased (j:ℕ)(hi:j+1≤c):entry j=0:=by
    apply zero_changed draw fixed j
    funext a
    let ratio:=(R.family.path.levels.clock.op j per).ratio
    change (if valid:j+1≤K then ratio.residue (physical R (pin R fk o) valid a) else 0)=0
    rw [dif_pos (hi.trans ck),housed (j+1) hi a,←ratio.root.map_zero]
    exact ratio.residue_embed 0
  have lift₀:footprint R (pin R fk o) (vc.trans ck)=0:=by
    funext a e
    simp [footprint,housed (v+1) vc a,lift]
  have begin₀:homes (V:=V) entry 0 first (v-first)=0:=
    stayed V entry first (v-first) (fun j _ hi=>erased j (by omega))
  refine ⟨trace,?_⟩
  dsimp only [reported,enrolled]
  rw [trace,lift₀,begin₀]

end YM.Integration.WilsonOriginalObservedRoseProbeRoute
end
