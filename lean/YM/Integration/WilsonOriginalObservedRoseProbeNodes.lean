import YM.Integration.WilsonOriginalObservedRoseProbeBound
import YM.Integration.WilsonOriginalObservedRoseProbePlace
import YM.Integration.WilsonOriginalObservedRoseProbeRoute
import YM.Integration.WilsonOriginalObservedRoseHaarProbe
/-! Exact geometric registration of the genuinely occupied smooth signed cells. The original upper and lower survey can have different thermal orders. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseProbeNodes
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

open WilsonOriginalTwoFlatRosePublishedFigure (profile)
open WilsonReceivedChronologicalFixedCellFee (tape)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonOriginalObservedRoseProbePlace (ticket)
open WilsonOriginalObservedRoseProbeRead (quota)
variable {G:Gauge}(R:Run G)

theorem original (φ:Test 3):∃B:ℝ,0<B ∧
    ∀{f K c N per v first:ℕ}(fk:f≤K)(kn:K≤N)(ck:c≤K),v+1≤c→first≤v→∀{r:ℝ},
    0<r→R.family.S.a f≤r→4*(B*r)<R.family.S.a c→
    ∀y:Site (R.family.side f per)×Site (R.family.side f per),WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ y≠0→
    ∀{q e:ℕ}(V:Realm G (q+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (O:Realm G (e+1) Credit.leanC)(seen:O.draws=R.family.path.levels)(D:Fin 3→ℕ)(s:FC)
    (κ:(a:Fin 3)→Knob (D a))(pt:Fin 3→Chamber)(A:Case D),
    let o:=atOrigin y
    let X:=pin R (fk.trans kn) o
    let entry:=tape draw fk o
    let course:=onLevels draw entry
    let root:=WilsonIndependentCollarOrdinaryCruise.address R.family.path.levels course (c-(v+1)) (v+1) (homes (V:=V) entry 0 first (v-first))
    WilsonOriginalObservedRoseProbeRead.filed R D s κ pt (fun j (i:s)=>course j i.val) (fun i:s=>root i.val)
      O seen (profile D s A)=enrolled R D O seen N per c (ck.trans kn) (X 1,X 2) s (ticket D s κ pt A):=by
  obtain ⟨B,hB,rooms⟩:=WilsonOriginalObservedRoseProbeBound.original R φ
  refine ⟨B,hB,?_⟩
  intro f K c N per v first fk kn ck vc old r hr fine room y charged q e V draw O seen D s κ pt A o X entry course root
  have housed:=rooms fk ck hr fine room y charged
  obtain ⟨pathEq,location⟩:=WilsonOriginalObservedRoseProbeRoute.purchased V R draw o fk vc ck old housed
  have centered:X 0=0:=by
    change (R.family.S.toDepth (fk.trans kn) per).embed (atOrigin y 0)=0
    exact (R.family.S.toDepth (fk.trans kn) per).root.map_zero
  have filing:=WilsonOriginalObservedRoseProbePlace.fields R D s κ pt A O seen o fk kn vc ck centered
    (WilsonOriginalTwoFlatRoseCapturedDigits.purchased R o fk kn vc ck housed)
  change WilsonOriginalObservedRoseProbeRead.filed R D s κ pt (fun j (i:s)=>course j i.val) (fun i:s=>root i.val)
    O seen (profile D s A)=_
  rw [show course=WilsonReceivedChronologicalMaterialSites.digits R (pin R fk o) from pathEq,
    show root=_ from location]
  exact filing

end YM.Integration.WilsonOriginalObservedRoseProbeNodes
end
