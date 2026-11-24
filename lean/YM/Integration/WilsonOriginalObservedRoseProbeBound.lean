import YM.Integration.WilsonOriginalObservedRoseProbeRoute
import YM.Integration.WilsonOriginalHeterogeneousStopSites
import YM.Integration.WilsonThermometerRegisteredTripleRoom
/-! Compactness of the actual signed test gives one pre-cutoff room at the physical capture scale for every relative cell of nonzero signed mass. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseProbeBound
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

open WilsonThermometerAlignedCells (atOrigin placedAt)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonReceivedChronologicalMaterialSites (physical)
open Trace.Pilot Next.UVStress
variable {G:Gauge}(R:Run G)

theorem original (φ:Test 3):
    ∃B:ℝ,0<B ∧ ∀{f K c per:ℕ}(fk:f≤K)(ck:c≤K){r:ℝ},0<r→R.family.S.a f≤r→
    4*(B*r)<R.family.S.a c→∀y:Site (R.family.side f per)×Site (R.family.side f per),
    WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ y≠0→
    ∀j,∀jc:j≤c,∀i,physical R (pin R fk (atOrigin y)) (jc.trans ck) i=0:=by
  obtain ⟨M,shape⟩:=WilsonCapturedPrimaryCaptureRoom.shape φ
  refine ⟨(M:ℝ)+1,by positivity,?_⟩
  intro f K c per fk ck r hr mesh room y active j jc i
  obtain ⟨b,x,live,location⟩:=WilsonThermometerAlignedCells.supported (R:=R) r (f,per) φ active
  let S₀:=R.family.S
  let u:=address (S₀.a f) (r • x)
  have size (v:Fin 3)(a:Axis):|S₀.a f*(u v a:ℝ)|≤((M:ℝ)+1)*r:=by
    have t:=(Extraction.tile_bounds (S₀.a_pos f) ((r • x) v a) (u v a)).mp rfl
    change S₀.a f*((u v a:ℝ)-1)<r*x v a ∧ r*x v a≤S₀.a f*(u v a:ℝ) at t
    have head:|S₀.a f*(u v a:ℝ)|≤|r*x v a|+S₀.a f:=by
      rw [abs_le];exact ⟨by linarith [neg_abs_le (r*x v a),t.2],by linarith [le_abs_self (r*x v a),t.1]⟩
    rw [abs_mul r (x v a),abs_of_pos hr] at head
    have cap:=mul_le_mul_of_nonneg_left (shape x live v a) hr.le
    nlinarith only [head,cap,mesh]
  have spot (v:Fin 3):wrap (S₀.side f per) (u v)=atOrigin y v+b:=congrFun location v
  have offset:atOrigin y i=wrap (S₀.side f per) (u i-u 0):=by
    rw [map_sub,spot i,spot 0]
    simp [atOrigin]
  let g:=S₀.toDepth fk per
  change (S₀.toDepth (jc.trans ck) per).parent (g.embed (atOrigin y i))=0
  rw [offset,g.embed_wrap]
  apply WilsonOriginalHeterogeneousStopSites.parent
  intro a
  have scale:S₀.a K*(g.count.val:ℝ)=S₀.a f:=S₀.embeds_scale g
  change 2*|S₀.a K*((g.count.val • (u i a-u 0 a):ℤ):ℝ)|<S₀.a j
  rw [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,←mul_assoc,scale,Int.cast_sub,mul_sub]
  have points:=abs_sub (S₀.a f*(u i a:ℝ)) (S₀.a f*(u 0 a:ℝ))
  have final:=room.trans_le (S₀.strictAnti.antitone jc)
  linarith only [points,size i a,size 0 a,final]

end YM.Integration.WilsonOriginalObservedRoseProbeBound
end
