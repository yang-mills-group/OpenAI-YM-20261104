import YM.Integration.WilsonPhysicalStationMixedWickChamberLaw
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTolerance
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRegistered
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace
open PhysMS Spec OPE Next.UVStress Trace.Pilot PhysicalNext.Repeat.Legato
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare Next.Rank.Station
open MS MS.Land MS.Menus MS.Theater XSpace.Structure1
open Local.Physical
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationMixedBasisSale (Sold)
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonPhysicalStationMixedWickPivots (reflected)
open WilsonPhysicalStationMixedNamedProbe (coefficient)
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationMixedWickRespondents (balance)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel)
open WilsonPhysicalStationGradedLowerPanel (frame left right)
open Further.CorrectedLift (ladder)
open scoped BigOperators Classical Topology
open WilsonPhysicalStationGradedLowerPanel (cross)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedWickSolvent (Room)
open WilsonPhysicalStationGradedLowerPanel (charge)
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical



open WilsonPhysicalStationMixedWickLowerLaw (ceiling)
open WilsonPhysicalStationMixedWickChamberPorts (quantity ledger contact)
open WilsonPhysicalStationMixedWickCollege (chosen)
open WilsonMovingForkReporterMixedHouses (Held)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)(V:∀m,Vane R.family m)
    {m D:ℕ}(B:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
    (i:ℕ)(b:(R.family.labels.level (hi i)).Index)(s:Signed)(v:Fin 2)
local notation "A₀" => contact R (S:=S) B lo hi ax i false true b s v
local notation "room₀" => chosen R (S:=S) B (lo i) (ax i)
local notation "I" => Glyph B (lo i)
local notation "AX" => R.family.path.levels
local notation "T₀" => (AX).clock.monitor (V m).k
local notation "Q₀" => rank R.family (hi i) b
local notation "z₀" => probe R.family b s v


theorem original (hl:lo i < m+1)(hr:hi i < m+1)
    (bind:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)(P:Tapes.Panel D)
    (held:Held (f:=f) R bind O χ H price (quantity R lo hi counted) (ledger R (S:=S) B lo hi ax counted more) P (V m))
    (active:i≤D)(width:100*(max (lo i) (hi i)+1)≤D):
    0≤ceiling R A₀ B (ax i) room₀ ∧ ∀{Ml Bl Mr Br:ℝ}(_checked:(V m).checked f H m)
    (_fileL:Filed (f:=f) (l:=ℓ) J₀ J V (lo i) m Ml Bl)
    (_fileR:Filed (f:=f) (l:=ℓ) J₀ J V (hi i) m Mr Br)(_simple:G.Simple)(_below:(ℓ:Filter _)≤f.fuse)
    (_hot:1≤T₀)(_late:(room₀).floor≤D)
    (_inGram:tested AX (V m).b (V m).k (room₀).ξ∈(room₀).site)(_fitsGram:FitSky AX (V m).b (V m).k (room₀).ξ)
    {h:ℕ}(le:(lo i)≤h)(_rpos:0<(V m).wheel.r)
    (k:ℕ)(u:(Bel R.family.book).Field h)(c:ℝ)(W:S.Field h)(_lower:W∈LinearMap.range (F.sector.derivatives.rise le))
    (q:ℕ)(eps:ℝ)(fee:I→ℝ),
    let x:=(V m).wheel.r • tested AX (V m).b (V m).k (room₀).ξ
    let L:=WilsonPhysicalStationLowerReceiver.ear R (e:=h) x ((J.U m (hi i)) z₀)
    let X:=J.U k h u-(c:ℂ) • J.U m h u
    ‖L (X-W)‖*T₀^Q₀≤T₀^q*eps→
    (∀j:I,‖WilsonPhysicalStationLowerReceiver.ear R x (WilsonPhysicalStationGradedLowerPanel.right R (J.U m) B (lo i) j)
      (X-W)‖*T₀^j.2.1.val≤T₀^q*fee j)→
    WilsonMeasuredPublicEntranceNativeLowerTolerance.Meter R F B (lo i) (ax i) le (J.U m) x q Q₀ L X
      (eps+∑j:I,ceiling R A₀ B (ax i) room₀*fee j):=by
  obtain ⟨pos,income⟩:=WilsonPhysicalStationMixedWickChamberLaw.original R F J₀ J V B lo hi ax counted more i b s v
    hl hr bind O χ price P held active width
  refine ⟨pos,?_⟩
  intro Ml Bl Mr Br checked filedL filedR simple below hot late inGram fits h le rp k u c W old q eps fee
  dsimp only
  intro head axes
  have law:=income checked filedL filedR simple below hot late inGram fits le rp
  exact ⟨T₀,W,eps,fee,fun _=>ceiling R A₀ B (ax i) room₀,fun _=>pos,
    ⟨hot,Work.A05.smul_conf rp ((room₀).clear inGram),law.1,old,head,axes,law.2.2⟩,le_rfl⟩

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRegistered
end
