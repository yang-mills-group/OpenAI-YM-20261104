import YM.Integration.WilsonPhysicalStationMixedWickLowerLaw
import YM.Integration.WilsonPhysicalStationMixedWickChamberSales

/-! The complete physical lower solve on one genuinely posted course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickChamberLaw
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


include F in
theorem original (hl:lo i < m+1)(hr:hi i < m+1)
    (bind:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)(P:Tapes.Panel D)
    (held:Held (f:=f) R bind O χ H price (quantity R lo hi counted) (ledger R (S:=S) B lo hi ax counted more) P (V m))
    (active:i≤D)(width:100*(max (lo i) (hi i)+1)≤D):
    0≤ceiling R A₀ B (ax i) room₀ ∧ ∀{Ml Bl Mr Br:ℝ}(_checked:(V m).checked f H m)
    (_fileL:Filed (f:=f) (l:=ℓ) J₀ J V (lo i) m Ml Bl)
    (_fileR:Filed (f:=f) (l:=ℓ) J₀ J V (hi i) m Mr Br)(_simple:G.Simple)(_below:(ℓ:Filter _)≤f.fuse)
    (_hot:1≤T₀)(_late:(room₀).floor≤D)
    (_inGram:tested AX (V m).b (V m).k (room₀).ξ∈(room₀).site)(_fitsGram:FitSky AX (V m).b (V m).k (room₀).ξ)
    {h:ℕ}(le:(lo i)≤h)(_rpos:0<(V m).wheel.r),
    let xG:=(V m).wheel.r • tested AX (V m).b (V m).k (room₀).ξ
    let L:=(WilsonPhysicalStationLowerReceiver.ear R (e:=h) xG ((J.U m (hi i)) z₀)).comp
      (F.sector.derivatives.rise le)
    IsUnit (WilsonPhysicalStationGradedLowerPanel.metered B (lo i) T₀ (frame R (J.U m) B (lo i) (ax i) xG)).det ∧
    (∑j:I,charge R (J.U m) B (lo i) (ax i) xG T₀ Q₀ L j • WilsonPhysicalStationLowerReceiver.ear R (e:=(lo i))
      xG (WilsonPhysicalStationGradedLowerPanel.right R (J.U m) B (lo i) j)=L) ∧
    ∀j:I,‖charge R (J.U m) B (lo i) (ax i) xG T₀ Q₀ L j‖*T₀^Q₀ ≤ ceiling R A₀ B (ax i) room₀*T₀^j.2.1.val:=by
  let n:Fin (D+1):=⟨i,Nat.lt_succ_of_le active⟩
  have lowerWidth:100*(lo i+1)≤D:=(Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_max_left _ _) 1)).trans width
  have award:=WilsonPhysicalStationMixedWickLowerLaw.original R F (ℓ:=ℓ) (H:=H) (D:=D) J₀ J V A₀ hl hr B (ax i) room₀
  refine ⟨award.1,?_⟩
  intro Ml Bl Mr Br checked fileL fileR simple below hot late inGram fitsGram h le rp
  have sale:=WilsonPhysicalStationMixedWickChamberSales.original R (H:=H) B lo hi ax counted more bind O χ price P (V m) checked held n false true b s v hl hr width
  have grams:=WilsonPhysicalStationMixedWickChamberSales.basis R (H:=H) B lo hi ax counted more bind O χ price P (V m) checked held n hl lowerWidth
  exact award.2 checked fileL fileR simple below sale grams hot late inGram fitsGram (room₀).ξ inGram fitsGram le rp

end YM.Integration.WilsonPhysicalStationMixedWickChamberLaw
end
