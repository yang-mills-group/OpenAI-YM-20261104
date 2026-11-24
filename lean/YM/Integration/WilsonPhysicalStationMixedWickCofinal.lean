import YM.Integration.WilsonPhysicalStationMixedWickLowerLaw
import YM.Integration.WilsonPhysicalStationMixedWickChamberLaw
import YM.Integration.WilsonPhysicalStationMixedWickAttendance

/-! The complete physical lower solve on one genuinely posted course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickCofinal
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
    (B:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
    (i:ℕ)

local notation "room₀" => chosen R (S:=S) B (lo i) (ax i)
local notation "AX" => R.family.path.levels
local notation "M₀" => ledger R (S:=S) B lo hi ax counted more
variable (bind:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)
    {Y:Type*}{stream:Filter Y}(m D:Y→ℕ)(P:∀j,Tapes.Panel (D j))
local notation "held₀" => fun j=>Held (f:=f) R bind O χ H price (quantity R lo hi counted) M₀ (P j) (V (m j))
local notation "x₀" => fun j=>(V (m j)).wheel.r • tested AX (V (m j)).b (V (m j)).k (room₀).ξ

def Paid (m₀:ℕ):Prop:=
  let x:=(V m₀).wheel.r • tested AX (V m₀).b (V m₀).k (room₀).ξ
  let U:=J.U m₀
  let T:=(AX).clock.monitor (V m₀).k
  IsUnit (WilsonPhysicalStationGradedLowerPanel.metered B (lo i) T (frame R U B (lo i) (ax i) x)).det ∧
  ∀(b:(R.family.labels.level (hi i)).Index)(s:Signed)(v:Fin 2){h:ℕ}(le:lo i≤h),
    let slot:=contact R (S:=S) B lo hi ax i false true b s v
    let Q:=rank R.family (hi i) b
    let L:=(WilsonPhysicalStationLowerReceiver.ear R (e:=h) x ((U (hi i)) (probe R.family b s v))).comp
      (F.sector.derivatives.rise le)
    (∑n:Glyph B (lo i),charge R U B (lo i) (ax i) x T Q L n • WilsonPhysicalStationLowerReceiver.ear R
      (e:=lo i) x (WilsonPhysicalStationGradedLowerPanel.right R U B (lo i) n)=L) ∧
    ∀n:Glyph B (lo i),‖charge R U B (lo i) (ax i) x T Q L n‖*T^Q≤
      ceiling R slot B (ax i) room₀*T^n.2.1.val

include F in
theorem original (stock:∀ᶠj in stream,held₀ j)(dates:Tendsto (fun j=>(V (m j)).k) stream atTop)
    (horizons:Tendsto m stream atTop)(stage:Tendsto D stream atTop)(simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)
    (filed:∀ᶠj in stream,∃Ml Bl Mr Br:ℝ,Filed (f:=f) (l:=ℓ) J₀ J V (lo i) (m j) Ml Bl ∧
      Filed (f:=f) (l:=ℓ) J₀ J V (hi i) (m j) Mr Br):
    Tendsto (fun j=>tested AX (V (m j)).b (V (m j)).k (room₀).ξ) stream (𝓝 (room₀).ξ) ∧
    ∀ᶠj in stream,Paid R F J V B lo hi ax i (m j):=by
  let width:=100*(max (lo i) (hi i)+1)
  let wanted:=max i (max (room₀).floor width)
  obtain ⟨pose,calendar⟩:=WilsonPhysicalStationMixedWickAttendance.original R bind O χ price
    (quantity R lo hi counted) M₀ P (fun j=>V (m j)) stock dates stage simple
    (room₀).ξ (room₀).generic (room₀).site (room₀).neighborhood wanted
  refine ⟨pose,?_⟩
  filter_upwards [calendar,horizons.eventually_ge_atTop (max (lo i) (hi i)),filed] with j now cap files
  obtain ⟨sold,hot,enough,rpos,member,fits⟩:=now
  obtain ⟨Ml,Bl,Mr,Br,fileL,fileR⟩:=files
  have act:i≤D j:=(le_max_left ..).trans enough
  have large:(room₀).floor≤D j:=(le_max_left ..).trans ((le_max_right ..).trans enough)
  have ample:width≤D j:=(le_max_right ..).trans ((le_max_right ..).trans enough)
  have he:lo i < m j+1:=Nat.lt_succ_of_le ((le_max_left ..).trans cap)
  have hh:hi i < m j+1:=Nat.lt_succ_of_le ((le_max_right ..).trans cap)
  have funded (b:(R.family.labels.level (hi i)).Index)(s:Signed)(v:Fin 2){h:ℕ}(le:lo i≤h):=
    (WilsonPhysicalStationMixedWickChamberLaw.original R F (ℓ:=ℓ) (H:=H) (D:=D j) J₀ J V B lo hi ax counted more i b s v he hh
      bind O χ price (P j) sold act ample).2 sold.choose fileL fileR simple below hot large member fits le rpos
  let n:Fin (D j+1):=⟨i,Nat.lt_succ_of_le act⟩
  have lowWidth:100*(lo i+1)≤D j:=(Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_max_left _ _) 1)).trans ample
  have grams:=WilsonPhysicalStationMixedWickChamberSales.basis R (H:=H) B lo hi ax counted more
    bind O χ price (P j) (V (m j)) sold.choose sold n he lowWidth
  have near:=WilsonPhysicalStationMixedWickMetered.original R F J₀ J V B (lo i) (ax i) (room₀).site
    (room₀).compact (room₀).clear sold.choose he Ml Bl fileL simple below hot grams (room₀).ξ member fits
  have actual:=(room₀).solvent (J.U (m j)) (x₀ j) _ member ((AX).clock.monitor (V (m j)).k)
    (lt_of_lt_of_le zero_lt_one hot) (D j) large near
  exact ⟨actual.1,fun b s v _ le=>(funded b s v le).2⟩

end YM.Integration.WilsonPhysicalStationMixedWickCofinal
end
