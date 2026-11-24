import YM.Integration.WilsonPhysicalStationMixedWickNeighbors
import YM.Integration.WilsonPhysicalStationMixedWickCofinal
/-! Weighted lower probes at the two radii of an original measured pair. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPaired
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonMovingForkReporterFilament WilsonMovingForkReporterBraided
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent


open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
open WilsonMovingForkReporterBasisVisits (Seen)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonMovingForkReporterRestriction (vane)
open WilsonMeasuredPublicEntranceNativeFrame (atRadius)
open WilsonPhysicalStationOwnedTableFaculty (Faculty)
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
    (fac:Facilities R.family f S)(F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}
    (J₀:ℝ→tower S)(H:(Bel R.family.book).Hierarchy){arch:Arch R.family}
    (B:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)
variable (number:ℕ→ℕ)(tests:∀d,Fin (number d)→Axes R.family)
    {radius:ℝ}(cap:Ioc (0:ℝ) radius→ℕ)(V:∀s,Vane R.family (cap s))
    (pan:∀s,Tapes.Panel (cap s))(outer inner:ℕ→Ioc (0:ℝ) radius)
open MS MS.Land MS.Menus MS.Theater XSpace.Structure1 Local.Physical
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedWickNeighbors (month venue Admitted)
open WilsonPhysicalStationMixedWickCofinal (Paid)
open WilsonPhysicalStationMixedWickChamberPorts (quantity ledger)
open WilsonPhysicalStationMixedWickCollege (chosen)
variable (c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)))(J:Scaling S)
    (book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
local notation "M₀" => ledger R (S:=S) book lo hi ax counted more
local notation "AX" => R.family.path.levels

def Read :Prop:=
  ∀(side:Bool)(i:ℕ),
    let room:=chosen R (S:=S) book (lo i) (ax i)
    Tendsto (fun j=>tested AX (c.report (month side j)).b (c.report (month side j)).k room.ξ) atTop (𝓝 room.ξ) ∧
    ∀ᶠj:ℕ in atTop,Paid R F J c.report book lo hi ax i (month side j)

theorem original (fund:Admitted R (f:=f) (l:=l) J₀ H B O χ price cap V pan outer inner
    (quantity R lo hi counted) M₀ c J)(simple:G.Simple)(below:(l:Filter _)≤f.fuse):
    Read R F cap V outer inner c J book lo hi ax:=by
  intro side i
  let z:=venue outer inner c.pick side
  obtain ⟨stock,dates,months,stages,files⟩:=fund side
  obtain ⟨Ml,Bl,_,_,left⟩:=files (lo i)
  obtain ⟨Mr,Br,_,_,right⟩:=files (hi i)
  exact WilsonPhysicalStationMixedWickCofinal.original R F (ℓ:=l) (H:=H) J₀ J c.report book lo hi ax counted more i B O χ price
    (month side) (fun j=>cap (z j)) (fun j=>pan (z j)) (Filter.Eventually.of_forall stock) dates months stages
    simple below ((left.and right).mono fun _ both=>⟨Ml,Bl,Mr,Br,both.1,both.2⟩)

def Listening :Prop:=
  ∀o u:ℕ→Ioc (0:ℝ) radius,Tendsto (fun i=>(o i:ℝ)) atTop (𝓝 0)→
    Tendsto (fun i=>(u i:ℝ)) atTop (𝓝 0)→(∀ᶠi:ℕ in atTop,(u i:ℝ)<(o i:ℝ))→
    (∀i,(o i:ℝ)≤2*(u i:ℝ))→∃w:Pair (fun i=>V (o i)) (fun i=>V (u i)),∃charts:Scaling S,
    WilsonPhysicalStationOwnedTablePair.Held R F (l:=l) J₀ H (arch:=arch) number tests cap V o u w charts ∧
    Admitted R (f:=f) (l:=l) J₀ H B O χ price cap V pan o u (quantity R lo hi counted) M₀ w charts ∧
    Read R F cap V o u w charts book lo hi ax

theorem purchased (grade:ℕ→ℕ)(chart:∀s,grade (V s).k=cap s)
    (mixed:∀s h,∀w:h≤cap s,WilsonMovingForkReporterMixedHouses.Held (f:=f) R B O χ H price
      (quantity R lo hi counted) M₀ (pan s) (vane w (V s)))
    (school:WilsonPhysicalStationOwnedTableSchool.Neighbors R H number tests F (l:=l) (arch:=arch) cap V J₀)
    (simple:G.Simple)(below:(l:Filter _)≤f.fuse):
    Listening R F (l:=l) J₀ H (arch:=arch) B O χ price number tests cap V pan book lo hi ax counted more:=by
  intro o u left right apart compare
  obtain ⟨w,charts,owned⟩:=school o u left right apart compare
  have enrolled:=WilsonPhysicalStationMixedWickNeighbors.original R F J₀ H B O χ price number tests cap V pan o u
    (quantity R lo hi counted) M₀ w charts grade chart mixed owned
  exact ⟨w,charts,owned,enrolled,original R F J₀ H B O χ price cap V pan o u w charts book lo hi ax counted more
    enrolled simple below⟩

end YM.Integration.WilsonPhysicalStationMixedWickPaired
end
