import YM.Integration.WilsonPhysicalStationMixedWickPaired

/-! All original grades on one school. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickGrades
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

open WilsonPhysicalStationMixedWickPaired (Read)
def entry (e h:ℕ)(a:Axis):ℕ:=Encodable.encode (e,h,a)
def names (i:ℕ):ℕ×ℕ×Axis:=(Encodable.decode (α:=ℕ×ℕ×Axis) i).getD (0,0,0)
def lower (i:ℕ):ℕ:=(names i).1
def upper (i:ℕ):ℕ:=(names i).2.1
def axis (i:ℕ):Axis:=(names i).2.2
theorem booked (e h:ℕ)(a:Axis):names (entry e h a)=(e,h,a):=by
  simp [names,entry]
def All :Prop:=
  ∀(e h:ℕ)(a:Axis),∃i:ℕ,lower i=e ∧ upper i=h ∧ axis i=a ∧ ∀side:Bool,
    let room:=chosen R (S:=S) book (lower i) (axis i)
    Tendsto (fun j=>tested AX (c.report (month side j)).b (c.report (month side j)).k room.ξ) atTop (𝓝 room.ξ) ∧
    ∀ᶠj:ℕ in atTop,Paid R F J c.report book lower upper axis i (month side j)

theorem original (paid:Read R F cap V outer inner c J book lower upper axis):
    All R F cap V outer inner c J book:=by
  intro e h a
  refine ⟨entry e h a,?_,?_,?_,fun side=>paid side (entry e h a)⟩
  · simp only [lower,booked]
  · simp only [upper,booked]
  · simp only [axis,booked]

end YM.Integration.WilsonPhysicalStationMixedWickGrades
end
