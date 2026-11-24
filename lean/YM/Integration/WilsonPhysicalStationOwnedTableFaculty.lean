import YM.Integration.WilsonPhysicalStationBasisJury
import YM.Integration.WilsonPhysicalStationOwnedTableStanding
/-! The same correction on a presold pair of Vanes for every subsequently admitted finite detector menu. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationOwnedTableFaculty
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
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent


open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
open WilsonMovingForkReporterPostedRanks (paid)
variable {G:Gauge} (R:Run G) (B:Binding R.family) (O:HaarBudget G) (χ:ChartRatio G)
    {f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
    (H:(Bel R.family.book).Hierarchy) {arch:Arch R.family}
    (price:ℕ→ℝ) (count:ℕ→ℕ) (tests:∀d,Fin (count d)→Axes R.family)
    (F:Final R.family f S) (J₀:ℝ→tower S)
local notation "C"=>R.family


variable (school:∀i,Vane R.family i)(age:ℕ→ℕ)(pan:∀i,Tapes.Panel (age i))
open WilsonPhysicalStationFullVote (Head principal)
open WilsonPhysicalStationBasisPortfolio (column)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonMovingForkReporterBasisVisits (Seen)
open WilsonPhysicalStationBasisChronology (Bank)
open Next.Rank.Configuration
variable {T:Campaign R}(L:Pillars R T)(fac:Facilities R.family f S)

open WilsonPhysicalStationBasisBallot (Seats Record)
open WilsonPhysicalStationBasisOwners (Earned)
open WilsonPhysicalStationBasisWallet (vote)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonPhysicalStationFullVote (Head)
open WilsonPhysicalStationBasisJury (Row Menu)
variable {e h:ℕ}{D:Type*}[Fintype D](rows:D→Row R.family h)

open WilsonPhysicalStationOwnedTableStanding (Seat)
def Faculty (J:Scaling S)(horizon:h=e+1):Prop:=
  ∃start:ℕ,∃seats:∀i:ℕ,start ≤ i→Seat R (l:=l) H F J₀ school J horizon i,
    ∀n:ℕ,∀rows:Fin n→Row R.family h,Menu R count tests rows→∀Z ε:ℝ,0 < ε→∀ᶠi:ℕ in atTop,∀live:start ≤ i,∀t:Fin n,
      Record R (ℓ:=l) J₀ J school (seats i live).da (seats i live).db (seats i live).cb (rows t).q (seats i live).w
        (probe R.family (rows t).peer (rows t).turn (rows t).side) (rows t).region Z ε

include L fac in
theorem original (J:Scaling S)(simple:G.Simple)(below:(l:Filter _) ≤ f.fuse)(horizon:h=e+1)
    (deep:Tendsto age atTop atTop)(late:Tendsto (fun i=>(school (2*i)).k) atTop atTop)
    (house:∀ᶠk:ℕ in atTop,MergeProof.East.topL R.family.path.levels k ≤ R.family.path.levels.clock.monitor k)
    (dates:∀i,(school (2*i+1)).k=(school (2*i)).k ∨ (school (2*i+1)).k=(school (2*i)).k+1)
    (inside:∀i,(school (2*i+1)).wheel.r ≤ (school (2*i)).wheel.r)
    (seen:∀i,Seen (f:=f) R B O χ H price count tests (pan i) (school (2*i)))
    (fine:∀i,(school (2*i+1)).checked f H (2*i+1))
    (fields:∃A B':ℝ,1 ≤ A ∧ 0 ≤ B' ∧ ∀ᶠi:ℕ in atTop,
      Filed (f:=f) (l:=l) J₀ J school h (2*i) A B' ∧ Filed (f:=f) (l:=l) J₀ J school h (2*i+1) A B')
    :Faculty R (l:=l) H count tests F J₀ school J horizon:=by
  let blank:Fin 0→Row R.family h:=Fin.elim0
  have empty:Menu R count tests blank:=Filter.Eventually.of_forall (fun _ t=>Fin.elim0 t)
  obtain ⟨start,seats,_⟩:=WilsonPhysicalStationOwnedTableStanding.original R B O χ H price count tests F J₀ school age pan
    L fac blank J simple below horizon deep late house dates inside seen fine empty fields
  refine ⟨start,seats,?_⟩
  intro n rows menu Z ε small
  obtain ⟨A,B',pos,_,papers⟩:=fields
  let W:=‖Further.CorrectedLift.ladder R.family h‖*A
  have Wnon:0 ≤ W:=mul_nonneg (Further.CorrectedLift.ladder R.family h).opNorm_nonneg (zero_le_one.trans pos)
  have source (t:Fin n):=WilsonPhysicalStationOwnedTablePosts.original R B O χ H price count tests school age pan L fac (fun a:Seats R.family h (rows t).q=>a.val) (rows t).peer (rows t).turn (rows t).side
    (fun a => a.property.trans_le (rows t).eligible) (rows t).region (rows t).compact (rows t).separated simple horizon
    deep late house dates inside seen fine (menu.mono fun _ sold=>sold t) (fun _=>W*Z) small
  have all:=Filter.eventually_all.mpr source
  filter_upwards [all,papers] with i funded bought
  intro old t
  let X:=seats i old
  obtain ⟨da',db',ca',cb',pay⟩:=funded t
  apply WilsonPhysicalStationBasisBallot.original R J₀ J school X.da X.db X.cb (rows t).q X.w _ below
  filter_upwards [pay X.w] with N cash
  intro per top ξ inside fit u uu
  exact cash per top (fun j=>X.earned.chart j.val (N,per) top) ξ inside fit
    (fun j=>vote R J₀ J school h (2*i+1) u j.val.val)
    (fun j=>(WilsonPhysicalStationBasisWallet.paid R J₀ J school bought.2 u j.val.val).trans (mul_le_mul_of_nonneg_left uu Wnon))

end YM.Integration.WilsonPhysicalStationOwnedTableFaculty
end
