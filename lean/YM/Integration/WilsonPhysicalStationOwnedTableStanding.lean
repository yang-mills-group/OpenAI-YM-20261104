import YM.Integration.WilsonPhysicalStationBasisJury
import YM.Integration.WilsonPhysicalStationOwnedTablePosts
/-! A fixed correction and kinetic limit at each pair of dates before all measurement accuracies. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationOwnedTableStanding
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

structure Seat (J:Scaling S)(horizon:h=e+1)(i:ℕ) where
  da:h ≤ 2*i
  db:h ≤ 2*i+1
  ca:(school (2*i)).checked f H (2*i)
  cb:(school (2*i+1)).checked f H (2*i+1)
  w:Head R.family h→(ℕ×ℕ)→R.family.label h
  v:Head R.family h→R.family.label h
  g:ℝ
  earned:Earned R F (ℓ:=l) J₀ J school da db ca cb (show e ≤ h by omega) w v g

def Standing (J:Scaling S)(horizon:h=e+1):Prop:=
  ∃start:ℕ,∃seats:∀i:ℕ,start ≤ i→Seat R (l:=l) H F J₀ school J horizon i,
    ∀Z ε:ℝ,0 < ε→∀ᶠi:ℕ in atTop,∀live:start ≤ i,∀t:D,
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
    (menu:Menu R count tests rows)
    (fields:∃A B':ℝ,1 ≤ A ∧ 0 ≤ B' ∧ ∀ᶠi:ℕ in atTop,
      Filed (f:=f) (l:=l) J₀ J school h (2*i) A B' ∧ Filed (f:=f) (l:=l) J₀ J school h (2*i+1) A B')
    :Standing R (l:=l) H F J₀ school rows J horizon:=by
  obtain ⟨A,B',pos,_,papers⟩:=fields
  have live:=late.eventually (WilsonPhysicalStationBasisClock.original R simple house)
  have rates:=late.eventually (WilsonPhysicalStationKineticLimit.bracket R simple)
  have elected : ∀ᶠi:ℕ in atTop,Nonempty (Seat R (l:=l) H F J₀ school J horizon i):=by
    filter_upwards [papers,live,rates,eventually_ge_atTop h] with i bought warm ratio ih
    have da:h ≤ 2*i:=by omega
    have db:h ≤ 2*i+1:=by omega
    let U:=school (2*i)
    let V:=school (2*i+1)
    let ca:U.checked f H (2*i):=(seen i).choose
    let cb:V.checked f H (2*i+1):=fine i
    obtain ⟨w,v,g,income⟩:=WilsonPhysicalStationBasisOwners.original R L fac F J₀ J school
      da db ca cb simple below bought.2 bought.1 (dates i) horizon warm ratio
    exact ⟨⟨da,db,ca,cb,w,v,g,income⟩⟩
  obtain ⟨start,good⟩:=eventually_atTop.1 elected
  let seats:=fun i (old:start ≤ i)=>(good i old).some
  refine ⟨start,seats,?_⟩
  intro Z ε small
  let W:=‖Further.CorrectedLift.ladder R.family h‖*A
  have Wnon:0 ≤ W:=mul_nonneg (Further.CorrectedLift.ladder R.family h).opNorm_nonneg (zero_le_one.trans pos)
  have source (t:D):=WilsonPhysicalStationOwnedTablePosts.original R B O χ H price count tests school age pan L fac (fun a:Seats R.family h (rows t).q=>a.val) (rows t).peer (rows t).turn (rows t).side
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

end YM.Integration.WilsonPhysicalStationOwnedTableStanding
end
