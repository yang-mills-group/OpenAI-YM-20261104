import YM.Integration.WilsonPhysicalStationBasisBallot
/-! Joint directed measurements using one earlier-engineering correction and one kinetic limit for every detector. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisJury
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


open WilsonMovingForkReporterRankFilament (Kept)
variable (b:ℕ→Fin 3→ℝ) (c:ℕ→ℝ) (P:∀d,ℝ→Fin 3→Tapes.Panel d) (grade:ℕ→ℕ)
    {start:ℕ} {radius:ℝ} (station:Ioc (0:ℝ) radius→{k:ℕ // start  <  k}) (offset:Ioc (0:ℝ) radius→ℝ)

open WilsonMovingForkReporterMeasuredRadii (observed)
variable (Y:∀ (_:ℕ) (k:{k:ℕ // start  <  k}),ℕ→ℕ→TableL R.family (grade k))
    (outer inner:ℕ→Ioc (0:ℝ) radius)
variable (pick:Pair (fun i=>WilsonMovingForkReporterMeasuredRadii.observed R b c grade station offset Y (outer i) i)
  (fun i=>WilsonMovingForkReporterMeasuredRadii.observed R b c grade station offset Y (inner i) i))
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s))


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
structure Row (family:Family G)(h:ℕ) where
  q:ℕ
  peer:(family.labels.level h).Index
  eligible:q ≤ rank family h peer
  turn:Signed
  side:Fin 2
  region:Set (Points 2)
  compact:IsCompact region
  separated:region⊆conf 2
variable {e h:ℕ}{D:Type*}[Fintype D](rows:D→Row R.family h)
def bill (t:D)(a:Seats R.family h (rows t).q):Axes R.family:=
  column R a.val (rows t).peer (rows t).turn (rows t).side (a.property.trans_le (rows t).eligible)
    (rows t).region (rows t).compact (rows t).separated
def Menu : Prop:=∀ᶠd:ℕ in atTop,∀t:D,∀a:Seats R.family h (rows t).q,∃j:Fin (count d),tests d j=bill R rows t a
def Result (J:Scaling S)(horizon:h=e+1)(Z ε:ℝ):Prop:=
  ∀ᶠi:ℕ in atTop,let U:=pick.report (2*i);let V:=pick.report (2*i+1)
  ∃(da:h ≤ 2*i)(db:h ≤ 2*i+1)(ca:U.checked f H (2*i))(cb:V.checked f H (2*i+1))
      (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)(g:ℝ),
    Earned R F (ℓ:=l) J₀ J pick.report da db ca cb (show e ≤ h by omega) w v g ∧
    ∀t:D,Record R (ℓ:=l) J₀ J pick.report da db cb (rows t).q w
      (probe R.family (rows t).peer (rows t).turn (rows t).side) (rows t).region Z ε

include L fac located in
theorem original (J:Scaling S)(simple:G.Simple)(below:(l:Filter _) ≤ f.fuse)(horizon:h=e+1)
    (bank:Bank R B O χ price P grade station offset Y outer inner)
    (adjacent:∀s v:Ioc (0:ℝ) radius,(s:ℝ)   ≤   v→(v:ℝ)   ≤   2*(s:ℝ)→
      (station v).val   ≤   (station s).val ∧ (station s).val   ≤   (station v).val+1)
    (comparable:∀i,(outer i:ℝ)   ≤   2*(inner i:ℝ))
    (seen:∀i,Seen (f:=f) R B O χ H price count tests
       (P (grade (station (outer (pick.pick i)))) (offset (outer (pick.pick i))) 0) (pick.report (2*i)) ∧
       Seen (f:=f) R B O χ H price count tests
       (P (grade (station (inner (pick.pick i)))) (offset (inner (pick.pick i))) 0) (pick.report (2*i+1)))
    (menu:Menu R count tests rows)
    (fields:∃A B':ℝ,1 ≤ A ∧ 0 ≤ B' ∧ ∀ᶠi:ℕ in atTop,
      Filed (f:=f) (l:=l) J₀ J pick.report h (2*i) A B' ∧ Filed (f:=f) (l:=l) J₀ J pick.report h (2*i+1) A B')
    (Z:ℝ){ε:ℝ}(small:0 < ε):
    Result R (l:=l) H F J₀ b c grade station offset Y outer inner pick rows J horizon Z ε:=by
  unfold Result
  obtain ⟨A,B',pos,_,papers⟩:=fields
  let W:=‖Further.CorrectedLift.ladder R.family h‖*A
  have Wnon:0 ≤ W:=mul_nonneg (Further.CorrectedLift.ladder R.family h).opNorm_nonneg (zero_le_one.trans pos)
  have source (t:D):=WilsonPhysicalStationBasisPosts.original R B O χ H price count tests b c P grade station offset Y outer inner pick
    located L fac (fun a:Seats R.family h (rows t).q=>a.val) (rows t).peer (rows t).turn (rows t).side
    (fun a => a.property.trans_le (rows t).eligible) (rows t).region (rows t).compact (rows t).separated simple horizon
    bank adjacent comparable seen (menu.mono fun _ sold=>sold t) (fun _=>W*Z) small
  have all:=Filter.eventually_all.mpr source
  have live:=WilsonPhysicalStationBasisChronology.stocked R B O χ price b c P grade station offset Y outer inner pick simple bank
  have late:=(WilsonPhysicalStationBasisChronology.grows R b c grade station offset Y outer inner pick).2
  have rates:=late.eventually (WilsonPhysicalStationKineticLimit.bracket R simple)
  filter_upwards [all,papers,live,rates,eventually_ge_atTop h] with i funded bought warm ratio ih
  have da:h ≤ 2*i:=by omega
  have db:h ≤ 2*i+1:=by omega
  let U:=pick.report (2*i)
  let V:=pick.report (2*i+1)
  let ca:U.checked f H (2*i):=(seen i).1.choose
  let cb:V.checked f H (2*i+1):=(seen i).2.choose
  have dates:=WilsonPhysicalStationBasisChronology.dates R b c grade station offset Y outer inner pick located adjacent comparable i h
  obtain ⟨w,v,g,income⟩:=WilsonPhysicalStationBasisOwners.original R L fac F J₀ J pick.report
    da db ca cb simple below bought.2 bought.1 dates.1 horizon warm ratio
  refine ⟨da,db,ca,cb,w,v,g,income,?_⟩
  intro t
  obtain ⟨da',db',ca',cb',pay⟩:=funded t
  apply WilsonPhysicalStationBasisBallot.original R J₀ J pick.report da db cb (rows t).q w _ below
  filter_upwards [pay w] with N cash
  intro per top ξ inside fit u uu
  exact cash per top (fun j=>income.chart j.val (N,per) top) ξ inside fit
    (fun j=>vote R J₀ J pick.report h (2*i+1) u j.val.val)
    (fun j=>(WilsonPhysicalStationBasisWallet.paid R J₀ J pick.report bought.2 u j.val.val).trans (mul_le_mul_of_nonneg_left uu Wnon))

end YM.Integration.WilsonPhysicalStationBasisJury
end
