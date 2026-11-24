import YM.Integration.WilsonPhysicalStationBasisOwners
import YM.Integration.WilsonPhysicalStationBasisWallet
/-! The signed directed finite-profile receipt on the exact elected weak reporters. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisOwnedPosts
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
    {start:ℕ} {radius:ℝ} (station:Ioc (0:ℝ) radius→{k:ℕ // start < k}) (offset:Ioc (0:ℝ) radius→ℝ)

open WilsonMovingForkReporterMeasuredRadii (observed)
variable (Y:∀ (_:ℕ) (k:{k:ℕ // start < k}),ℕ→ℕ→TableL R.family (grade k))
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
variable {e h:ℕ}{I:Type*}[Fintype I](a:I→Head R.family h)(peer:(R.family.labels.level h).Index)
    (s:Signed)(v:Fin 2)(eligible:∀j,rank R.family h (a j).val  ≤  rank R.family h peer)
    (K:Set (Points 2))(compact:IsCompact K)(separated:K ⊆ conf 2)
local notation "X₀" => fun j=>column R (a j) peer s v (eligible j) K compact separated
local notation "ages" => fun i=>grade (station (outer (pick.pick i)))
local notation "z₀" => probe R.family peer s v
local notation "AX₀" => R.family.path.levels


open WilsonPhysicalStationBasisOwners (Earned)
open WilsonPhysicalStationBasisWallet (vote)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonPhysicalStationKineticLimit (transit)

def Paid (J:Scaling S)(horizon:h=e+1)(Z ε:ℝ):Prop:=
  ∀ᶠi:ℕ in atTop,let U:=pick.report (2*i);let V:=pick.report (2*i+1)
  ∃(da:h < 2*i+1)(db:h < (2*i+1)+1)(ca:U.checked f H (2*i))(cb:V.checked f H (2*i+1))
      (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v₀:Head R.family h→R.family.label h)(g:ℝ),
    Earned R F (ℓ:=l) J₀ J pick.report (Nat.le_of_lt_succ da) (Nat.le_of_lt_succ db) ca cb
      (show e ≤ h by omega) w v₀ g ∧
    ∀ᶠN:ℕ in atTop,∀p:ℕ,∀top:V.k < N,∀ξ:Points 2,tested (AX₀) U.b U.k ξ∈K→FitSky (AX₀) U.b U.k ξ→
      ∀u:(Bel R.family.book).Field h,‖u‖ ≤ Z→
      let o:=Station.choose (AX₀) U.b U.k ξ
      let z:=U.wheel.atCut (N,p) ⟨h,da⟩ z₀
      let Γ:=born R h (tested (AX₀) U.b U.k ξ) z₀
      let χ₀ (j:I):ℂ:=signal R N p U.k V.k h (rank R.family h (a j).val)
        (Station.mag (AX₀) U.b U.k) (Station.mag (AX₀) V.b V.k)
      let μ (j:I):ℂ:=vote R J₀ J pick.report h (2*i+1) u (a j).val
      ‖(∑j,μ j*principal R V db (per:=p) cb top w U.k o z (a j))-
        ∑j,μ j*(χ₀ j*Γ (a j).val)‖ ≤ ε
include L fac located in
theorem original (J:Scaling S)(hg:G.Simple)(below:(l:Filter _) ≤ f.fuse)(horizon:h=e+1)
    (bank:Bank R B O χ price P grade station offset Y outer inner)
    (adjacent:∀s v:Ioc (0:ℝ) radius,(s:ℝ)  ≤  v→(v:ℝ)  ≤  2*(s:ℝ)→
      (station v).val  ≤  (station s).val ∧ (station s).val  ≤  (station v).val+1)
    (comparable:∀i,(outer i:ℝ)  ≤  2*(inner i:ℝ))
    (seen:∀i,Seen (f:=f) R B O χ H price count tests
       (P (grade (station (outer (pick.pick i)))) (offset (outer (pick.pick i))) 0) (pick.report (2*i)) ∧
       Seen (f:=f) R B O χ H price count tests
       (P (grade (station (inner (pick.pick i)))) (offset (inner (pick.pick i))) 0) (pick.report (2*i+1)))
    (menu:∀ᶠd:ℕ in atTop,∀j,∃t:Fin (count d),tests d t=(X₀) j)
    (fields:∃A B':ℝ,1 ≤ A ∧ 0 ≤ B' ∧ ∀ᶠi:ℕ in atTop,
      Filed (f:=f) (l:=l) J₀ J pick.report h (2*i) A B' ∧ Filed (f:=f) (l:=l) J₀ J pick.report h (2*i+1) A B')
    (Z:ℝ){ε:ℝ}(small:0 < ε):
    Paid R (l:=l) H F J₀ b c grade station offset Y outer inner pick a peer s v K J horizon Z ε:=by
  unfold Paid
  obtain ⟨A,B',pos,nonneg,papers⟩:=fields
  let W:=‖(Further.CorrectedLift.ladder R.family h)‖*A
  have Wnon:0 ≤ W:=mul_nonneg (Further.CorrectedLift.ladder R.family h).opNorm_nonneg (zero_le_one.trans pos)
  have sale:=WilsonPhysicalStationBasisPosts.original R B O χ H price count tests b c P grade station offset Y outer inner pick located
    L fac a peer s v eligible K compact separated hg horizon bank adjacent comparable seen menu (fun _=>W*Z) small
  have live:=WilsonPhysicalStationBasisChronology.stocked R B O χ price b c P grade station offset Y outer inner pick hg bank
  have late:=(WilsonPhysicalStationBasisChronology.grows R b c grade station offset Y outer inner pick).2
  have ratios:=late.eventually (WilsonPhysicalStationKineticLimit.bracket R hg)
  filter_upwards [sale,papers,live,ratios] with i sale₁ bought warm ratio
  obtain ⟨da,db,ca,cb,cash⟩:=sale₁
  let U:=pick.report (2*i)
  let V:=pick.report (2*i+1)
  have position:=WilsonPhysicalStationBasisChronology.dates R b c grade station offset Y outer inner pick located adjacent comparable i h
  obtain ⟨w,v₀,g,income⟩:=WilsonPhysicalStationBasisOwners.original R L fac F J₀ J pick.report
    (Nat.le_of_lt_succ da) (Nat.le_of_lt_succ db) ca cb hg below bought.2 bought.1 position.1 horizon warm ratio
  refine ⟨da,db,ca,cb,w,v₀,g,income,?_⟩
  filter_upwards [cash w] with N pay
  intro per top ξ inside fit u uu
  apply pay per top (fun j=>income.chart (a j) (N,per) top) ξ inside fit
  intro j
  exact (WilsonPhysicalStationBasisWallet.paid R J₀ J pick.report bought.2 u (a j).val).trans
    (mul_le_mul_of_nonneg_left uu Wnon)

end YM.Integration.WilsonPhysicalStationBasisOwnedPosts
end
