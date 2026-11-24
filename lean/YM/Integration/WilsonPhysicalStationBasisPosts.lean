import YM.Integration.WilsonPhysicalStationBasisChronology
/-! The signed directed finite-profile receipt on the exact elected weak reporters. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisPosts
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
    {start:ℕ} {radius:ℝ} (station:Ioc (0:ℝ) radius→{k:ℕ // start<k}) (offset:Ioc (0:ℝ) radius→ℝ)

open WilsonMovingForkReporterMeasuredRadii (observed)
variable (Y:∀ (_:ℕ) (k:{k:ℕ // start<k}),ℕ→ℕ→TableL R.family (grade k))
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
    (s:Signed)(v:Fin 2)(eligible:∀j,rank R.family h (a j).val ≤ rank R.family h peer)
    (K:Set (Points 2))(compact:IsCompact K)(separated:K ⊆ conf 2)
local notation "X₀" => fun j=>column R (a j) peer s v (eligible j) K compact separated
local notation "ages" => fun i=>grade (station (outer (pick.pick i)))
local notation "z₀" => probe R.family peer s v
local notation "AX₀" => R.family.path.levels

include L fac located in
theorem original (hg:G.Simple)(horizon:h=e+1)
    (bank:Bank R B O χ price P grade station offset Y outer inner)
    (adjacent:∀s v:Ioc (0:ℝ) radius,(s:ℝ) ≤ v→(v:ℝ) ≤ 2*(s:ℝ)→
      (station v).val ≤ (station s).val ∧ (station s).val ≤ (station v).val+1)
    (comparable:∀i,(outer i:ℝ) ≤ 2*(inner i:ℝ))
    (seen:∀i,Seen (f:=f) R B O χ H price count tests
       (P (grade (station (outer (pick.pick i)))) (offset (outer (pick.pick i))) 0) (pick.report (2*i)) ∧
       Seen (f:=f) R B O χ H price count tests
       (P (grade (station (inner (pick.pick i)))) (offset (inner (pick.pick i))) 0) (pick.report (2*i+1)))
    (menu:∀ᶠd:ℕ in atTop,∀j,∃t:Fin (count d),tests d t=(X₀) j)
    (M:I→ℝ){ε:ℝ}(small:0 < ε):
    ∀ᶠi:ℕ in atTop,let U:=pick.report (2*i);let V:=pick.report (2*i+1)
    ∃(da:h < 2*i+1)(db:h < (2*i+1)+1)(ca:U.checked f H (2*i))(cb:V.checked f H (2*i+1)),
    ∀w:Head R.family h→(ℕ×ℕ)→R.family.label h,∀ᶠN:ℕ in atTop,∀p:ℕ,∀top:V.k < N,
    (∀j,WilsonPhysicalStationBasisWindow.Filed R ((X₀) j) da db U V (e:=e) (p:=p) ca cb top (w (a j) (N,p)))→
    ∀ξ:Points 2,tested (AX₀) U.b U.k ξ∈K→FitSky (AX₀) U.b U.k ξ→
    ∀μ:I→ℂ,(∀j,‖μ j‖ ≤ M j)→
      let o:=Station.choose (AX₀) U.b U.k ξ
      let z:=U.wheel.atCut (N,p) ⟨h,da⟩ z₀
      let Γ:=born R h (tested (AX₀) U.b U.k ξ) z₀
      let χ₀ (j:I):ℂ:=signal R N p U.k V.k h (rank R.family h (a j).val)
        (Station.mag (AX₀) U.b U.k) (Station.mag (AX₀) V.b V.k)
      ‖(∑j,μ j*principal R V db (per:=p) cb top w U.k o z (a j))-
        ∑j,μ j*(χ₀ j*Γ (a j).val)‖ ≤ ε:=by
  obtain ⟨deep,late⟩:=WilsonPhysicalStationBasisChronology.grows R b c grade station offset Y outer inner pick
  have sale:=WilsonPhysicalStationBasisSettlement.before R hg (X₀) deep late M small
  have live:=WilsonPhysicalStationBasisChronology.stocked R B O χ price b c P grade station offset Y outer inner pick hg bank
  filter_upwards [eventually_ge_atTop h,live,sale,deep.eventually menu,deep.eventually_ge_atTop (100*(h+1))] with i room hot tariff tags large
  let U:=pick.report (2*i)
  let V:=pick.report (2*i+1)
  have da:h < 2*i+1:=by omega
  have db:h < (2*i+1)+1:=by omega
  let ca:U.checked f H (2*i):=(seen i).1.choose
  let cb:V.checked f H (2*i+1):=(seen i).2.choose
  refine ⟨da,db,ca,cb,?_⟩
  intro w
  have position:=WilsonPhysicalStationBasisChronology.dates R b c grade station offset Y outer inner pick
    located adjacent comparable i h
  have slots (j:I):WilsonMovingForkReporterBasisRows.Sold R U ((X₀) j) (by change h ≤ 2*i;omega) ((ages) i) ca:=
    WilsonPhysicalStationBasisSettlement.seated R B O χ H price count tests _ U (seen i).1 ca ((X₀) j) large
      (by change h ≤ 2*i;omega) (tags j)
  have heard:=WilsonPhysicalStationBasisPortfolio.original R L fac da db U V a peer s v eligible K compact separated
    hg ca cb position.1 horizon hot position.2.2 slots w
  filter_upwards [heard] with N heardN
  intro per top stamped ξ inside fit μ raw
  exact (heardN per top stamped ξ inside fit μ).trans (tariff μ raw)

end YM.Integration.WilsonPhysicalStationBasisPosts
end
