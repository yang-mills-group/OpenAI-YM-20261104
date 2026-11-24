import YM.Integration.WilsonPhysicalStationBasisSettlement
import YM.Integration.WilsonMovingForkReporterMeasuredPosts
/-! The two real paid reporter dates, degrees and thermal column incomes before the original cutoffs. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisChronology
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


local notation "year" => fun i=>grade (station (outer (pick.pick i)))
local notation "post" => fun i=>(pick.report (2*i)).k
def Bank : Prop:=∀ (i:ℕ) (k:{k:ℕ // start < k}),PoisedSky (fun j:Fin (grade k+1)×Fin 3=>P (grade k)
  (WilsonMovingForkReporterSharedCutoffs.geometry grade (station ∘ outer) (station ∘ inner)
    (offset ∘ outer) (offset ∘ inner) i k j.1) j.2)
  B R.makes O χ (MergeProof.East.trays (grade k)) (price (grade k)) k (Y i k)
theorem grows : Tendsto (year) atTop atTop ∧ Tendsto (post) atTop atTop:=by
  have deep:Tendsto (year) atTop atTop:=by
    refine tendsto_atTop.mpr (fun n=>?_)
    filter_upwards [eventually_ge_atTop n] with i high
    have :=pick.outer i
    omega
  refine ⟨deep,tendsto_atTop.mpr (fun d=>?_)⟩
  filter_upwards [deep.eventually_ge_atTop ((Finset.range d).sup grade+1)] with i high
  rw [(WilsonMovingForkReporterMeasuredPosts.dates R b c grade station offset Y outer inner pick i).1]
  by_contra! small
  have bound:=Finset.le_sup (f:=grade) (Finset.mem_range.mpr small)
  omega

theorem stocked (hg:G.Simple)(bank:Bank R B O χ price P grade station offset Y outer inner):
    ∀ᶠi in atTop, WilsonPhysicalStationBasisClock.Live R ((post) i):=by
  have house:∀ᶠk:ℕ in atTop,topL R.family.path.levels k ≤ R.family.path.levels.clock.monitor k:=by
    filter_upwards [eventually_gt_atTop start] with k hk
    exact (bank 0 ⟨k,hk⟩).limit
  exact (grows R b c grade station offset Y outer inner pick).2.eventually
    (WilsonPhysicalStationBasisClock.original R hg house)

include located in
theorem dates (adjacent:∀ s v:Ioc (0:ℝ) radius,(s:ℝ) ≤ v→(v:ℝ) ≤ 2*(s:ℝ)→
      (station v).val ≤ (station s).val ∧ (station s).val ≤ (station v).val+1)
    (comparable:∀i,(outer i:ℝ) ≤ 2*(inner i:ℝ)) (i h:ℕ):
    let A:=pick.report (2*i);let W:=pick.report (2*i+1)
    (W.k=A.k ∨ W.k=A.k+1) ∧
    (1/2:ℝ)^h ≤ WilsonPhysicalStationMeasuredCash.aperture R A.k W.k h (Station.mag R.family.path.levels A.b A.k)
      (Station.mag R.family.path.levels W.b W.k) ∧
    WilsonPhysicalStationMeasuredCash.aperture R A.k W.k h (Station.mag R.family.path.levels A.b A.k)
      (Station.mag R.family.path.levels W.b W.k) ≤ 1:=by
  dsimp only
  refine ⟨?_, WilsonMovingForkReporterMeasuredPosts.bounded R b c grade station offset Y outer inner pick located comparable h i⟩
  obtain ⟨am,bm⟩:=WilsonMovingForkReporterMeasuredPosts.dates R b c grade station offset Y outer inner pick i
  have sep:(inner (pick.pick i):ℝ)<(outer (pick.pick i):ℝ):=
    lt_of_eq_of_lt (located (inner (pick.pick i)))
      (lt_of_lt_of_eq (pick.separate i) (located (outer (pick.pick i))).symm)
  have :=adjacent (inner (pick.pick i)) (outer (pick.pick i)) sep.le (comparable _)
  omega

end YM.Integration.WilsonPhysicalStationBasisChronology
end
