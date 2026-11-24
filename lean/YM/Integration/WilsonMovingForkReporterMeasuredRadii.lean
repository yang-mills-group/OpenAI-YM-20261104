import YM.Integration.WilsonMovingForkReporterRankFilament

/-! The one original pair of vanes realizing two real radii approaching zero supplies the numerical graded pay and represents the fixed continuum field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterMeasuredRadii
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

def observed (Y:∀ (_:ℕ) (k:{k:ℕ // start<k}),ℕ→ℕ→TableL R.family (grade k))
    (s:Ioc (0:ℝ) radius) (i:ℕ) : Vane R.family (grade (station s)) :=
  WilsonMovingForkReporterOriginalCouncil.reporters R (grade (station s)) (station s) (b (grade (station s)) 0) (c (grade (station s))) (Y i (station s)) (offset s)

private theorem dates (t:ℕ→Ioc (0:ℝ) radius) (vanish:Tendsto (fun i=>(t i:ℝ)) atTop (𝓝 0))
    (large:∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s)) :
    Tendsto (fun i=>grade (station (t i))) atTop atTop ∧ Tendsto (fun i=>(station (t i)).val) atTop atTop := by
  have going:Tendsto (fun i=>grade (station (t i))) atTop atTop := by
    apply tendsto_atTop.mpr
    intro d
    obtain ⟨e,pos,gate⟩:=large d
    exact (vanish.eventually_lt_const pos).mono (fun i hi=>gate (t i) hi)
  refine ⟨going,tendsto_atTop.mpr (fun d=>?_)⟩
  filter_upwards [going.eventually_ge_atTop ((Finset.range d).sup grade+1)] with i high
  by_contra! small
  have bound:=Finset.le_sup (f:=grade) (Finset.mem_range.mpr small)
  omega

theorem original (lead:Leading F J₀) (simple:G.Simple) (bliss:Bliss F l arch H)
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s))
    (large:∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s))
    (outer inner:ℕ→Ioc (0:ℝ) radius) (eligible:∀i,1≤grade (station (inner i)))
    (vanish₁:Tendsto (fun i=>(outer i:ℝ)) atTop (𝓝 0)) (vanish₂:Tendsto (fun i=>(inner i:ℝ)) atTop (𝓝 0))
    (apart:∀ᶠ i in atTop,(inner i:ℝ)<(outer i:ℝ)) :
    ∃ (Y:∀ (_:ℕ) (k:{k:ℕ // start<k}),ℕ→ℕ→TableL R.family (grade k)),
      (∀ (i:ℕ) (k:{k:ℕ // start<k}),PoisedSky (fun j:Fin (grade k+1)×Fin 3=>P (grade k)
        (WilsonMovingForkReporterSharedCutoffs.geometry grade (station ∘ outer) (station ∘ inner)
          (offset ∘ outer) (offset ∘ inner) i k j.1) j.2)
        B R.makes O χ (MergeProof.East.trays (grade k)) (price (grade k)) k (Y i k)) ∧
      let V i:=observed R b c grade station offset Y (outer i) i
      let W i:=observed R b c grade station offset Y (inner i) i
      ∃ pick:Pair V W,∃J:Scaling S,
        Scribe f J pick.report arch F.sector l F.room.kernel H ∧
        (∀i,J.r (2*i)=(outer (pick.pick i):ℝ) ∧ J.r (2*i+1)=(inner (pick.pick i):ℝ)) ∧
        (∀d,∃A B':ℝ,1≤A ∧ 0≤B' ∧ ∀ᶠ i in atTop,
          WilsonMovingForkReporterBothArms.Filed (f:=f) (l:=l) J₀ J pick.report d (2*i) A B' ∧
          WilsonMovingForkReporterBothArms.Filed (f:=f) (l:=l) J₀ J pick.report d (2*i+1) A B') ∧
        ∀i,Kept (f:=f) R B O χ H price count tests
            (P (grade (station (outer (pick.pick i)))) (offset (outer (pick.pick i))) 0) (pick.report (2*i)) ∧
          Kept (f:=f) R B O χ H price count tests
            (P (grade (station (inner (pick.pick i)))) (offset (inner (pick.pick i))) 0) (pick.report (2*i+1)) := by
  obtain ⟨Y,paid,named⟩:=issued outer inner eligible
  refine ⟨Y,paid,?_⟩
  have same (s:Ioc (0:ℝ) radius) (i:ℕ) :(observed R b c grade station offset Y s i).wheel.r=(s:ℝ) :=
    (located s).symm
  have first:=dates grade station outer vanish₁ large
  have second:=dates grade station inner vanish₂ large
  obtain ⟨pick,J,keeper,rows,fields,prices⟩ :=
    WilsonMovingForkReporterRankFilament.original R B O χ H price count tests F J₀
      (fun i=>P (grade (station (outer i))) (offset (outer i)) 0)
      (fun i=>P (grade (station (inner i))) (offset (inner i)) 0) lead simple bliss first.1 second.1
      (V:=fun i=>observed R b c grade station offset Y (outer i) i)
      (W:=fun i=>observed R b c grade station offset Y (inner i) i)
      (by simpa only [same] using vanish₁) (by simpa only [same] using vanish₂)
      (by simpa only [same] using apart) first.2 second.2 (fun i=>(named i).1) (fun i=>(named i).2)
  exact ⟨pick,J,keeper,fun i=>⟨(rows i).1.trans (same _ _),(rows i).2.trans (same _ _)⟩,fields,prices⟩

end YM.Integration.WilsonMovingForkReporterMeasuredRadii
end
