import YM.Integration.WilsonMovingForkReporterMeasuredRadii
import YM.Integration.WilsonPhysicalStationMeasuredCash

/-! The physical radii and calendar on the two original reported tables. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterMeasuredPosts
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

include located in
theorem measured (i:ℕ) :
    (pick.report (2*i)).wheel.r=(outer (pick.pick i):ℝ) ∧
    (pick.report (2*i+1)).wheel.r=(inner (pick.pick i):ℝ) := by
  rw [even,odd]
  exact ⟨(located _).symm,(located _).symm⟩

theorem dates (i:ℕ) :
    (pick.report (2*i)).k=(station (outer (pick.pick i))).val ∧
    (pick.report (2*i+1)).k=(station (inner (pick.pick i))).val := by
  rw [even,odd]
  exact ⟨rfl,rfl⟩

theorem floor (needs:∀d:ℕ,(ℝ→Fin 3→Tapes.Panel d)→ℝ→ℕ)
    (bought:∀k>start,needs (grade k) (P (grade k)) (c (grade k))≤k) (i:ℕ) :
    let A:=pick.report (2*i);let E:=pick.report (2*i+1)
    needs (grade A.k) (P (grade A.k)) (c (grade A.k))≤A.k ∧
    needs (grade E.k) (P (grade E.k)) (c (grade E.k))≤E.k := by
  rw [even,odd]
  exact ⟨bought _ (station _).property,bought _ (station _).property⟩

include located in
theorem aperture (h i:ℕ) :
    let A:=pick.report (2*i);let E:=pick.report (2*i+1)
    WilsonPhysicalStationMeasuredCash.aperture R A.k E.k h
      (Station.mag R.family.path.levels A.b A.k) (Station.mag R.family.path.levels E.b E.k) =
      ((inner (pick.pick i):ℝ)/(outer (pick.pick i):ℝ))^h := by
  have r:=measured R b c grade station offset Y outer inner pick located i
  exact congrArg₂ (fun x y:ℝ=>(x/y)^h) r.2 r.1
include located in
theorem bounded (comparable:∀i,(outer i:ℝ)≤2*(inner i:ℝ)) (h i:ℕ) :
    let A:=pick.report (2*i);let E:=pick.report (2*i+1)
    let err:=WilsonPhysicalStationMeasuredCash.aperture R A.k E.k h
      (Station.mag R.family.path.levels A.b A.k) (Station.mag R.family.path.levels E.b E.k)
    (1/2:ℝ)^h ≤ err ∧ err ≤ 1 := by
  dsimp only
  rw [aperture R b c grade station offset Y outer inner pick located]
  have pos := (outer (pick.pick i)).property.1
  have low:(1/2:ℝ)≤(inner (pick.pick i):ℝ)/(outer (pick.pick i):ℝ) :=
    (le_div_iff₀ pos).2 (by linarith only [comparable (pick.pick i)])
  have sep:(inner (pick.pick i):ℝ)<(outer (pick.pick i):ℝ) :=
    lt_of_eq_of_lt (located (inner (pick.pick i)))
      (lt_of_lt_of_eq (pick.separate i) (located (outer (pick.pick i))).symm)
  have upper:(inner (pick.pick i):ℝ)/(outer (pick.pick i):ℝ)≤1 := (div_le_one pos).2 sep.le
  exact ⟨pow_le_pow_left₀ (by norm_num) low h,pow_le_one₀ (div_nonneg (inner _).property.1.le pos.le) upper⟩

end YM.Integration.WilsonMovingForkReporterMeasuredPosts
end
