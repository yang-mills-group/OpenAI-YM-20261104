import YM.Integration.WilsonMovingForkReporterRankSurvey
import YM.Integration.WilsonMovingForkReporterSignedBothArms

/-! The two reporters for one preselected public field family keep the physically measured rank price after the common Scribe restricts their horizons. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterRankFilament
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

def Kept {cap h:ℕ} (P:Tapes.Panel cap) (V:Vane R.family h) : Prop :=
  ∃ hc:V.checked f H h,WilsonMovingForkReporterNamedInk.Filed B R.makes O χ P V (MergeProof.East.trays cap) (price cap) ∧
    ∀s:Fin (count cap), 100*((tests cap s).weight+1)≤cap → ∀hs:(tests cap s).weight≤h,
        paid R V (tests cap s) hs hc cap

theorem narrow {cap h:ℕ} (P:Tapes.Panel cap) (V:Vane R.family cap) (fits:h≤cap)
    (issued:Named (f:=f) R B O χ H price count tests P V) :
    Kept (f:=f) R B O χ H price count tests P (WilsonMovingForkReporterRestriction.vane fits V) := by
  obtain ⟨before,ink,rank⟩:=issued
  refine ⟨WilsonMovingForkReporterRestriction.checked fits V before,
    WilsonMovingForkReporterNamedInk.narrow B R.makes O χ _ fits ink,?_⟩
  intro s deep fits
  exact rank s deep

theorem original {D E:ℕ→ℕ} {V:∀i,Vane C (D i)} {W:∀i,Vane C (E i)}
    (X:∀i,Tapes.Panel (D i)) (Y:∀i,Tapes.Panel (E i))
    (lead:Leading F J₀) (simple:G.Simple) (bliss:Bliss F l arch H)
    (higher:Tendsto D atTop atTop) (lower:Tendsto E atTop atTop)
    (vanish₁:Tendsto (fun i=>(V i).wheel.r) atTop (𝓝 0))
    (vanish₂:Tendsto (fun i=>(W i).wheel.r) atTop (𝓝 0))
    (apart:∀ᶠ i in atTop,(W i).wheel.r < (V i).wheel.r)
    (stages₁:Tendsto (fun i=>(V i).k) atTop atTop) (stages₂:Tendsto (fun i=>(W i).k) atTop atTop)
    (first:∀i,Named (f:=f) R B O χ H price count tests (X i) (V i))
    (second:∀i,Named (f:=f) R B O χ H price count tests (Y i) (W i)):
    ∃ c:Pair V W,∃ J:Scaling S,Scribe f J c.report arch F.sector l F.room.kernel H ∧
      (∀i,J.r (2*i)=(V (c.pick i)).wheel.r ∧ J.r (2*i+1)=(W (c.pick i)).wheel.r) ∧
      (∀d,∃ A B':ℝ,1≤A ∧ 0≤B' ∧ ∀ᶠ i in atTop,
        WilsonMovingForkReporterBothArms.Filed (f:=f) (l:=l) J₀ J c.report d (2*i) A B' ∧
        WilsonMovingForkReporterBothArms.Filed (f:=f) (l:=l) J₀ J c.report d (2*i+1) A B') ∧
      ∀i, Kept (f:=f) R B O χ H price count tests (X (c.pick i)) (c.report (2*i)) ∧
          Kept (f:=f) R B O χ H price count tests (Y (c.pick i)) (c.report (2*i+1)) := by
  obtain ⟨c,J,school,radii,wages⟩:=WilsonMovingForkReporterBothArms.original F J₀ lead R.makes simple bliss
    higher lower vanish₁ vanish₂ apart stages₁ stages₂ (fun i=>(first i).choose) (fun i=>(second i).choose)
  refine ⟨c,J,school,radii,wages,fun i=>?_⟩
  rw [even,odd]
  exact ⟨narrow R B O χ H price count tests _ _ (c.outer i) (first _),
         narrow R B O χ H price count tests _ _ (c.inner i) (second _)⟩

end YM.Integration.WilsonMovingForkReporterRankFilament
end
