import YM.Integration.WilsonPhysicalStationBasisSettlement
import YM.Integration.WilsonMovingForkReporterBothArms
/-! The actual measured numeric votes from the two original Scribe rows. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisWallet
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


open Further.CorrectedLift (ladder)
open WilsonMovingForkReporterBothArms (Filed)
variable (J:Scaling S)(V:∀i,Vane R.family i)
def vote (h i:ℕ)(u:(Bel R.family.book).Field h):R.family.label h:=
  ladder R.family h ((J.U i h).symm (J₀ (V i).wheel.r h u))
theorem paid {h i:ℕ}{A B':ℝ}(file:Filed (f:=f) (l:=l) J₀ J V h i A B')
    (u:(Bel R.family.book).Field h)(a:(R.family.labels.level h).Index):
    ‖vote R J₀ J V h i u a‖ ≤ (‖ladder R.family h‖*A)*‖u‖:=by
  have full:=((ladder R.family h).le_opNorm ((J.U i h).symm (J₀ (V i).wheel.r h u))).trans
    (mul_le_mul_of_nonneg_left (file u).1 (norm_nonneg _))
  simpa only [vote,mul_assoc] using (norm_le_pi_norm (vote R J₀ J V h i u) a).trans full

theorem both (h:ℕ)(original:∃A B':ℝ,1 ≤ A ∧ 0 ≤ B' ∧ ∀ᶠi:ℕ in atTop,
    Filed (f:=f) (l:=l) J₀ J V h (2*i) A B' ∧ Filed (f:=f) (l:=l) J₀ J V h (2*i+1) A B'):
    ∃c:ℝ,0 ≤ c ∧ ∀ᶠi:ℕ in atTop,∀u:(Bel R.family.book).Field h,∀a:(R.family.labels.level h).Index,
      ‖vote R J₀ J V h (2*i) u a‖ ≤ c*‖u‖ ∧ ‖vote R J₀ J V h (2*i+1) u a‖ ≤ c*‖u‖:=by
  obtain ⟨A,B',pos,_,sold⟩:=original
  refine ⟨‖ladder R.family h‖*A,mul_nonneg ((ladder R.family h).opNorm_nonneg) (zero_le_one.trans pos),?_⟩
  filter_upwards [sold] with i sale
  exact fun u a=>⟨paid R J₀ J V sale.1 u a,paid R J₀ J V sale.2 u a⟩
end YM.Integration.WilsonPhysicalStationBasisWallet
end
