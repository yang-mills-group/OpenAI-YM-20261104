import YM.Integration.WilsonPhysicalStationOwnedTablePair
import YM.Integration.WilsonPhysicalStationMeasuredCash
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedBraidedGeometry
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
    PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open PhysicalNext.Repeat.Legato WilsonMovingForkReporterBraided
open WilsonPhysicalStationMeasuredCash (aperture)
open scoped Classical
variable {G:Gauge}(R:Run G){radius:ℝ}(cap:Ioc (0:ℝ) radius→ℕ)
    (V:∀s,Vane R.family (cap s))(outer inner:ℕ→Ioc (0:ℝ) radius)
    (c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)))
local notation "AX"=>R.family.path.levels
theorem original (located:∀s,(V s).wheel.r=(s:ℝ))
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ) ≤ u→(u:ℝ) ≤ 2*(s:ℝ)→
      (V u).k ≤ (V s).k ∧ (V s).k ≤ (V u).k+1)
    (comparable:∀i,(outer i:ℝ) ≤ 2*(inner i:ℝ))(n h:ℕ):
    let A:=c.report (2*n)
    let B:=c.report (2*n+1)
    (B.k=A.k ∨ B.k=A.k+1) ∧ B.wheel.r ≤ A.wheel.r ∧ A.wheel.r ≤ 2*B.wheel.r ∧
      aperture R A.k B.k h (mag AX A.b A.k) (mag AX B.b B.k)=(B.wheel.r/A.wheel.r)^h ∧
      aperture R A.k B.k h (mag AX A.b A.k) (mag AX B.b B.k) ≤ 1:=by
  dsimp only
  have sep:(inner (c.pick n):ℝ)<(outer (c.pick n):ℝ):=by simpa only [located] using c.separate n
  have phase:=adjacent (inner (c.pick n)) (outer (c.pick n)) sep.le (comparable _)
  rw [even,odd]
  change ((V (inner (c.pick n))).k=(V (outer (c.pick n))).k ∨ (V (inner (c.pick n))).k=(V (outer (c.pick n))).k+1) ∧ _
  have rad:=(c.separate n).le
  refine ⟨by omega,rad,?_,rfl,?_⟩
  · change (V (outer (c.pick n))).wheel.r ≤ 2*(V (inner (c.pick n))).wheel.r
    simpa only [located] using comparable (c.pick n)
  · exact pow_le_one₀ (div_nonneg (V _).wheel.rad.le (V _).wheel.rad.le) ((div_le_one (V _).wheel.rad).2 rad)
end YM.Integration.WilsonPhysicalStationMixedBraidedGeometry
end
