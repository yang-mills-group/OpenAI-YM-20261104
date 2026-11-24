import YM.Integration.WilsonMovingForkReporterNamedInk
import YM.Integration.WilsonPhysicalStationMixedWickSites

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterMixedFitting
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open YM.Integration.WilsonLimitConstruction PhysicalNext.Repeat.Legato
open WilsonMovingForkReporterRestriction
open Next.Rank.Ribbon

open WilsonMovingForkReporterNamedInk (Filed)
variable {G:Gauge}{C:Family G}{B:Binding C}{H:C.Makes}{O:HaarBudget G}{J:ChartRatio G}

theorem enrolled {D h n:ℕ}{z:ℝ}{P:Tapes.Panel D}{V:Vane C h}(ink:Filed B H O J P V n z):
    1≤V.b ∧ AllowedSky C.path.levels V.b V.k := by
  obtain ⟨_,_,stored,_⟩:=ink.bill
  have large:=P.huge
  rw [←ink.aperture]
  refine ⟨by linarith only [large,Nat.cast_nonneg (α:=ℝ) D],?_⟩
  rw [←P.factor (C.path.levels.clock.J V.k)]
  exact stored.age.allot.permitted

theorem original {I:Type*}{atI:Filter I}{d h n:I→ℕ}{z:I→ℝ}(P:∀i,Tapes.Panel (d i))(V:∀i,Vane C (h i))
    (income:∀ᶠi in atI,Filed B H O J (P i) (V i) (n i) (z i))(late:Tendsto (fun i=>(V i).k) atI atTop)
    (simple:G.Simple){m:ℕ}(x:Points m)(inside:x∈generic m):
    Tendsto (fun i=>tested C.path.levels (V i).b (V i).k x) atI (𝓝 x) ∧ ∀ᶠi in atI,FitSky C.path.levels (V i).b (V i).k x := by
  have legit:=income.mono (fun i print=>enrolled print)
  obtain ⟨limit,allowed⟩:=WilsonPhysicalStationMixedWickSites.original C.path.levels simple x inside
    (fun i=>(V i).k) (fun i=>(V i).b) late (legit.mono fun _ h=>h.1)
  exact ⟨limit,(allowed.and legit).mono (fun _ h=>h.1 h.2.2)⟩

end YM.Integration.WilsonMovingForkReporterMixedFitting
end
