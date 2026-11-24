import YM.Integration.WilsonMovingForkReporterNamedInk
import YM.Integration.WilsonPhysicalPositionWeakRoofCourse

/-! The appointed heating stamp on a restricted weak table keeps its original data at every cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterSuppliedBatch
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open YM.Integration.WilsonLimitConstruction PhysicalNext.Repeat.Legato
open WilsonMovingForkReporterNamedInk
variable {G:Gauge} (R:Run G) (B:Binding R.family) (H:R.family.Makes) (O:HaarBudget G) (J:ChartRatio G)
  {f:Extraction.Order} (a:(Cells.standard R.family).Hierarchy)
  (b:ℕ→Fin 3→ℝ) (z c:ℕ→ℝ) (P:∀d,ℝ→Fin 3→Tapes.Panel d)

theorem original (d k:ℕ) (x:Fin (d+1)→ℝ)
    (range:∀i,x i∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b d))
    (aligned:∀i,(P d (x i) 0).arc=b d 0+x i)
    (earned:WilsonPhysicalPositionWeakRoofCourse.earned (F:=f) R B H O J a b z c P d k) :
    ∃Y:ℕ→ℕ→TableL R.family d,
      PoisedSky (fun j:Fin (d+1)×Fin 3=>P d (x j.1) j.2) B H O J (MergeProof.East.trays d) (z d) k Y ∧
      ∀i, let V:=WilsonMovingForkReporterOriginalCouncil.reporters R d k (b d 0) (c d) Y (x i)
          V.checked f a d ∧ Filed B H O J (P d (x i) 0) V (MergeProof.East.trays d) (z d) :=by
  obtain ⟨Y,board,prices⟩:=earned x range
  refine ⟨Y,board,fun i=>⟨prices i,aligned i,?_⟩⟩
  obtain ⟨l,r,t,full⟩:=board.supply (i,0)
  exact ⟨l,r,t,full⟩

end YM.Integration.WilsonMovingForkReporterSuppliedBatch
end
