import YM.Integration.WilsonMovingForkReporterOriginalCouncil
import YM.Integration.WilsonMovingForkReporterRestriction

/-! The appointed heating stamp on a restricted weak table keeps its original data at every cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterNamedInk
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
variable {G:Gauge} {C:Family G} (B:Binding C) (H:C.Makes) (O:HaarBudget G) (J:ChartRatio G)
  {D d n:ℕ} {z:ℝ} (P:Tapes.Panel D) (V:Vane C d)

structure Filed (n:ℕ) (z:ℝ) : Prop where
  aperture : P.arc=V.b
  bill : ∃ l r, ∃ h:LegacyCostSky B J (-3) z (P.bag (C.path.levels.clock.J V.k)) V.k n D O l r,
    ∀ N p (hx:V.k<N), ∃ Ψ, ActumSky B H O J P h Ψ hx ∧
      ∀ a:Fin (d+1), ∃ L:StampDuty C V.k N p a (P.bag (C.path.levels.clock.J V.k)).taylor Ψ
        (P.bag (C.path.levels.clock.J V.k)).era.coast.Q (stamp C.path.levels N p),
        L.T=V.R N p a

theorem issued {I:Type} [Fintype I] (menu:I→Tapes.Panel D) (k:ℕ) (row:ℕ→ℕ→TableL C D)
    (c:ℝ) (paid:PoisedSky menu B H O J n z k row) (a:I) (within:d≤D):
    Filed B H O J (menu a) (vane within (⟨k,(menu a).arc,c,row⟩ : Vane C D)) n z := by
  refine ⟨rfl,?_⟩
  obtain ⟨l,r,h,bill⟩:=paid.supply a
  refine ⟨l,r,h,fun N p live=>?_⟩
  obtain ⟨Ψ,act,all⟩:=bill N p live
  exact ⟨Ψ,act,fun i=>all (slot within i)⟩

theorem narrow {big:Vane C D} (h:d≤D) (income:Filed B H O J P big n z):
    Filed B H O J P (vane h big) n z := by
  obtain ⟨l,r,t,cash⟩:=income.bill
  refine ⟨income.aperture,l,r,t,fun N p live=>?_⟩
  obtain ⟨Ψ,act,all⟩:=cash N p live
  exact ⟨Ψ,act,fun i=>all (slot h i)⟩

theorem capacity (income:Filed B H O J P V n z) (t:ℕ) {need:ℝ}
    (scale:t≤D) (arc:need≤(D:ℝ)+6):
    need≤V.b ∧ t≤(P.bag (C.path.levels.clock.J V.k)).taylor := by
  rw [←income.aperture,P.stable]
  exact ⟨arc.trans P.huge,scale.trans P.enough⟩

end YM.Integration.WilsonMovingForkReporterNamedInk
end
