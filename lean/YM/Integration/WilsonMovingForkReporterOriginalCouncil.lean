import YM.Integration.WilsonMovingForkReporterCouncil
import YM.Integration.WilsonThermometerOriginalPanelDates

/-! Grouped weak reporters on the original Wilson family and its registered table. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterOriginalCouncil
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open YM.Integration.WilsonLimitConstruction PhysicalNext.Repeat.Legato
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  (H:(Cells.standard R.family).Hierarchy) (O:HaarBudget G) (J:ChartRatio G)
  (z:ℕ→ℝ) (b:ℕ→Fin 3→ℝ) (width:ℕ→ℝ)

def reporters (d k:ℕ) (base c:ℝ) (Y:ℕ→ℕ→TableL R.family d) (s:ℝ):Vane R.family d :=
  ⟨k,base+s,c,Y⟩

include F simple in
theorem original (income:∀u d,u≤d → generator G u≤z d)
    (base:∀d,5<b d 0) (positive:∀d,0≤width d)
    (cover:∀B:Binding R.family,B.prices=R.metals.K→∀d,
      WilsonPhysicalPositionWeakRoofSchedule.Window B R.makes O J d (z d) (b d) (width d)) :
    ∃ B:Binding R.family,B.prices=R.metals.K ∧ ∀d,
      ∃ P:ℝ→Fin 3→Tapes.Panel d,∃ c,
        (∀s∈Icc 0 (width d),Checks (b d 0+s) (b d 1+s) (b d 2+s) c (MergeProof.East.trays d) d) ∧
        (∀s∈Icc 0 (width d),∀i,(P s i).arc=b d i+s ∧
          (P s i).currency=(P 0 i).currency ∧ (P s i).θ=(P 0 i).θ) ∧
        ∀ n:ℕ,∀ᶠ k in atTop,∀x:Fin (n+1)→ℝ,(∀i,x i∈Icc 0 (width d))→
          ∃ Y,PoisedSky (fun j:Fin (n+1)×Fin 3 =>P (x j.1) j.2) B R.makes O J
              (MergeProof.East.trays d) (z d) k Y ∧
            ∀i,let V:=reporters R d k (b d 0) c Y (x i)
               V.checked f H d ∧ V.R=Y ∧ V.k=k ∧ V.b=b d 0+x i := by
  have old:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories
    R.doors R.makes R.carries R.books).1
  obtain ⟨_,_,_,scrim,_,B,_,prices,_⟩:=old.reception
  refine ⟨B,prices,fun d=>?_⟩
  obtain ⟨P,c,checks,axes,book⟩ := WilsonMovingForkReporterCouncil.original B R.makes O J
    F H simple scrim (fun u hu=>income u d hu) (b d) (width d) (base d) (positive d)
    (cover B prices d) (Next.Rank.East.enclosing R.stories old.freight R.makes)
  refine ⟨P,c,checks,axes,fun n=>?_⟩
  filter_upwards [book n] with k all x range
  obtain ⟨Y,paid,fares⟩:=all x range
  exact ⟨Y,paid,fun i=>⟨fares i,rfl,rfl,rfl⟩⟩

end YM.Integration.WilsonMovingForkReporterOriginalCouncil
end
