import YM.Integration.WilsonMovingForkReporterBasisSurvey
import YM.Integration.WilsonPhysicalPositionWeakRoofOnRun

/-! The funded physical Wilson campaign issues the rank-aware survey before choosing its public final field, either scale, or the cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterBasisOnRun
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward MergeProof MergeProof.East MergeProof.Accent
open WilsonPhysicalPositionWeakRoofSchedule WilsonPhysicalPositionWeakRoofClock
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff
open WilsonPhysicalPositionWeakRoofCourse
variable {G:Gauge}


open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankSurvey (Books)

def Banks (R:Run G) : Prop :=
  ∃(B:Binding R.family), B.prices=R.metals.K ∧
  ∃(O:HaarBudget G)(z:ℕ→ℝ)(b:ℕ→Fin 3→ℝ),
    (∀ i d, i≤d → generator G i≤z d) ∧ Monotone (fun d => b d 0) ∧
    (∀ (d:ℕ)(i:Fin 3),(d:ℝ)+6≤b d i) ∧
    ∀ {index:Extraction.Order}{S:Table R.family.book}, Final R.family index S →
      ∀(a:(Cells.standard R.family).Hierarchy)(count:ℕ→ℕ)(tests:∀d,Fin (count d)→Axes R.family)
        (needs:∀d:ℕ,(ℝ→Fin 3→Tapes.Panel d)→ℝ→ℕ),
    ∃ (P : ∀ d, ℝ → Fin 3 → Tapes.Panel d) (c : ℕ → ℝ) (grade : ℕ → ℕ)
      (start : ℕ) (radius : ℝ), 0 < radius ∧
      ∃ (station:Ioc (0:ℝ) radius → {k:ℕ // start<k}) (offset:Ioc (0:ℝ) radius→ℝ),
      (∀ s,offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))) ∧
        (s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s)) ∧
      (∀s v:Ioc (0:ℝ) radius, (s:ℝ)≤v → (v:ℝ)≤2*(s:ℝ) →
        (station v).val≤(station s).val ∧ (station s).val≤(station v).val+1) ∧
      (∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s)) ∧
      (∀k>start,needs (grade k) (P (grade k)) (c (grade k))≤k) ∧
      WilsonMovingForkReporterBasisSurvey.Cleared R B O (Next.Foundations.chart G) b z P grade start count tests ∧
      Books (F:=index) R B O (Next.Foundations.chart G) a b z c P grade start radius station offset count tests

theorem original (R:Run G) (simple:G.Simple) (roofs:R2I.RG05Joint.ReporterRoofs.Roofed R.kit):Banks R := by
  obtain ⟨O,z,b,income,grow,large,room⟩:=roofs
  have old:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories
    R.doors R.makes R.carries R.books).1
  obtain ⟨_,_,_,scrim,_,B,_,prices,_⟩:=old.reception
  refine ⟨B,prices,O,z,b,income,grow,large,?_⟩
  intro index S F a count tests needs
  have parade:=Next.Rank.East.enclosing R.stories old.freight R.makes
  exact WilsonMovingForkReporterBasisSurvey.original R B O (Next.Foundations.chart G)
    F a simple scrim b z grow large (room R.family rfl B prices R.makes parade)
      (fun d i hi=>income i d hi) parade count tests needs

end YM.Integration.WilsonMovingForkReporterBasisOnRun
end
