import YM.Integration.WilsonPhysicalPositionWeakRoofCourse
import YM.Integration.WilsonPhysicalPositionWeakRoofFlagship

/-! Actual original reporter windows on any of the run's selected continuum extractions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionWeakRoofOnRun
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


def Banks (R:Run G) : Prop :=
  ∃(B:Binding R.family), B.prices=R.metals.K ∧
  ∃(O:HaarBudget G)(z:ℕ→ℝ)(b:ℕ→Fin 3→ℝ),
    (∀ i d, i≤d → generator G i≤z d) ∧ Monotone (fun d => b d 0) ∧
    (∀ (d:ℕ)(i:Fin 3),(d:ℝ)+6≤b d i) ∧
    ∀ {index:Extraction.Order}{S:Table R.family.book}, Final R.family index S →
      ∀(a:(Cells.standard R.family).Hierarchy)(needs:ℕ→ℕ),
    ∃ (P : ∀ d, ℝ → Fin 3 → Tapes.Panel d) (c : ℕ → ℝ) (grade : ℕ → ℕ)
      (start : ℕ) (radius : ℝ), 0 < radius ∧
      (∀ k > start, needs (grade k) ≤ k ∧ earned (F:=index) R B R.makes O (Next.Foundations.chart G) a b z c P (grade k) k) ∧
      (∀ d, ∀ x ∈ Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b d),
        Checks (b d 0+x) (b d 1+x) (b d 2+x) (c d) (MergeProof.East.trays d) d ∧
        ∀ i, (P d x i).arc=b d i+x ∧ (P d x i).currency=(P d 0 i).currency ∧
          (P d x i).θ=(P d 0 i).θ) ∧
      ∃ date : Ioc (0:ℝ) radius → ℕ,
        (∀ s, start < date s ∧ ∃ x ∈ Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (date s))),
          (s:ℝ) = Station.gap R.family.path.levels (b (grade (date s)) 0+x) (date s)) ∧
        (∀ s v : Ioc (0:ℝ) radius, (s:ℝ) ≤ v → (v:ℝ) ≤ 2*(s:ℝ) →
          date v ≤ date s ∧ date s ≤ date v+1) ∧
        (∀ D : ℕ, ∃ e > (0:ℝ), ∀ s : Ioc (0:ℝ) radius, (s:ℝ) < e → D ≤ grade (date s))

theorem original (R:Run G) (simple:G.Simple) (roofs:R2I.RG05Joint.ReporterRoofs.Roofed R.kit):Banks R := by
  obtain ⟨O,z,b,income,grow,large,room⟩:=roofs
  have old:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories
    R.doors R.makes R.carries R.books).1
  obtain ⟨_,_,_,scrim,_,B,_,prices,_⟩:=old.reception
  refine ⟨B,prices,O,z,b,income,grow,large,?_⟩
  intro index S F a needs
  have parade:=Next.Rank.East.enclosing R.stories old.freight R.makes
  exact WilsonPhysicalPositionWeakRoofCourse.original R B R.makes O (Next.Foundations.chart G)
    F a simple scrim b z grow large (room R.family rfl B prices R.makes parade) (fun d i hi=>income i d hi) parade needs

end YM.Integration.WilsonPhysicalPositionWeakRoofOnRun
end
