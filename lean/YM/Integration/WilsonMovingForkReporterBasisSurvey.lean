import YM.Integration.WilsonMovingForkReporterRankSurvey
import YM.Integration.WilsonMovingForkReporterBasisTariff

/-! One original survey prices every raw basis direction of the actual two reported measurements. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterBasisSurvey
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward MergeProof MergeProof.East MergeProof.Accent
open WilsonPhysicalPositionWeakRoofSchedule WilsonPhysicalPositionWeakRoofClock
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}
open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
variable (R : Run G) (B : Binding R.family) (H : R.family.Makes) (O : HaarBudget G) (J : ChartRatio G)
variable {W : Bid.Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ}
  {L : ∀ N p m : ℕ, m < N → GaugeDoor (R.family.path.rep N p (m+1)) (R.family.path.rep N p m)}
variable {F : Extraction.Order} {S : Table R.family.book} (U : Final R.family F S)
  (a : (Cells.standard R.family).Hierarchy)
variable (simple : G.Simple) (fund : Scrim R.family W u ψ φ δ (fly R.family.path.levels) r L)

open WilsonPhysicalPositionWeakRoofCourse (earned)



open WilsonMovingForkReporterRankSurvey (Books)
open WilsonMovingForkReporterHeatedCourse (fits ceiling)

def Cleared (b:ℕ→Fin 3→ℝ)(z:ℕ→ℝ)(P:∀d,ℝ→Fin 3→Tapes.Panel d)(grade:ℕ→ℕ)
    (start:ℕ)(count:ℕ→ℕ)(tests:∀d,Fin (count d)→Axes R.family) : Prop :=
  ∀k>start, (grade k:ℝ)+1 ≤ R.family.path.levels.clock.monitor k^(WilsonMovingForkReporterRankCourse.surplus (grade k)) ∧
    ∀x∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade k)),∀j:Fin 3,∀s:Fin (count (grade k)),
      100*((tests (grade k) s).weight+1)≤grade k →
      WilsonMovingForkReporterBasisTariff.Booked R B R.makes O J (tests (grade k) s) (P (grade k) x j) k (z (grade k))

include U simple fund
theorem original (b : ℕ → Fin 3 → ℝ) (z : ℕ → ℝ)
    (mono : Monotone (fun d => b d 0)) (base : ∀ (d:ℕ) (i:Fin 3), (d:ℝ)+6 ≤ b d i)
    (room : ∀ d, WilsonPhysicalPositionWeakRoofSchedule.Window B R.makes O J d (z d) (b d) (WilsonPhysicalPositionWeakRoofSchedule.width b d))
    (band : ∀ d i, i ≤ d → generator G i ≤ z d) (actual : ParadeX R.family)
    (count : ℕ → ℕ) (tests:∀d, Fin (count d) → Axes R.family)
    (needs : ∀ d:ℕ,(ℝ → Fin 3 → Tapes.Panel d) → ℝ → ℕ) :
    ∃ (P : ∀ d, ℝ → Fin 3 → Tapes.Panel d) (c : ℕ → ℝ) (grade : ℕ → ℕ)
      (start : ℕ) (radius : ℝ), 0 < radius ∧
      ∃ (station:Ioc (0:ℝ) radius → {k:ℕ // start<k}) (offset:Ioc (0:ℝ) radius→ℝ),
      (∀ s,offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))) ∧
        (s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s)) ∧
      (∀s v:Ioc (0:ℝ) radius, (s:ℝ)≤v → (v:ℝ)≤2*(s:ℝ) →
        (station v).val≤(station s).val ∧ (station s).val≤(station v).val+1) ∧
      (∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s)) ∧
      (∀k>start,needs (grade k) (P (grade k)) (c (grade k))≤k) ∧
      Cleared R B O J b z P grade start count tests ∧
      Books (F:=F) R B O J a b z c P grade start radius station offset count tests := by
  have windows (d:ℕ):0≤WilsonPhysicalPositionWeakRoofSchedule.width b d := by
    unfold WilsonPhysicalPositionWeakRoofSchedule.width
    linarith only [le_max_left 0 (b (d+1) 0-b d 0)]
  have broad (d:ℕ) : (d:ℝ)+6≤ceiling b d :=
    (base d 0).trans (by simpa using fits b d 0 0 ⟨le_rfl,windows d⟩)
  have invoices (d:ℕ) (P:ℝ→Fin 3→Tapes.Panel d) := WilsonMovingForkReporterBasisTariff.original R B R.makes O J simple fund d (tests d)
    (z d) (ceiling b d) (broad d) (band d) P
  let total (d:ℕ) (P:ℝ→Fin 3→Tapes.Panel d) (c:ℝ) := max (needs d P c) (invoices d P).choose
  obtain ⟨P,c,grade,start,radius,pos,pay,pins,date,witness,adjacent,cofinal⟩:=
    WilsonMovingForkReporterRankCourse.original R B R.makes O J U a simple fund b z
      mono base room band actual count tests total
  let station (s:Ioc (0:ℝ) radius):{k:ℕ // start<k}:=⟨date s,(witness s).1⟩
  choose offset legal read using fun s=>(witness s).2
  refine ⟨P,c,grade,start,radius,pos,station,offset,fun s=>⟨legal s,read s⟩,adjacent,cofinal,
    (fun k hk=>(le_max_left ..).trans (pay k hk).1),?_,?_⟩
  · intro k hk
    refine ⟨(pay k hk).2.1,?_⟩
    intro x hx j s small
    have gate:=(invoices (grade k) (P (grade k))).choose_spec k ((le_max_right ..).trans (pay k hk).1)
    obtain ⟨arc,cash,rate⟩:=(pins (grade k) x hx).2 j
    exact gate j s small _ rate cash (arc.trans_le (fits b (grade k) j x hx))
  intro outer inner live
  exact WilsonMovingForkReporterRankTables.original (f:=F) R B O J a b z c P grade
    (station ∘ outer) (station ∘ inner) (offset ∘ outer) (offset ∘ inner) count tests
    (fun k=>(pay k k.2).2.2.1) (fun k=>(pay k k.2).2.1)
    (fun k x hx s hs=>(pay k k.2).2.2.2 x hx 0 s hs)
    (fun d x hx=>((pins d x hx).2 0).1) (fun i=>legal _) (fun i=>legal _) live

end YM.Integration.WilsonMovingForkReporterBasisSurvey
end
