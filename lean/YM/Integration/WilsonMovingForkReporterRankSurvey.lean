import YM.Integration.WilsonMovingForkReporterRankTables

/-! A single original survey finances both physical angular readings at the two selected radii with common tables at coincident dates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterRankSurvey
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



def Books (b:ℕ→Fin 3→ℝ) (z c:ℕ→ℝ) (P:∀d,ℝ→Fin 3→Tapes.Panel d) (grade:ℕ→ℕ)
    (start:ℕ) (radius:ℝ) (station:Ioc (0:ℝ) radius → {k:ℕ // start<k}) (offset:Ioc (0:ℝ) radius→ℝ)
    (count:ℕ→ℕ) (tests:∀d,Fin (count d)→Axes R.family) : Prop :=
  ∀outer inner:ℕ→Ioc (0:ℝ) radius,
   (∀ i, 1≤grade (station (inner i))) →
   ∃Y:∀ (_:ℕ) (k:{k:ℕ // start<k}),ℕ→ℕ→TableL R.family (grade k),
    (∀ (i:ℕ) (k:{k:ℕ // start<k}),PoisedSky (fun j:Fin (grade k+1)×Fin 3=>P (grade k)
      (WilsonMovingForkReporterSharedCutoffs.geometry grade (station ∘ outer) (station ∘ inner)
        (offset ∘ outer) (offset ∘ inner) i k j.1) j.2)
      B R.makes O J (MergeProof.East.trays (grade k)) (z (grade k)) k (Y i k)) ∧
    ∀i,let u:=station (outer i);let v:=station (inner i)
       let A:=WilsonMovingForkReporterOriginalCouncil.reporters R (grade u) u (b (grade u) 0) (c (grade u)) (Y i u) (offset (outer i))
       let A':=WilsonMovingForkReporterOriginalCouncil.reporters R (grade v) v (b (grade v) 0) (c (grade v)) (Y i v) (offset (inner i))
       Named (f:=F) R B O J a z count tests (P (grade u) (offset (outer i)) 0) A ∧
        Named (f:=F) R B O J a z count tests (P (grade v) (offset (inner i)) 0) A'

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
      Books (F:=F) R B O J a b z c P grade start radius station offset count tests := by
  obtain ⟨P,c,grade,start,radius,pos,pay,pins,date,witness,adjacent,cofinal⟩:=
    WilsonMovingForkReporterRankCourse.original R B R.makes O J U a simple fund b z
      mono base room band actual count tests needs
  let station (s:Ioc (0:ℝ) radius):{k:ℕ // start<k}:=⟨date s,(witness s).1⟩
  choose offset legal read using fun s=>(witness s).2
  refine ⟨P,c,grade,start,radius,pos,station,offset,fun s=>⟨legal s,read s⟩,adjacent,cofinal,
    fun k hk=>(pay k hk).1,?_⟩
  intro outer inner live
  exact WilsonMovingForkReporterRankTables.original (f:=F) R B O J a b z c P grade
    (station ∘ outer) (station ∘ inner) (offset ∘ outer) (offset ∘ inner) count tests
    (fun k=>(pay k k.2).2.2.1) (fun k=>(pay k k.2).2.1)
    (fun k x hx s hs=>(pay k k.2).2.2.2 x hx 0 s hs)
    (fun d x hx=>((pins d x hx).2 0).1) (fun i=>legal _) (fun i=>legal _) live

end YM.Integration.WilsonMovingForkReporterRankSurvey
end
