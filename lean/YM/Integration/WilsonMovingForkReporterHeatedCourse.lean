import YM.Integration.WilsonMovingForkReporterAfterPanel
import YM.Integration.WilsonMovingForkReporterHeatedAperture

/-! The complete growing original reporter course pays every finite genuine two-name menu after its own Taylor order, before its optical date. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterHeatedCourse
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward MergeProof MergeProof.East MergeProof.Accent
open WilsonPhysicalPositionWeakRoofSchedule WilsonPhysicalPositionWeakRoofClock
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}


open WilsonMovingForkReporterHeatedAperture (Test Ready spread)

def ceiling (b:ℕ→Fin 3→ℝ) (d:ℕ) :=
  max (b d 0) (max (b d 1) (b d 2)) + WilsonPhysicalPositionWeakRoofSchedule.width b d

theorem fits (b:ℕ→Fin 3→ℝ) (d:ℕ) (j:Fin 3)
    (x:ℝ) (hx:x∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b d)) :
    b d j+x≤ceiling b d := by
  apply add_le_add _ hx.2
  fin_cases j
  · exact le_max_left .. 
  · exact (le_max_left ..).trans (le_max_right ..)
  · exact (le_max_right ..).trans (le_max_right ..)

variable {C:Family G}

private theorem payroll (H:C.Makes) (simple:G.Simple) (d:ℕ) {n:ℕ} (E:Fin n→WilsonMovingForkReporterHeatedAperture.Test C)
    (lo hi:ℝ) (six:6≤lo) (room:(d:ℝ)+6≤lo) (wide:lo≤hi)
    (P:ℝ→Fin 3→Tapes.Panel d) :
    ∃ k₀:ℕ,∀k≥k₀,∀j:Fin 3,∀s:Fin n,100*((E s).height+1)≤d →
      Ready (E s) (P 0 j).θ lo hi k := by
  classical
  let Seats := {s:Fin n // 100*((E s).height+1)≤d}
  have funds (j:Fin 3) := WilsonMovingForkReporterHeatedAperture.finite
    (ι:=Seats) simple H (fun s=>E s.1) (P 0 j).θ (fun s=>s.2.trans (P 0 j).enough) lo hi six wide
    (fun s i=>by
      have h1 := Tapes.savings C ((E s.1).deg i)
      have paid := s.2
      have scored := (E s.1).capped 1
      have h2 := (E s.1).elevated i
      have pressure : (E s.1).deg i + spread (E s.1) ≤ d := by dsimp [spread]; omega
      have amount : ((E s.1).deg i:ℝ)+(spread (E s.1):ℝ)≤d := by exact_mod_cast pressure
      linarith only [h1,amount,room])
  obtain ⟨k₀,gate⟩ := eventually_atTop.mp (eventually_all.mpr funds)
  exact ⟨k₀,fun k hk j s hs=>gate k hk j ⟨s,hs⟩⟩
variable (R : Run G) (B : Binding R.family) (H : R.family.Makes) (O : HaarBudget G) (J : ChartRatio G)
variable {W : Bid.Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ}
  {L : ∀ N p m : ℕ, m < N → GaugeDoor (R.family.path.rep N p (m+1)) (R.family.path.rep N p m)}
variable {F : Extraction.Order} {S : Table R.family.book} (U : Final R.family F S)
  (a : (Cells.standard R.family).Hierarchy)
variable (simple : G.Simple) (fund : Scrim R.family W u ψ φ δ (fly R.family.path.levels) r L)

open WilsonPhysicalPositionWeakRoofCourse (earned)

include U simple fund

theorem original (b : ℕ → Fin 3 → ℝ) (z : ℕ → ℝ)
    (mono : Monotone (fun d => b d 0)) (base : ∀ (d:ℕ) (i:Fin 3), (d:ℝ)+6 ≤ b d i)
    (room : ∀ d, WilsonPhysicalPositionWeakRoofSchedule.Window B H O J d (z d) (b d) (WilsonPhysicalPositionWeakRoofSchedule.width b d))
    (band : ∀ d i, i ≤ d → generator G i ≤ z d) (actual : ParadeX R.family)
    (count : ℕ → ℕ) (tests:∀d, Fin (count d) → WilsonMovingForkReporterHeatedAperture.Test R.family)
    (needs : ∀ d:ℕ,(ℝ → Fin 3 → Tapes.Panel d) → ℝ → ℕ) :
    ∃ (P : ∀ d, ℝ → Fin 3 → Tapes.Panel d) (c : ℕ → ℝ) (grade : ℕ → ℕ)
      (start : ℕ) (radius : ℝ), 0 < radius ∧
      (∀ k > start, needs (grade k) (P (grade k)) (c (grade k)) ≤ k ∧
        earned (F:=F) R B H O J a b z c P (grade k) k ∧
        ∀ x∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade k)),∀j:Fin 3,
          ∀s:Fin (count (grade k)),100*((tests (grade k) s).height+1)≤grade k →
            Ready (tests (grade k) s) (P (grade k) x j).θ ((grade k:ℝ)+6) (ceiling b (grade k)) k) ∧
      (∀ d, ∀ x ∈ Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b d),
        Checks (b d 0+x) (b d 1+x) (b d 2+x) (c d) (MergeProof.East.trays d) d ∧
        ∀ i, (P d x i).arc=b d i+x ∧ (P d x i).currency=(P d 0 i).currency ∧
          (P d x i).θ=(P d 0 i).θ) ∧
      ∃ date : Ioc (0:ℝ) radius → ℕ,
        (∀ s, start < date s ∧ ∃ x ∈ Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (date s))),
          (s:ℝ) = Station.gap R.family.path.levels (b (grade (date s)) 0+x) (date s)) ∧
        (∀ s v : Ioc (0:ℝ) radius, (s:ℝ) ≤ v → (v:ℝ) ≤ 2*(s:ℝ) →
          date v ≤ date s ∧ date s ≤ date v+1) ∧
        (∀ D : ℕ, ∃ e > (0:ℝ), ∀ s : Ioc (0:ℝ) radius, (s:ℝ) < e → D ≤ grade (date s)) := by

  have windows (d:ℕ):0≤WilsonPhysicalPositionWeakRoofSchedule.width b d := by
    unfold WilsonPhysicalPositionWeakRoofSchedule.width
    linarith only [le_max_left 0 (b (d+1) 0-b d 0)]
  have broad (d:ℕ) : (d:ℝ)+6≤ceiling b d :=
    (base d 0).trans (by simpa using fits b d 0 0 ⟨le_rfl,windows d⟩)
  have invoices (d:ℕ) (P:ℝ→Fin 3→Tapes.Panel d) := payroll H simple d (tests d) ((d:ℝ)+6) (ceiling b d)
    (by linarith only [Nat.cast_nonneg (α:=ℝ) d]) le_rfl (broad d) P
  let total (d:ℕ) (P:ℝ→Fin 3→Tapes.Panel d) (c:ℝ) := max (needs d P c) (invoices d P).choose
  obtain ⟨P,c,grade,start,radius,pos,owed,pins,dates⟩ :=
    WilsonMovingForkReporterAfterPanel.original R B H O J U a simple fund b z mono base room band actual total
  refine ⟨P,c,grade,start,radius,pos,?_,pins,dates⟩
  intro k hk
  obtain ⟨financed,earned_⟩ := owed k hk
  refine ⟨(le_max_left ..).trans financed,earned_,?_⟩
  intro x hx j s h
  rw [(pins (grade k) x hx).2 j |>.2.2]
  exact (invoices (grade k) (P (grade k))).choose_spec k ((le_max_right ..).trans financed) j s h

end YM.Integration.WilsonMovingForkReporterHeatedCourse
end
