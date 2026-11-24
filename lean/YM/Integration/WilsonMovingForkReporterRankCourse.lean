import YM.Integration.WilsonMovingForkReporterHeatedCourse
import YM.Integration.WilsonMovingForkReporterRankMarket
import YM.Integration.WilsonMovingForkReporterFixedRanks

/-! The actual original field measurements pay the graded two-point loss on all short-window stations of a common optical election. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterRankCourse
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
open WilsonMovingForkReporterHeatedCourse (fits ceiling)
open WilsonMovingForkReporterRankMarket (amount)
variable (R : Run G) (B : Binding R.family) (H : R.family.Makes) (O : HaarBudget G) (J : ChartRatio G)
variable {W : Bid.Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ}
  {L : ∀ N p m : ℕ, m < N → GaugeDoor (R.family.path.rep N p (m+1)) (R.family.path.rep N p m)}
variable {F : Extraction.Order} {S : Table R.family.book} (U : Final R.family F S)
  (a : (Cells.standard R.family).Hierarchy)
variable (simple : G.Simple) (fund : Scrim R.family W u ψ φ δ (fly R.family.path.levels) r L)

open WilsonPhysicalPositionWeakRoofCourse (earned)


def surplus (d:ℕ) : ℝ := 1/(16*(MergeProof.East.trays d:ℝ))

def reached {d:ℕ} (A:Axes R.family) (P:Tapes.Panel d) (k:ℕ) (z:ℝ) : Prop :=
  let E:=WilsonMovingForkReporterFixedRanks.test A
  WilsonReporterWeightedRankEpoch.Result (K:=E.support) (u:=MergeProof.East.trays d)
    B H O J E.raw P E.rank k (amount E) z

include simple fund in
private theorem payroll (d:ℕ) {n:ℕ} (roster:Fin n→Axes R.family) (z upper:ℝ)
    (wide:(d:ℝ)+6≤upper) (band:∀i,i≤d → generator G i≤z) (P:ℝ→Fin 3→Tapes.Panel d) :
    ∃ k₀:ℕ,∀k≥k₀, (d:ℝ)+1 ≤ (R.family.path.levels.clock.monitor k)^(surplus d) ∧
      ∀j:Fin 3,∀s:Fin n,100*((roster s).weight+1)≤d → ∀pan:Tapes.Panel d,
        pan.θ=(P 0 j).θ → pan.currency=(P 0 j).currency → pan.arc≤upper →
          reached R B H O J (roster s) pan k z := by
  classical
  let Seats:={s:Fin n // 100*((roster s).weight+1)≤d}
  have funds (j:Fin 3) (s:Seats) :
      ∀ᶠ k:ℕ in atTop,∀pan:Tapes.Panel d,pan.θ=(P 0 j).θ → pan.currency=(P 0 j).currency →
        pan.arc≤upper → reached R B H O J (roster s.1) pan k z := by
    have active:=s.2
    have fitsD : (roster s.1).weight≤d := by omega
    exact WilsonMovingForkReporterRankMarket.original B H simple fund O J
      (WilsonMovingForkReporterFixedRanks.test (roster s.1)) d (MergeProof.East.trays d) (P 0 j).θ
      (P 0 j).currency z upper active (active.trans (P 0 j).enough) (Nat.le_add_left ..) wide
      (fun _=>band _ fitsD) (WilsonMovingForkReporterFixedRanks.portable (roster s.1) fitsD)
  have pos:0<surplus d := by unfold surplus MergeProof.East.trays;positivity
  have ripe:∀ᶠ k:ℕ in atTop, (d:ℝ)+1≤(R.family.path.levels.clock.monitor k)^(surplus d) :=
    (Station.mag_rate R.family.path.levels simple pos).eventually_ge_atTop _
  obtain ⟨k₀,gate⟩:=eventually_atTop.mp (ripe.and (eventually_all.mpr (fun j=>eventually_all.mpr (funds j))))
  exact ⟨k₀,fun k hk=>⟨(gate k hk).1,fun j s hs=>(gate k hk).2 j ⟨s,hs⟩⟩⟩

include U simple fund
theorem original (b : ℕ → Fin 3 → ℝ) (z : ℕ → ℝ)
    (mono : Monotone (fun d => b d 0)) (base : ∀ (d:ℕ) (i:Fin 3), (d:ℝ)+6 ≤ b d i)
    (room : ∀ d, WilsonPhysicalPositionWeakRoofSchedule.Window B H O J d (z d) (b d) (WilsonPhysicalPositionWeakRoofSchedule.width b d))
    (band : ∀ d i, i ≤ d → generator G i ≤ z d) (actual : ParadeX R.family)
    (count : ℕ → ℕ) (tests:∀d, Fin (count d) → Axes R.family)
    (needs : ∀ d:ℕ,(ℝ → Fin 3 → Tapes.Panel d) → ℝ → ℕ) :
    ∃ (P : ∀ d, ℝ → Fin 3 → Tapes.Panel d) (c : ℕ → ℝ) (grade : ℕ → ℕ)
      (start : ℕ) (radius : ℝ), 0 < radius ∧
      (∀ k > start, needs (grade k) (P (grade k)) (c (grade k)) ≤ k ∧
        (grade k:ℝ)+1 ≤ (R.family.path.levels.clock.monitor k)^(surplus (grade k)) ∧
        earned (F:=F) R B H O J a b z c P (grade k) k ∧
        ∀ x∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade k)),∀j:Fin 3,
          ∀s:Fin (count (grade k)),100*((tests (grade k) s).weight+1)≤grade k →
            reached R B H O J (tests (grade k) s) (P (grade k) x j) k (z (grade k))) ∧
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
  have invoices (d:ℕ) (P:ℝ→Fin 3→Tapes.Panel d) := payroll R B H O J simple fund d (tests d)
    (z d) (ceiling b d) (broad d) (band d) P
  let total (d:ℕ) (P:ℝ→Fin 3→Tapes.Panel d) (c:ℝ) := max (needs d P c) (invoices d P).choose
  obtain ⟨P,c,grade,start,radius,pos,owed,pins,dates⟩ :=
    WilsonMovingForkReporterAfterPanel.original R B H O J U a simple fund b z mono base room band actual total
  refine ⟨P,c,grade,start,radius,pos,?_,pins,dates⟩
  intro k hk
  obtain ⟨financed,earned_⟩ := owed k hk
  have charged := (invoices (grade k) (P (grade k))).choose_spec k ((le_max_right ..).trans financed)
  refine ⟨(le_max_left ..).trans financed,charged.1,earned_,?_⟩
  intro x hx j s cap
  obtain ⟨arc,cash,rate⟩:=(pins (grade k) x hx).2 j
  exact charged.2 j s cap _ rate cash (arc.trans_le (fits b (grade k) j x hx))

end YM.Integration.WilsonMovingForkReporterRankCourse
end
