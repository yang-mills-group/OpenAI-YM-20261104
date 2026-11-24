import YM.Integration.WilsonPhysicalPositionWeakRoofCourse

/-! The native optical date is chosen after the actual reporter order and the whole admitted finite family. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterAfterPanel
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward MergeProof MergeProof.East MergeProof.Accent
open WilsonPhysicalPositionWeakRoofSchedule WilsonPhysicalPositionWeakRoofClock
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}

private theorem pocket (r : ℕ → ℝ) (pos : ∀ k, 0 < r k) (n : ℕ) :
    ∃ e > (0:ℝ), ∀ k ≤ n, e ≤ r k := by
  induction n with
  | zero => exact ⟨r 0,pos 0,fun k h => (Nat.eq_zero_of_le_zero h) ▸ le_rfl⟩
  | succ n ih =>
    obtain ⟨e,h,cost⟩ := ih
    refine ⟨min e (r (n+1)),lt_min h (pos _),fun k hk => ?_⟩
    rcases Nat.eq_or_lt_of_le hk with eq|low
    · exact eq ▸ min_le_right .. 
    · exact (min_le_left ..).trans (cost k (by omega))

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
    (needs : ∀ d:ℕ,(ℝ → Fin 3 → Tapes.Panel d) → ℝ → ℕ) :
    ∃ (P : ∀ d, ℝ → Fin 3 → Tapes.Panel d) (c : ℕ → ℝ) (grade : ℕ → ℕ)
      (start : ℕ) (radius : ℝ), 0 < radius ∧
      (∀ k > start, needs (grade k) (P (grade k)) (c (grade k)) ≤ k ∧ earned (F:=F) R B H O J a b z c P (grade k) k) ∧
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
  let B0 (d : ℕ) := b d 0
  have affordable (d : ℕ) : 0 ≤ WilsonPhysicalPositionWeakRoofSchedule.width b d := by
    unfold WilsonPhysicalPositionWeakRoofSchedule.width; linarith only [le_max_left 0 (b (d+1) 0-b d 0)]
  have minimum (d : ℕ) : 5 < b d 0 := by linarith only [base d 0, Nat.cast_nonneg (α:=ℝ) d]
  choose P c checks axes bank using fun d => WilsonMovingForkReporterCouncil.original
    B H O J U a simple fund (band d) (b d) (WilsonPhysicalPositionWeakRoofSchedule.width b d) (minimum d) (affordable d) (room d) actual
  have widthPaid : ∀ᶠ k in atTop, topL R.family.path.levels k ≤ R.family.path.levels.clock.monitor k :=
    (bank 0 0).mono (fun _ board => (board (fun _ => 0) (fun _ => ⟨le_rfl,affordable 0⟩)).choose_spec.1.limit)
  choose entry ready using fun d => eventually_atTop.mp (bank d d)
  have positive (d : ℕ) : 0 ≤ B0 d := (by norm_num : (0:ℝ) ≤ 5).trans (minimum d).le
  have rises : Tendsto B0 atTop atTop := by
    apply tendsto_atTop.2
    intro y
    obtain ⟨D,hd⟩ := exists_nat_gt y
    filter_upwards [eventually_ge_atTop D] with k hk
    have le : (D:ℝ) ≤ k := by exact_mod_cast hk
    exact hd.le.trans (le.trans (by dsimp [B0]; linarith only [base k 0]))
  obtain ⟨t,grade,_,first,grades,_,later,_⟩ := WilsonPhysicalPositionWeakRoofDates.original
    R simple B0 mono positive rises (fun d => max (entry d) (needs d (P d) (c d)))
  obtain ⟨early,can⟩ := eventually_atTop.mp later
  obtain ⟨start,old,radius,rpos,date,seats,neighbor⟩ :=
    WilsonPhysicalPositionWeakRoofCrossings.original R simple B0 t positive first widthPaid early
  refine ⟨P,c,grade,start,radius,rpos,?_,?_,date,?_,neighbor,?_⟩
  · intro k hk
    rcases can k (old.trans hk.le) with ⟨cost,_,_⟩
    exact ⟨(le_max_right ..).trans cost,ready _ _ ((le_max_left ..).trans cost)⟩
  · intro d x hx
    exact ⟨checks d x hx,axes d x hx⟩
  · intro s
    obtain ⟨live,_,_,θ,hθ,gap⟩ := seats s
    obtain ⟨_,lo,up⟩ := can _ (old.trans live.le)
    let x := dial R B0 t (date s) - B0 (grade (date s)) + θ
    have total : b (grade (date s)+1) 0 + 1 ≤ b (grade (date s)) 0 + WilsonPhysicalPositionWeakRoofSchedule.width b (grade (date s)) :=
      next_base b _
    have charge : x ∈ Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (date s))) := by
      dsimp only [x,B0] at *
      exact ⟨by linarith only [lo,hθ.1],by linarith only [up,hθ.2,total]⟩
    refine ⟨live,x,charge,?_⟩
    have exponent : b (grade (date s)) 0 + x = dial R B0 t (date s) + θ := by
      dsimp only [x,B0]
      ring
    rw [exponent]
    exact gap
  · intro D
    obtain ⟨k0,all⟩ := eventually_atTop.mp (grades.eventually_ge_atTop D)
    obtain ⟨e,ep,lower⟩ := pocket (ruler R B0 t) (fun _ => Station.gap_pos ..) k0
    refine ⟨e,ep,fun s low => all _ ?_⟩
    by_contra! small
    exact (not_le_of_gt low) ((lower _ small.le).trans (seats s).2.1)

end YM.Integration.WilsonMovingForkReporterAfterPanel
end
