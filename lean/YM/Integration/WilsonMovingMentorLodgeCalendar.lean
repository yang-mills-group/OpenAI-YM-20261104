import YM.Integration.WilsonMovingMentorLodgePrice
import YM.Integration.WilsonPhysicalHistoryKioskSeries

/-! Sum the actual analytic reserve over all visited dates in one physical
cutoff and one period. The earliest measured coupling pays the whole sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorLodgeCalendar
open Filter Finset Lattice RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G : Gauge}

theorem total (R : Run G) (simple : G.Simple) (rate : ℕ → ℝ) (held : WilsonMovingMentorLodge.Held rate R.kit)
    (q : ℕ) {ε : ℝ} (pos : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ (N per : ℕ) (dates : Finset ℕ),
      (∀ m ∈ dates, k ≤ m ∧ m < N) →
      ∑ m ∈ dates, WilsonMovingMentorLodgePrice.amount R N per m ≤ ε*(regulatorRun R.family N per k)^q := by
  obtain ⟨K,positive,calendar⟩ := WilsonPhysicalHistoryKioskSeries.income R simple q
  obtain ⟨start,localPrice⟩ := eventually_atTop.1
    (WilsonMovingMentorLodgePrice.measured R simple rate held (a:=((q+4:ℕ):ℝ))
      (Nat.cast_nonneg _) (div_pos pos positive))
  filter_upwards [eventually_ge_atTop start] with k after N per dates visits
  let g := regulatorRun R.family N per
  have nonneg (t : ℕ) : 0 ≤ g t := by change 0 ≤ (Real.sqrt _)⁻¹; positivity
  let bill := fun m : ℕ => (1:ℝ)/(((m:ℝ)+1)*((m:ℝ)+2))
  have price (m : ℕ) (atDate : m ∈ dates) :
      WilsonMovingMentorLodgePrice.amount R N per m ≤ (ε*(g k)^q)*bill m := by
    obtain ⟨past,valid⟩ := visits m atDate
    have bought := localPrice m (after.trans past) N per valid
    rw [Real.rpow_natCast] at bought
    have step := calendar k (m+1) N per (by omega) (by omega)
    have room : 0 < ((m:ℝ)+1)*((m:ℝ)+2) := by positivity
    have scale : ((m:ℝ)+1)*((m:ℝ)+2) ≤ (((m+1:ℕ):ℝ)+1)*(((m+1:ℕ):ℝ)+2) := by
      push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) m]
    have quotient : (g (m+1))^(q+4) ≤ K*(g k)^q / (((m:ℝ)+1)*((m:ℝ)+2)) :=
      (le_div_iff₀ room).mpr ((mul_le_mul_of_nonneg_left scale (pow_nonneg (nonneg _) _)).trans step)
    calc WilsonMovingMentorLodgePrice.amount R N per m ≤ (ε/K)*(g (m+1))^(q+4) := bought
         _ ≤ (ε/K)*(K*(g k)^q/(((m:ℝ)+1)*((m:ℝ)+2))) :=
             mul_le_mul_of_nonneg_left quotient (div_nonneg pos.le positive.le)
         _ = (ε*(g k)^q)*bill m := by dsimp [bill]; field_simp [positive.ne']
  calc ∑ m ∈ dates, WilsonMovingMentorLodgePrice.amount R N per m ≤ ∑ m ∈ dates, (ε*(g k)^q)*bill m :=
         Finset.sum_le_sum price
       _ = (ε*(g k)^q)*∑ m ∈ dates,bill m := (Finset.mul_sum ..).symm
       _ ≤ (ε*(g k)^q)*1 :=
         mul_le_mul_of_nonneg_left (WilsonPhysicalHistoryKioskSeries.installments dates) (mul_nonneg pos.le (pow_nonneg (nonneg _) _))
       _ = _ := mul_one _

end YM.Integration.WilsonMovingMentorLodgeCalendar
end
