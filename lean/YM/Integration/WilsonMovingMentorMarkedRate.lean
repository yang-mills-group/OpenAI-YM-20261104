import YM.Integration.WilsonMovingLogCurrency

/-! Physical price of the regular income outside the marked seed on all
original cutoff dates. The seed rank is fixed before any period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorMarkedRate
open Filter RG Wilson PhysicalNext.Repeat.Legato
open scoped Topology
variable {G : Gauge}

def exponent (k : ℕ) : ℝ := -(3/8:ℝ)*(4*(k:ℝ)+4)+1/80

theorem original (R : Run G) (simple : G.Simple) (q k : ℕ) (rank : q ≤ 3*k+2)
    {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per i : ℕ, m ≤ i → i ≤ N →
      (R.alloy.B.a.clock.hatBeta i)^(exponent k) ≤
        ε * (Pert.Asymptotics.regulatorRun R.family N per i)^q := by
  have gap : exponent k < -((q:ℝ)/2) := by
    have h : (q:ℝ) ≤ 3*(k:ℝ)+2 := by exact_mod_cast rank
    unfold exponent
    linarith
  obtain ⟨start,paid⟩ := eventually_atTop.1
    (WilsonMovingLogCurrency.physical R simple (Nat.cast_nonneg q) gap positive)
  obtain ⟨onset,warm⟩ := eventually_atTop.1
    ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_ge_atTop (max (start+1) onset)] with m early N per i after live
  have date : i-1+1=i := by omega
  have one := paid (i-1) (by omega) N per (by omega)
  rw [date,Real.rpow_natCast] at one
  have nonnegative : 0 ≤ (R.alloy.B.a.clock.hatBeta i)^(exponent k) :=
    Real.rpow_nonneg (by have ok := warm i (by omega); change 1 ≤ R.alloy.B.a.clock.hatBeta i at ok; linarith) _
  linarith

end YM.Integration.WilsonMovingMentorMarkedRate
end
