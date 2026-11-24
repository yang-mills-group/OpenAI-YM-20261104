import YM.Integration.WilsonThermometerReunitedPost

/-! Raise a finite original roster's analytic order on the very same masked income. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRaisedRoster
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations Push.AbsoluteSums
open scoped Classical BigOperators Topology

theorem salary {V ι T : Type} [DecidableEq V] {n : Side} {G : Gauge}
    {J : Census V} {A : Passport n V} (M : ι → Row A J G T) {w : V → ℝ} {grades : V → ℕ}
    {σ b c : ℝ} {q Q seats shelf : ℕ} (F : Scene.Armada M w grades σ b q seats shelf)
    (higher : q ≤ Q) (hc : 1 ≤ c) :
    Scene.Armada M (Stoop.radius w c) grades σ (c⁻¹*b) Q seats shelf := by
  have cp : 0 < c := zero_lt_one.trans_le hc
  refine ⟨F.toMinistry,fun v => div_pos (F.positive v) cp,?_,
    ⟨F.purchases.1,fun i => ⟨((F.purchases.2 i).1).trans higher,(F.purchases.2 i).2⟩⟩,F.honor⟩
  intro x
  apply budget_mono (budget_scale (inv_nonneg.mpr cp.le) (F.suggests x))
  · intro i
    split
    · exact mul_nonneg (Poly.worth (fun v => div_pos (F.positive v) cp) _).le
        (mul_nonneg (M i).sound.le (Real.exp_pos _).le)
    · exact le_refl 0
  · intro i
    by_cases h : (M i).center=x
    · simp only [if_pos h]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (Stoop.shrink w _ (M i).binder.live F.positive hc)
        (mul_nonneg (M i).sound.le (Real.exp_pos _).le)
    · simp [h]

end YM.Integration.WilsonThermometerRaisedRoster
