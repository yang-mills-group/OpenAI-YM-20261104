import YM.Integration.ActualRunSpring
import YM.IterationFour.Running
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Roster

/-! The native Heir program, its real tube and its singleton quotation on the
   original selected Run, at every cutoff, period and nonterminal scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedNativeStage
open Function Set Lattice Wilson Pressure RG Tree Precision
open Push.PriceCompiler Supply Testing AnalyticBridge.VerifiedReset.Time
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open PhysicalNext.JointLoad.Psalm
open scoped Classical

variable {G : Gauge} (R : Run G) {N m : ℕ} (p : ℕ) (hm : m < N)
local notation "a₀" => R.alloy.B.a
local notation "i₀" => R.alloy.B.a.clock.J m
local notation "i₁" => R.alloy.B.a.clock.J (m+1)
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family N p (m+1)

include p hm

theorem chart :
    Suite.Enabled R.metals.p R.metals.K R.kit.prices R.kit.recordP R.kit.v
      (Solo.raise R.kit.t) R.kit.span (a₀) m p (ships R.alloy.B N m p) := by
  apply Suite.directed p hm R.alloy.B _ R.kit.pledging.conducts.hearing.covers
    R.kit.pledging.conducts.hearing.early
  intro j hj
  apply R.kit.pledging.conducts.full
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
  omega

theorem plays :
    Plays (R.kit.prices (i₁) (i₀)) (R.kit.recordP (i₁) (i₀))
      ((a₀).budget m) ((a₀).budget (m+1)) (query R.metals.p R.metals.K (i₁) (i₀))
      (ships R.alloy.B N m p) ((a₀).clock.hatBeta m) := (chart R p hm).make

theorem plented : 0 < (g₁) ∧
    Lute.Plented (R.kit.prices (i₁) (i₀)) (R.kit.recordP (i₁) (i₀))
      ((a₀).budget m) ((a₀).budget (m+1)) ((a₀).S.block m) (R.kit.span (i₁) (i₀))
      ((a₀).clock.hatBeta m) (g₁) :=
  (chart R p hm).clocks _ (R.makes.wilson.represents N p (m+1) hm).band

theorem quotation :
    Release.accepts (R.kit.span (i₁) (i₀)) ((a₀).budget (m+1)).supportExponent
      (Solo.raise R.kit.t (i₁) (i₀)) ((a₀).S.block m) ∧
    Release.Quotation (R.kit.prices (i₁) (i₀)) ((a₀).budget m).power (R.kit.span (i₁) (i₀))
      ((a₀).budget (m+1)).supportExponent (Solo.raise R.kit.t (i₁) (i₀))
      (R.kit.v (i₁) (i₀)) := (chart R p hm).pre

theorem affordable :
    (R.kit.v (i₁) (i₀) / (((a₀).S.block m).val : ℝ)) * (a₀).clock.allowance (m+1) ≤
      forecastE (a₀) m/8 := (chart R p hm).spare

end YM.Integration.QLocalInheritedNativeStage
end
