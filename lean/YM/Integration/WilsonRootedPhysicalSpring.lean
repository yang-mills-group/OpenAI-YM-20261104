import YM.Integration.WilsonRootedUltravioletSource
import YM.Integration.ActualRunSpring

/-! The original marked height acquisition acts on the physical spring already
carried by this very run. Its teller, expense, hose, input and output are fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalSpring
open Filter Function Finset Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy MergeProof LocalLTE RGLocalTaylor
open Org GapsLocal.Renew ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [Fintype V] (R : Run G) (J : Request V) (Γ : Census V)
    {N per m : ℕ} {below : m < N} (P : ActualRunSpring.Packet R N per m below)
local notation "j₁" => R.alloy.B.a.clock.J (m+1)
local notation "j₀" => R.alloy.B.a.clock.J m
local notation "cash" => Mallow.houseS P.spring P.point
local notation "x₀" => R.alloy.B.a.clock.hatBeta m
local notation "L₀" => R.rolls.L (j₁)
local notation "β₁" => betaF G (x₀) (L₀)
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family N per (m+1)

/-- No cash is chosen after the spring. The E-bound of the full physical
incoming representative, including its prior evolution, pays the marked Captain. -/
theorem high (height : Mallow.RG12.Earned (ManuscriptQLocalMarkedHeightRun.acquisition G J)
      R.kit.shape R.alloy.delay) :
    ManuscriptQLocalMarkedHeightRun.High (R.kit.expense (j₁) (j₀)) (cash) J Γ ((2*(g₁))^(J.order+1)) := by
  have ticket := height (j₁) (x₀) (R.alloy.B.valid.pays m) (j₀) (step_paid R.alloy.B.a m)
  have beta : R.alloy.B.a.clock.hatBeta (m+1) = (β₁) := beta_eq R.alloy.B.valid m
  have count : incomingE G (L₀) (x₀) = R.alloy.B.a.clock.allowance (m+1) := by
    unfold incomingE
    rw [←beta]
    rfl
  have cap : (P.input P.point.val).activities.EBound (P.input P.point.val).p (incomingE G (L₀) (x₀)) := by
    rw [←P.fine,count]
    exact (R.makes.wilson.represents N per (m+1) below).good.labels.boundE
  apply ManuscriptQLocalMarkedHeightRun.certificate _ (cash) J Γ
    (i:=(j₁)) (h:=R.metals.p.profile (j₀)) ticket (cash).laws.data.funds
    (protocol (n:=per) R.alloy.B below R.kit.pledging.conducts.full) cap
  have hp : 0 < (β₁) := zero_lt_one.trans_le ticket.1
  have price : (Real.sqrt (β₁))⁻¹ ≤ 2*(g₁) := by
    rw [←beta]
    exact (Currency.hat_g R.makes N per (m+1) below).1
  have sqrt : (Real.sqrt (β₁))⁻¹=(β₁)^(-(1/2:ℝ)) := by rw [Real.rpow_neg hp.le,Real.sqrt_eq_rpow]
  calc
    _ = ((Real.sqrt (β₁))⁻¹)^(J.order+1) := by
      rw [sqrt,←Real.rpow_natCast,←Real.rpow_mul hp.le]
      congr 1
      push_cast
      ring
    _ ≤ _ := pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) price _

end YM.Integration.WilsonRootedPhysicalSpring
end
