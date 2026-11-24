import YM.Integration.WilsonOriginalNullStored

/-! Purchase the parent's scalar and stencil gates before either physical
regulator. The host in the actual regular fee already includes the cost
of putting the full signed projected section back on its physical supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullClock
open Function Finset Filter Lattice Wilson RG Source Labels PhysicalNext PhysicalNext.Repeat
open Legato Peak Org JointLoad Clockwork LocalComparison Next.Foundations Push.Local
open Graces Planned.GuardedAtom Extra.Histories Push.PriceCompiler
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "A₀" => R.alloy.B.a
local notation "κ" => LocalComparison.forcedDivisor R.family

theorem ready (simple : G.Simple) (d q : ℕ)
    (roster : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power) :
    ∀ᶠ i : ℕ in atTop,
      d+3 ≤ (A₀).clock.J i ∧ q ≤ (A₀).clock.J i ∧ d ≤ ((A₀).budget i).order ∧
      d ≤ ((A₀).budget i).power ∧ hitWidth ((A₀).budget i) * (κ i) ≤ 1 ∧
      ∀ p, minSide G d ≤ (R.family.side i p).val := by
  filter_upwards [(A₀).fits.deep.eventually (eventually_ge_atTop (d+3)),
    (A₀).fits.deep.eventually (eventually_ge_atTop q),
    WilsonCenteredDividedRoom.original R simple,
    (A₀).S.den_strict.tendsto_atTop.eventually (eventually_ge_atTop (minSide G d))] with i degree asking room length
  have charge : 0 < (κ i) := Real.sqrt_pos.mpr (Real.exp_pos _)
  have sq : (κ i)*(κ i) = (A₀).clock.forcedAllowance i := Real.mul_self_sqrt (Real.exp_pos _).le
  have hit := room.2
  change hitWidth ((A₀).budget i)*(A₀).clock.forcedAllowance i/(κ i) ≤ 1 at hit
  rw [←sq,←mul_assoc,mul_div_cancel_right₀ _ charge.ne'] at hit
  have hprof := roster ((A₀).clock.J i)
  rw [← params_eq R.alloy.B.valid] at hprof
  refine ⟨degree,asking,(show d ≤ (A₀).clock.J i by omega).trans hprof.1,
    (show d ≤ (A₀).clock.J i by omega).trans hprof.2,hit,?_⟩
  intro p
  exact length.trans (Nat.le_mul_of_pos_left _ ((A₀).S.period p).property)

theorem restored (P : Stage) (d : ℕ) (L : Side) :
    4 * vigors G P d * coinFee G P d L ≤ Doors.rate L := by
  let v := vigors G P d
  let b := Motion.orbitCost ((Labels.frames G).level d)
  have positive := coin_pos G P d L
  have hb : 1 ≤ b := Motion.orbitCost_one_le _
  have bound : 4 * v ≤ host G P d := by
    change 4*v ≤ 1 + 2 * |v| * (1 + b + |faded P|)
    have haux := mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hb)
    have hother := mul_nonneg (abs_nonneg v) (abs_nonneg (faded P))
    linarith [le_abs_self v]
  calc
    4 * vigors G P d * coinFee G P d L ≤ host G P d * coinFee G P d L :=
      mul_le_mul_of_nonneg_right bound positive.le
    _ = _ := by unfold coinFee; field_simp [(simpleH G P d).ne']

end YM.Integration.WilsonOriginalNullClock
