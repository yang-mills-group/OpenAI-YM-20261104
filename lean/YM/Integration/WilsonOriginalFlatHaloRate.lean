import YM.Integration.WilsonOriginalPaidFlatHalos
import YM.Integration.WilsonCenteredDividedRoom

/-! A polynomial all-field wage on a finite family of actual cropped supports
costs any prescribed inverse clock power at the original flat stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFlatHaloRate
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Space" => Config G (R.family.side b per)



include simple in
theorem calendar (p:ℕ){tol:ℝ}(positive:0<tol):
    ∀ᶠ j:ℕ in atTop,hitWidth (R.alloy.B.a.budget j)*R.alloy.B.a.clock.forcedAllowance j ≤
      LocalComparison.forcedDivisor R.family j ∧
      R.alloy.B.a.clock.hatBeta j*LocalComparison.forcedDivisor R.family j ≤ tol/(R.alloy.B.a.clock.hatBeta j)^p:=by
  filter_upwards [WilsonCenteredDividedRoom.original R simple,WilsonCenteredCaptureClock.original R simple,
    eventually_ge_atTop (WilsonSingleHardRadius.start R simple p positive)] with j budget div late
  have bp:0<R.alloy.B.a.clock.hatBeta j:=zero_lt_one.trans (R.alloy.B.a.fits.delayed j)
  refine ⟨((div_le_iff₀ div.1).mp budget.2).trans_eq (one_mul _),?_⟩
  have cheap:=(WilsonSingleHardRadius.cash R simple p positive late).2
  apply (le_div_iff₀ (pow_pos bp p)).mpr
  have pay:=(le_div_iff₀ (pow_pos bp (p+1))).mp cheap
  calc
    _=LocalComparison.forcedDivisor R.family j*(R.alloy.B.a.clock.hatBeta j)^(p+1):=by rw [pow_succ];ring
    _≤tol:=pay

include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p d₀:ℕ){tol:ℝ}(positive:0<tol)
    (late:(eventually_atTop.mp (calendar R simple (p+d₀) positive)).choose ≤ b)
    {ι:Type*}[DecidableEq ι](seats:Finset ι)(y:ι→Site (R.family.side b per))
    {α:ℝ}(strength:(Ψ b).p.supportExponent≤α)(Y:Space→ℂ)(borel:Measurable Y)
    {e B:ℝ}(ep:0≤e)(bp:0≤B)(gross:∀U,‖Y U‖ ≤ B*β^d₀)
    (clear:∀U,(∀a∈seats,Healthy (Ψ b).p.threshold (halo (Ψ b).p.B {y a}) U)→‖Y U‖≤e)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b):
    ‖actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans ib) 1‖ ≤
      e+B*(seats.card:ℝ)*(4*Real.exp (α+2))*tol/β^p:=by
  have walk:=course.1.walk b (floor.trans ub) cut.le
  obtain ⟨width,cheap⟩:=(eventually_atTop.mp (calendar R simple (p+d₀) positive)).choose_spec b late
  rw [←walk.truep.point] at width
  have inc:0<β:=zero_lt_one.trans (R.alloy.B.a.fits.delayed b)
  have cap:=WilsonOriginalPaidFlatHalos.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture seats y Y borel ep (mul_nonneg bp (pow_nonneg inc.le _)) gross clear ui ib
  have bill:4*hitWidth (Ψ b).p*Real.exp ((Ψ b).p.supportExponent+2)*β*R.alloy.B.a.clock.forcedAllowance b ≤
      (4*Real.exp (α+2))*(tol/β^(p+d₀)):=by
    calc
      _=4*Real.exp ((Ψ b).p.supportExponent+2)*(β*(hitWidth (Ψ b).p*R.alloy.B.a.clock.forcedAllowance b)):=by ring
      _≤4*Real.exp (α+2)*(tol/β^(p+d₀)):=by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [strength])) (by norm_num))
          ((mul_le_mul_of_nonneg_left width inc.le).trans cheap) _ (by positivity)
        apply mul_nonneg inc.le;apply mul_nonneg _ (YM.Push.Local.allowance_pos _ _).le;unfold hitWidth;positivity
  apply cap.trans
  calc
    _≤e+(B*β^d₀)*((seats.card:ℝ)*(4*Real.exp (α+2)*(tol/β^(p+d₀)))):=by
      gcongr
    _=_:=by rw [pow_add];field_simp [inc.ne']

end YM.Integration.WilsonOriginalFlatHaloRate
end

