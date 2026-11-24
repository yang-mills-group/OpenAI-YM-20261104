import YM.Integration.WilsonAddressedFiniteGuardEars

/-! The original single failed-stencil event under an arbitrary held Wilson field retains its actual spring factor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldHaloFare
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonAddressedFiniteGuardFields (cap gap footprint)
open WilsonOriginalMicroscopicEntranceHeldHalo (spring)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){N per m k i:ℕ}(π:ℕ  →  Layout G)(Γ:ℕ  →  Pace.Coin)
    (Ψ:∀j,Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    {K:ℕ}(cut:K  ≤  N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m   ≤   u)(ui:u   ≤   i)
    (fixed:WilsonSingleHardRadius.first R simple   ≤   u)(cap:WilsonCenteredCaptureClock.first R simple   ≤   K)
local notation "H" => R.alloy.B.a.clock.hatBeta K
local notation "param" => R.alloy.B.a.budget K
local notation "μ" before:max W:max => WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W


variable {I:Type}[Fintype I](d:I  →  ℕ)
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryCollar WilsonCapturedPrimaryPaid
open WilsonFirstReceivedRadialStencil WilsonOriginalRadialRaySpring

open WilsonAddressedFiniteGuardEars (fare)
include course cut top way ticket floor ui fixed cap in
theorem original (e p:ℕ){B tol:ℝ}(bp:0 ≤ B)(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
      (p+WilsonAddressedFiniteGuardCapital.power R d e univ) positive)).choose ≤ K)
    (before:i+1 ≤ K)(strength:(param).supportExponent ≤ 100)
    (o:I → Site (R.family.side K per))(v:∀a,R.family.label (d a))
    (income:∀a,(R.family.labels.level (d a)).coeffSize (v a) ≤ B*H^e)(s:Finset I)(W:Config G (R.family.side i per)):
    let read:=actualTransport R.family (N:=N) (gap R d N per K o v s) ((Nat.le_succ i).trans before)
    ‖read W‖ ≤ spring R i N per W*fare R (K:=K) d B tol p s:=by
  intro read
  have pw:=WilsonAddressedFiniteGuardCapital.price_nonneg R d bp s
  have hp:0<H:=zero_lt_one.trans_le (R.family.path.levels.fits.delayed K).le
  have gross:(WilsonAddressedFiniteGuardCapital.price R d B s*
        ((WilsonAddressedFiniteGuardCapital.count R d s:ℝ)*(4*Real.exp ((param).supportExponent+2))*(tol/H^p)))
       ≤ fare R (K:=K) d B tol p s:=by
    apply mul_le_mul_of_nonneg_left _ pw
    apply mul_le_mul_of_nonneg_right _ (div_nonneg positive.le (pow_nonneg hp.le _))
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    linarith
  have paid (W:Config G (R.family.side i per)):
      ‖read W‖ ≤ spring R i N per W*fare R (K:=K) d B tol p s:=
    (WilsonAddressedFiniteGuardRefund.original R π Γ Ψ course cut top simple way D Q ticket floor ui fixed cap d
      e p bp positive late before o v income s W).2.trans (mul_le_mul_of_nonneg_left gross (sq_nonneg _))
  exact paid W

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldHaloFare
end
