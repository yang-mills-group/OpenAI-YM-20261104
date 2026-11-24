import YM.Integration.WilsonOriginalSeparatedRegular
import YM.Integration.WilsonOriginalDecoderHaloRate
import YM.Integration.WilsonOriginalClockFacePosterior

/-! The actual regular difference of two dated prints at the original older
Wilson field. The probability tariff scales with the sum of the individual
root neighborhoods, including when the roots are far apart. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterDecoder
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm Multi Push.AbsoluteSums.Animals
open WilsonRootedKioskOccupiedSlip WilsonOriginalOrdinaryFlatHulls
open WilsonOriginalSeparatedRegular WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "fp" => (Ψ b).p
local notation "Z" => Site (R.family.side b per)

private theorem site_cost {x y E H τ B C F:ℝ} {p:ℕ} (sites:x≤y) (hp:0≤H)
    (tp:0≤τ)(bp:0≤B)(cp:0≤C):E+H*x*C*τ/B^p*F^2≤E+H*y*C*τ/B^p*F^2:=by gcongr

include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p:ℕ){tol:ℝ}(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p positive)).choose ≤ b)
    {V:Type}[Fintype V][DecidableEq V]{J:Census V}(s:J.Mode)(h:ℕ)(o:V→Z)
    (Y:Config G (R.family.side b per)→ℂ)(borel:Measurable Y){e M:ℝ}(ep:0 ≤ e)(mp:0 ≤ M)
    (gross:∀W,‖Y W‖ ≤ M)
    (near:∀W,(∀a∈roots fp h o s,Healthy (fp).threshold (halo (fp).B {a}) W)→‖Y W‖ ≤ e)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b)(U:Config G (R.family.side i per)):
    let span:=max (fp).B (reach (fp).B h)
    ‖actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans ib) U‖ ≤
      e+M*((s.val.card*(span+span+1)^4:ℕ):ℝ)*(4*Real.exp ((fp).supportExponent+2))*tol/β^p*
        (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
          (R.family.path.β N per (i+1)) U))^2:=by
  intro span
  have read:=WilsonOriginalDecoderHaloRate.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p 0 positive (by simpa only [Nat.add_zero] using late) (roots fp h o s) id le_rfl
    Y borel (e:=e) (B:=M) ep mp (by simpa only [pow_zero,mul_one] using gross) near ui ib U
  apply read.trans
  have card:((roots fp h o s).card:ℝ) ≤ ((s.val.card*(span+span+1)^4:ℕ):ℝ):=by
    exact_mod_cast WilsonOriginalSeparatedRegular.size h o s (p:=fp)
  have beta:0 ≤ β:=by exact (R.family.path.levels.fits.delayed b).le.trans' zero_le_one
  exact site_cost card mp positive.le beta (mul_nonneg (by norm_num) (Real.exp_nonneg _))
end YM.Integration.WilsonOriginalFullRosterDecoder
end
