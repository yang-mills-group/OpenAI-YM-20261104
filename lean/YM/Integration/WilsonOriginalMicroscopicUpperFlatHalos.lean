import YM.Integration.WilsonOriginalPaidFlatHalos
import YM.Integration.WilsonOlderFreshHardSite

/-! Every original upper date, including the microscopic cutoff. The elected
Topline supplies the same registered compulsory addresses at the endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicUpperFlatHalos
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
   (live:b≤N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N)){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Space" => Config G (R.family.side b per)


include course live top way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)
    {ι:Type*}[DecidableEq ι](seats:Finset ι)(y:ι→Site (R.family.side b per))
    (Y:Space→ℂ)(borel:Measurable Y){e M:ℝ}(ep:0≤e)(mp:0≤M)(gross:∀U,‖Y U‖≤M)
    (clear:∀U,(∀a∈seats,Healthy (Ψ b).p.threshold (halo (Ψ b).p.B {y a}) U)→‖Y U‖≤e)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b):
    ‖actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans ib) 1‖ ≤
      e+M*((seats.card:ℝ)*(4*hitWidth (Ψ b).p*Real.exp ((Ψ b).p.supportExponent+2)*β*
        R.alloy.B.a.clock.forcedAllowance b)):=by
  let Z (a:ι):=halo (Ψ b).p.B {y a}
  let event (a:ι):Set Space:={U|¬ Healthy (Ψ b).p.threshold (Z a) U}
  let v:=R.alloy.B.a.clock.forcedAllowance b
  let cash:ℝ:=(hitWidth (Ψ b).p*v)*Real.exp ((Ψ b).p.supportExponent+2)/κ
  have walk:=course.1.walk b (floor.trans ub) live
  have installed:=WilsonOlderFreshHardSite.original R way D Q π Γ Ψ course ticket (floor.trans ub) top live
  obtain ⟨_,_,⟨second⟩,_⟩:=installed.room
  let keeper:=WilsonCenteredStampedKeeper.original (Ψ b) second
  obtain ⟨div,hv,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec b capture
  rw [←walk.truep.point] at room
  have strict:0<v:=Real.sqrt_pos.mp div
  have price:0<cash:=by dsimp only [cash];apply div_pos _ div;apply mul_pos _ (Real.exp_pos _);apply mul_pos _ strict;unfold hitWidth;positivity
  have meas (a:ι):MeasurableSet (event a):=(healthy_closed (Ψ b).p.threshold (Z a)).measurableSet.compl
  have owned (a:ι):Owned (F:=F) (Ψ b) A (y a) κ cash
      (fun U=>((Ψ b).eval U:ℂ)*(event a).indicator (fun _=>(1:ℂ)) U):=by
    obtain ⟨r,fmt,due,hit⟩:=WilsonAddressedFlagIndicator.original (F:=F) (Ψ b) keeper A (y a)
      div hv room walk.truep.valid.labels.forced walk.truep.valid.labels.boundK
    refine ⟨r,fmt,due,fun U=>?_⟩
    rw [hit U]
    change ((Ψ b).eval U:ℂ)*(if (flags (Ψ b).p.threshold U ∩ Z a).Nonempty then (1:ℂ) else 0) =
      ((Ψ b).eval U:ℂ)*(event a).indicator (fun _=>(1:ℂ)) U
    rw [←WilsonAddressedFlagIndicator.value (Ψ b).p.threshold (Z a) U]
    by_cases h:Healthy (Ψ b).p.threshold (Z a) U <;> simp [event,WilsonAddressedFlagIndicator.badge,h]
  have heard:=WilsonOriginalFailedHaloPosterior.original R π Γ Ψ course live S A simple way D Q ticket floor ub fixed
    seats event (fun a _=>meas a) y (fun _=>cash) (fun _ _=>price) (fun a _=>owned a) Y borel ep mp gross
    (fun U ok=>clear U (fun a mem=>Classical.byContradiction (fun fail=>ok a mem fail))) ui ib
  have cancel:4*cash*β*κ=4*hitWidth (Ψ b).p*Real.exp ((Ψ b).p.supportExponent+2)*β*v:=by
    dsimp only [cash];field_simp [div.ne']
  simpa only [Metric.mem_closedBall,dist_zero_right,cancel,Finset.sum_const,nsmul_eq_mul,v] using heard

end YM.Integration.WilsonOriginalMicroscopicUpperFlatHalos
end

