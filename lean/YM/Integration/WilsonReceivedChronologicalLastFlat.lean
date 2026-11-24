import YM.Integration.WilsonReceivedChronologicalCurrentFlat
import YM.Integration.WilsonReceivedChronologicalDualInterval
import YM.Integration.WilsonVacuumPreResetSameTime

/-! The last dated coupon of a two-flat switch, including a switch at the very bottom reporting level. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalLastFlat
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ j)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "actors" => WilsonOriginalMixedBlockRows.room V
local notation "nulls" => fun _:V => (⊥:Submodule ℝ ℂ)

variable (rows:∀i:ℕ,Config G (R.family.side i per)→Marker.Poly (Stock.census V))


open WilsonReceivedChronologicalDualInterval (Owned)
open private nonnegFare from YM.Integration.WilsonOriginalCensusFiledPhysicalEdge
local notation "g" i:max => regulatorRun R.family N per i

def Here (j:ℕ)(s:(marks).Mode)(p:ℕ):Prop:=
  ∃(base:m≤j)(S S':V→ℝ)(a a':ℕ)
    (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books
      (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)))
    (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' (rows (j+1))),
    WilsonReceivedChronologicalInstallment.Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower
      (le_refl (j+1)) s p (1:Config G (R.family.side (j+1) per))

def Ticket (j u b v:ℕ)(s:(marks).Mode)(p size:ℕ)(η:ℝ):Prop:=
  (u≤v ∧ v≤b ∧ Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows j u b s p size η) ∨
    (b=j+1 ∧ ((v=j+1 ∧ Here (N:=N) R simple hk D Q π Γ Ψ books ahead rows j s p) ∨
      (u≤v ∧ v≤j ∧ Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows j u j s p size η)))

def wage {T:Type}[DecidableEq T]{J:Marker.Census T}(s:J.Mode)(p size:ℕ)(η:ℝ):ℝ:=
  WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*(2:ℝ)^p*WilsonOriginalCensusFiledHousing.fare s size

theorem nonneg {T:Type}[DecidableEq T]{J:Marker.Census T}(s:J.Mode)(p size:ℕ)(η:ℝ)(ep:0≤η):
    0 ≤ wage s p size η:=by
  apply add_nonneg
  · unfold WilsonOriginalOrdinaryFaceOrder.constant;positivity
  · exact mul_nonneg (mul_nonneg ep (by positivity)) (nonnegFare s size)

theorem original {j u b v:ℕ}{s:(marks).Mode}{p size:ℕ}{η:ℝ}(ep:0≤η)(live:j<N)(bn:b≤N)
    (first:(eventually_atTop.mp (WilsonVacuumPreResetSameTime.ratios R simple)).choose ≤ j)
    (issued:Ticket (N:=N) R simple hk D Q π Γ Ψ books ahead rows j u b v s p size η):
    ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side v per)) rows (j+1) s‖ ≤
      (wage s p size η)*(3:ℝ)^p*(g b)^p:=by
  have gp:0≤g b:=(ActualRunKernelPackets.regulator_pos R N per b bn).le
  have wage0:=nonneg s p size η ep
  have lift:wage s p size η*(g b)^p ≤ wage s p size η*(3:ℝ)^p*(g b)^p:=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right wage0 (one_le_pow₀ (by norm_num : (1:ℝ)≤3))) (pow_nonneg gp _)
  rcases issued with ⟨uv,vb,T⟩ | ⟨rfl,⟨rfl,H⟩ | ⟨uv,vj,T⟩⟩
  · exact (WilsonReceivedChronologicalDualInterval.purchased R simple hk D Q π Γ Ψ books ahead rows T uv vb).trans lift
  · obtain ⟨base,S,S',a,a',upper,lower,H⟩:=H
    have spent:=WilsonReceivedChronologicalCurrentFlat.original R simple hk D Q π Γ Ψ books base ahead rows upper lower s p H
    have exposed:WilsonOriginalOrdinaryFaceOrder.constant s s.val.card≤wage s p size η:=
      le_add_of_nonneg_right (mul_nonneg (mul_nonneg ep (by positivity)) (nonnegFare s size))
    exact (spent.trans (mul_le_mul_of_nonneg_right exposed (pow_nonneg gp _))).trans lift
  · have prior:=(WilsonReceivedChronologicalDualInterval.purchased R simple hk D Q π Γ Ψ books ahead rows T uv vj)
    have near:=(eventually_atTop.mp (WilsonVacuumPreResetSameTime.ratios R simple)).choose_spec j first N per live
    have change:=pow_le_pow_left₀ (ActualRunKernelPackets.regulator_pos R N per j live.le).le near p
    calc
      _ ≤ wage s p size η*(g j)^p:=prior
      _ ≤ wage s p size η*(3*g (j+1))^p:=mul_le_mul_of_nonneg_left change wage0
      _ = _:=by rw [mul_pow,mul_assoc]

end YM.Integration.WilsonReceivedChronologicalLastFlat
end
