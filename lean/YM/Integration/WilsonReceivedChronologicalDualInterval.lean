import YM.Integration.WilsonReceivedChronologicalTwoFlatSale
import YM.Integration.WilsonReceivedChronologicalDates

/-! Each real receipt may be tested at its elected older flat while all stage prices use the common capture clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalDualInterval
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

def Owned (j u b:ℕ)(s:(marks).Mode)(P size:ℕ)(η:ℝ):Prop:=
  ∃(base:m≤j)(S S':V→ℝ)(a a':ℕ)
    (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books
      (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)))
    (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books
      base ahead S' a' (rows (j+1))),
    WilsonReceivedChronologicalTwoFlatSale.Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower u b s P size η

theorem purchased {j u b:ℕ}{s:(marks).Mode}{p size:ℕ}{η:ℝ}
    (issued:Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows j u b s p size η)
    {v:ℕ}(uv:u≤v)(vb:v≤b):
    ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side v per)) rows (j+1) s‖ ≤
     (WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*(2:ℝ)^p*WilsonOriginalCensusFiledHousing.fare s size)*
       (regulatorRun R.family N per b)^p:=by
  obtain ⟨base,S,S',a,a',upper,lower,paid⟩:=issued
  exact WilsonReceivedChronologicalTwoFlatSale.paid R simple hk D Q π Γ Ψ books base ahead rows upper lower paid uv vb

open private nonnegFare from YM.Integration.WilsonOriginalCensusFiledPhysicalEdge

private theorem nonnegWage {T:Type}[DecidableEq T]{J:Census T}(s:J.Mode)(p size:ℕ)(η:ℝ)(ep:0≤η):
    0≤WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*(2:ℝ)^(p+1)*WilsonOriginalCensusFiledHousing.fare s size:=by
  apply add_nonneg
  · unfold WilsonOriginalOrdinaryFaceOrder.constant
    positivity
  · exact mul_nonneg (mul_nonneg ep (by positivity)) (nonnegFare s size)

theorem original (cost:ℕ):∃start:ℕ,∀{N per b L:ℕ}, start≤b → b+L≤N →
    R.family.S.a b/R.family.S.a (b+L)≤(R.family.path.levels.clock.hatBeta b)^cost →
    ∀(Ψ:∀ i,RG.Rep G (R.family.side i per))
      (rows:∀i:ℕ,Config G (R.family.side i per)→Marker.Poly (Stock.census V))
      (s:(marks).Mode)(u p size:ℕ)(η:ℝ)(_positive:0≤η)(days:Finset ℕ)
      (_earlier:∀ i ∈ days,b ≤ i+1)(_before:∀ i ∈ days,i+1 < b+L)
      (_issued:∀ i ∈ days,Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows i u b s (p+1) size η)
      (stop:ℕ→ℕ)(_bounded:∀ i ∈ days,u ≤ stop i ∧ stop i ≤ b),
    ∑i∈days,‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side (stop i) per)) rows (i+1) s‖ ≤
      (4*(cost:ℝ)/Real.log 3)*
      (WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*(2:ℝ)^(p+1)*WilsonOriginalCensusFiledHousing.fare s size)*
      (regulatorRun R.family N per b)^p:=by
  obtain ⟨start,clock⟩:=WilsonReceivedChronologicalDates.stages R simple cost
  refine ⟨start,?_⟩
  intro N per b L active live width Ψ rows s u p size η ep days earlier before issued stop bounded
  have count:=(clock (per:=per) active live width days earlier before).1
  let g:=regulatorRun R.family N per b
  let wage:=WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+
    η*(2:ℝ)^(p+1)*WilsonOriginalCensusFiledHousing.fare s size
  have gp:0 < g:=count.1
  have wage0:0≤wage:=nonnegWage s p size η ep
  have paid:∀ i ∈ days, ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side (stop i) per))
      rows (i+1) s‖ ≤ wage*g^(p+1):=fun i hi=>purchased R simple hk D Q π Γ Ψ books ahead rows (issued i hi)
        (bounded i hi).1 (bounded i hi).2
  calc
    _ ≤ ∑_i∈days,wage*g^(p+1):=Finset.sum_le_sum paid
    _ = ((days.card:ℝ)*g)*(wage*g^p):=by rw [Finset.sum_const,nsmul_eq_mul,pow_succ];ring
    _ ≤ (4*(cost:ℝ)/Real.log 3)*(wage*g^p):=mul_le_mul_of_nonneg_right count.2.2 (mul_nonneg wage0 (pow_nonneg gp.le _))
    _ = _:=by ring

end YM.Integration.WilsonReceivedChronologicalDualInterval
end
