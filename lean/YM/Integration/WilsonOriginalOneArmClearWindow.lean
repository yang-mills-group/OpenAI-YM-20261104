import YM.Integration.WilsonOriginalOneArmClearCash
import YM.Integration.WilsonOriginalPhysicalCorridorLength

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmClearWindow
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
variable {S S': V → ℝ}{a a':ℕ}
variable (rows:∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census V))

open WilsonOriginalOneArmClearCash (Owned wage)
open Finset Filter

private theorem wage_nn (s:(marks).Mode)(P:ℕ){η:ℝ}(ep:0≤η):0≤wage s P η:=by
  dsimp only [wage,WilsonOriginalOrdinaryFaceOrder.constant]
  positivity

/-- All local genuine two-source filings are heard on the same final original
board; the held value can be chosen after their schedule has been charged. -/
theorem charged {b K:ℕ}(active:b<K)(s:(marks).Mode)(P:ℕ)(η:ℝ)
    (sales:∀i∈Ico b K,Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows i b s (P+1) η):
    (∀ i:ℕ,b ≤ i → i ≤ K → Integrable (rows i) (prior G _)) ∧
     ∀W:Config G (R.family.side b per), flags (R.family.path.rep N per b).p.threshold W=∅ →
      (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per)
        (R.family.path.β N per (b+1)) W))^2 ≤ 2 →
      ∀i∈Ico b K, ‖WilsonOriginalJointTrialHearing.fee R N per W rows i s‖≤
        wage s (P+1) η*(regulatorRun R.family N per b)^(P+1):=by
  have price:=fun i (h:i∈Ico b K)=>WilsonOriginalOneArmClearCash.earned R simple hk D Q π Γ Ψ books ahead rows (sales i h)
  constructor
  · intro i lower upper
    by_cases last:i=K
    · have h:K-1∈Ico b K:=mem_Ico.mpr (by omega)
      have paid:=(price (K-1) h).1.1
      exact Eq.mp (congrArg (fun r:ℕ=>Integrable (rows r) (prior G _)) (by omega : K-1+1=i)) paid
    · exact (price i (mem_Ico.mpr ⟨lower,lt_of_le_of_ne upper last⟩)).1.2
  · intro W clear tilt i member
    exact (price i member).2 W clear tilt

include simple in
theorem total (cost P:ℕ)(s:(marks).Mode){η:ℝ}(ep:0≤η):
    ∀ᶠ b:ℕ in atTop,∀{N per K:ℕ},b<K → K≤N →
      R.family.S.a b/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta b)^cost →
      ∑_i∈Ico b K,wage s (P+1) η*(regulatorRun R.family N per b)^(P+1) ≤
      (4*(cost:ℝ)/Real.log 3)*wage s (P+1) η*(regulatorRun R.family N per b)^P:=by
  filter_upwards [WilsonOriginalPhysicalCorridorLength.original R simple cost] with b size
  intro N per K edges live span
  have last:b+(K-b)=K:=by omega
  have count:=size (L:=K-b) (N:=N) (per:=per) (last.symm ▸ live) (last.symm ▸ span)
  let g:=regulatorRun R.family N per b
  calc
    _ = (((K-b:ℕ):ℝ)*g)*(wage s (P+1) η*g^P):=by
      rw [sum_const,Nat.card_Ico,nsmul_eq_mul,pow_succ]
      ring
    _ ≤ (4*(cost:ℝ)/Real.log 3)*(wage s (P+1) η*g^P):=mul_le_mul_of_nonneg_right count.2.2
      (mul_nonneg (wage_nn s _ ep) (pow_nonneg count.1.le _))
    _ = _:=by ring

end YM.Integration.WilsonOriginalOneArmClearWindow
end
