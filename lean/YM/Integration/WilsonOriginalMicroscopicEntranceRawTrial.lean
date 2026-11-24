import YM.Integration.WilsonOriginalAlternativeTrialSettlement
import YM.Integration.WilsonOriginalMicroscopicEntranceTrialScale

/-! The funded trial starts with each column in its original units, and its complete occupied exit is charged at the receiving field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceRawTrial
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i b N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m  ≤  i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) 
  (grades : Fin 3 → ℕ) (order shelf seats : ℕ)
  (o:Fin 3→Site (R.family.side (b+1) per)) (v:∀j,R.family.label (grades j)) (z:Fin 3→ℂ)
  (ib:i  ≤  b) (upper:b+1  ≤  N)

local notation "actors" => (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3))
variable (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3))
  (WilsonOriginalAlternativeFiniteSource.sectors (V:=Fin 3)) grades order shelf seats i hi
  (WilsonReceivedCloseHistory.history (N:=N) R (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3))
    (WilsonOriginalAlternativeTrialSource.source R grades N per (b+1) o v z) i ib))
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "W_" => Ψ i
local notation "J_" => Stock.census (Fin 3)

local notation "fire_" => (WilsonOriginalAlternativeFiniteSource.fired (V:=Fin 3))
open Multi Comparison.RG02.Cumulants WilsonThermometerSolitaryFiledExchange WilsonThermometerSolitaryExchange
local notation "mask_" s:max => WilsonOriginalAlternativeTrialSource.mode R grades N per (b+1) o v z fire_ s
open WilsonThermometerMixedCollarSubpower WilsonOriginalOccupiedCorridor WilsonOriginalMicroscopicEntranceReader
open Filter
open WilsonOriginalAlternativeTrialCollateral
include course upper in
theorem original (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)(simple:G.Simple)
    (a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e)(it:0 < i)(age:WilsonOriginalAlternativeTrialSettlement.onset R simple a p C e cp ep ≤ i-1)
    (active:6*seats ≤ R.alloy.B.a.clock.J i)(wide:5 ≤ (W_).p.B)
    (apart:∀v k:Fin 3,v≠k→(W_).p.B^2+1 ≤ separation (homes v) (homes k))
    (u:ℕ)(ui:u ≤ i)(mu:m ≤ u)(old:WilsonOriginalAlternativeTrialEarlier.start R simple 1 (a*3) p C e cp ep ≤ u)
    (span:((i-u+WilsonOriginalAlternativeTrialCollateral.reserve (b+1) i:ℕ):ℝ) ≤ C*(1+Real.log (R.family.path.levels.clock.hatBeta i)))
    (initial:Fin 3→ℝ)(wages:∀j,(initial j)⁻¹ ≤ (R.family.path.levels.clock.hatBeta i)^a)
    (growth:scale (R.family.path.levels.clock.hatBeta (b+1)) ≤ 2*scale (R.family.path.levels.clock.hatBeta i))
    (actual:∀j,(weights j)⁻¹ ≤ (initial j)⁻¹*Real.exp ((9*((b+1-i:ℕ):ℝ)+6)*
      (scale (R.family.path.levels.clock.hatBeta (b+1)))^3))
    (s:(J_).Mode)(W:Config G (R.family.side u per))(clear:flags (Ψ u).p.threshold W=∅):
    (∀a,z a=WilsonOriginalMicroscopicEntranceGridRow.factor R grades (b+1) a)→
    let entered:=fun a U=>WilsonOriginalMicroscopicEntranceGridRow.factor R grades (b+1) a*
      WilsonOriginalMicroscopicGuardedTrial.guarded R grades N per (b+1) o v a U
    let face:=WilsonOriginalMicroscopicEntranceEarlier.face entered s
    let held:=actualTransport R.family (N:=N) face (ib.trans (Nat.le_succ b))
    let softReading:=fun U=>∏a∈s.val,value (gauge).E fire_ U a
    ‖actualTransport R.family (N:=N) (fun U=>held U-softReading U) ui W‖≤
      (3*(e*(Pert.Asymptotics.regulatorRun R.family N per i)^p))*(shards (J_) s).card:=by
  intro named entered face held softReading
  have filed:mask_ s=face:=by
    funext U
    simp only [WilsonOriginalAlternativeTrialSource.mode,WilsonOriginalAlternativeFiniteSource.fired,one_mul,
      WilsonOriginalMicroscopicEntranceEarlier.face,face,entered,WilsonOriginalAlternativeTrialSource.arm,
      WilsonOriginalMicroscopicGuardedTrial.guarded,named]
  have service:=WilsonOriginalAlternativeTrialSettlement.original R hk D Q π Γ Ψ course books hi ahead grades
    order shelf seats o v z ib upper P way ticket simple a p C e cp ep it age active wide apart u ui mu old span initial wages growth actual s W clear
  simpa only [held,softReading,filed,WilsonOriginalMicroscopicEntranceExchange.word_value] using service

end YM.Integration.WilsonOriginalMicroscopicEntranceRawTrial
end
