import YM.Integration.WilsonOriginalOneArmAppointments
import YM.Integration.WilsonOriginalOneArmFixedCash
import YM.Integration.WilsonOriginalOneArmClearWindow
import YM.Integration.WilsonOriginalOneArmClearCash
import YM.Integration.WilsonOriginalPhysicalCorridorLength

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmSchoolWindow
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


/-- The prior due at b, actual interior posting, and last canonical rent use their issued original pupils. -/
inductive Route (b K t:ℕ)(s:(marks).Mode)(P:ℕ)(η:ℝ):Prop where
  | base (home:t=b)(paid:WilsonOriginalOneArmAppointments.Material
      (Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows t b s P η)):Route b K t s P η
  | last (top:t+1=K)(paid:WilsonOriginalOneArmAppointments.Canonical
      (Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows t b s P η)):Route b K t s P η
  | dated {j u size:ℕ}(age:t=j+1)(inside:b<t ∧ t+1<K)
      (paid:WilsonReceivedChronologicalDualInterval.Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows j u b s P size η):
      Route b K t s P η

theorem charged {b K:ℕ}(active:b<K)(s:(marks).Mode)(P:ℕ)(η:ℝ)
    (sales:∀i∈Ico b K,Route (N:=N) R simple hk D Q π Γ Ψ books ahead rows b K i s (P+1) η):
    (∀ i:ℕ,b ≤ i → i ≤ K → Integrable (rows i) (prior G _)) ∧
     ∀W:Config G (R.family.side b per), flags (R.family.path.rep N per b).p.threshold W=∅ →
      (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per)
        (R.family.path.β N per (b+1)) W))^2 ≤ 2 →
      ∀i∈Ico b K, ‖WilsonOriginalJointTrialHearing.fee R N per W rows i s‖≤
        wage s (P+1) η*(regulatorRun R.family N per b)^(P+1):=by
  have price (t:ℕ)(h:t∈Ico b K):
      (Integrable (rows (t+1)) (prior G _) ∧ Integrable (rows t) (prior G _)) ∧
      ∀W:Config G (R.family.side b per),flags (R.family.path.rep N per b).p.threshold W=∅ →
        (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per)
          (R.family.path.β N per (b+1)) W))^2 ≤ 2 →
        ‖WilsonOriginalJointTrialHearing.fee R N per W rows t s‖≤wage s (P+1) η*(regulatorRun R.family N per b)^(P+1):=by
    cases sales t h with
    | base _ paid => exact WilsonOriginalOneArmClearCash.earned R simple hk D Q π Γ Ψ books ahead rows (WilsonOriginalOneArmAppointments.material paid)
    | last _ paid => exact WilsonOriginalOneArmClearCash.earned R simple hk D Q π Γ Ψ books ahead rows (WilsonOriginalOneArmAppointments.canonical paid)
    | dated age _ paid => cases age; exact WilsonOriginalOneArmFixedCash.original R simple hk D Q π Γ Ψ books ahead rows paid
  constructor
  · intro i lower upper
    by_cases last:i=K
    · have h:K-1∈Ico b K:=mem_Ico.mpr (by omega)
      have paid:=(price (K-1) h).1.1
      exact Eq.mp (congrArg (fun r:ℕ=>Integrable (rows r) (prior G _)) (by omega : K-1+1=i)) paid
    · exact (price i (mem_Ico.mpr ⟨lower,lt_of_le_of_ne upper last⟩)).1.2
  · intro W clear tilt i member
    exact (price i member).2 W clear tilt

end YM.Integration.WilsonOriginalOneArmSchoolWindow
end
