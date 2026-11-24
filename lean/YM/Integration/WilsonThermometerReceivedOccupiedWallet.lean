import YM.Integration.WilsonThermometerReceivedHardNodes

/-! The actual appointment prints the before-restoration raw forced salary on its final ordinary three-name field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerReceivedOccupiedWallet
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {X : (Fin 3) → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : (Fin 3) → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3)))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf

local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "gauge" => (Tint.Patrol.report student P.output (Coat.gStep (Ψ (i+1)).beta))
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "heat" => R.alloy.B.a.clock.hatBeta (i+1)

include course cut in
theorem original (way:WayStation R.kit)(q:ℕ)(stage:q+6*seats≤R.alloy.B.a.clock.J i):
    (gauge).E.Paid weights (Ψ i).p.B ((Ψ i).p.supportExponent+2) 1 ∧
    (∀v,0<weights v) ∧
    (gauge).K.Paid weights (Ψ i).p.B (Ψ i).p.supportExponent ((heat^q)⁻¹*κ) ∧
    (∀x,LocalComparison.actualPush R.family N per i (physical x)= (gauge).density x):=by
  obtain ⟨soft,wp,_,body⟩:=WilsonThermometerReceivedHardNodes.original R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P way q stage
  have tiny:=WilsonReceivedForcedExit.original R hk D Q π Γ Ψ books ahead actors pieces
    grades order shelf seats hi physical P cut way course q stage
  have smaller(v):weights v≤P.w v:=div_le_self (P.salary.positive v).le (one_le_pow₀ P.issued.Waffle.cool)
  have rel:=WilsonOriginalFiledHardRebill.smaller P.output.hard wp smaller tiny
  have hp:0<heat:=zero_lt_one.trans_le (R.alloy.B.a.fits.delayed _).le
  rw [Real.rpow_neg hp.le,Real.rpow_natCast] at rel
  exact ⟨soft,wp,rel,body⟩

end YM.Integration.WilsonThermometerReceivedOccupiedWallet
