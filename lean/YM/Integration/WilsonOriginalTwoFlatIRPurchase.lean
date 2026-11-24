import YM.Integration.WilsonOriginalTwoFlatIRInvoice
import YM.Integration.WilsonOriginalTwoFlatIRMounted

/-! Purchase the independent complete ordinary product at its actual dated teacher on the original course. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPurchase
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology
variable {G:Gauge}
variable (R:Run G) {m n per k:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:(j:ℕ) → RG.Rep G (R.family.side j per))
  {M:ℕ} (c:Concourse R.alloy R.kit R.T π Γ m M per k Ψ) {φ:ℕ → ℕ}
  (books:Mentor.Offices.Books D R.rolls Q φ) (lo:m  ≤  n)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type} [DecidableEq V] [Fintype V] {X:V → Type} [∀ j,AddCommGroup (X j)] [∀ j,Module ℝ (X j)]
  (actors:∀j,Set (X j)) (pieces:∀j,Submodule ℝ (X j)) (grades:V → ℕ)
  (ord shelf seats:ℕ) (source:Wallet actors → Config G (R.family.side (n+1) per) → Poly (Stock.census V))
  (H:WilsonOriginalReceivedChain.Post (N:=M) R hk D Q π Γ Ψ books ahead actors pieces grades
    ord shelf seats n lo source)
local notation "figure" => Oak.figureReal R hk D Q π Γ books lo H.op H.lesson ahead ord shelf
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J n)
local notation "Hβ" => R.alloy.B.a.clock.hatBeta n

local notation "P" => Ψ n
local notation "g" => Coat.gStep (P).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books lo H.op H.lesson ahead ord shelf
local notation "width" => ((P).p.supportExponent+2)
local notation "upper" => (R.alloy.B.a.clock.hatBeta (n+1))

open WilsonIndependentCollarSlateIntensity WilsonRegisteredPairUnaryWallet WilsonOlderFreshGraphSlate WilsonOriginalMixedBlockRows
variable {I marks:Type}[Fintype I][Fintype marks][DecidableEq marks]{P₀:Earn.Passport (R.family.side n per) marks}
    (B:I→Earn.Binder P₀ (Stock.census marks))(costs:marks→ℕ){q:ℕ}
    (T:∀z:I,Copy G (∑v∈(B z).mode.val,costs v) q (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J n)))
local notation "L" => (rendered (mounted B (fun i:I=>(T i).rows (WilsonOlderFreshGraphPointWallet.point (B i).center) disk)) (P).p (g))
local notation "one" => (fun _:marks=>(1:ℝ))
local notation "cash" => (fun i:I=>amount (T i) (B i).center)
local notation "q₀" => ∑i:I,Real.exp ((σ)*(B i).length)*(cash i)
local notation "ink" i:max U:max => ∑'a:(T i).Roster,WilsonGeneralArityCopyAccount.term (T i) (B i).center (g) U a
local notation "F" x:max U:max => ∏i:I,(1+Poly.send (B i).mode ((∏v∈(B i).mode.val,(x v).val)*(ink i U)))

include c in
theorem original (simple:G.Simple)(live:n<M)(large:2 ≤ Hβ)
    (pass:Pass D Q R.alloy R.kit)(hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved:shelf ≤ R.alloy.B.a.clock.J n)(load:H.op.count ≤ Burn.horizon k+2)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ n)
    (time:upper ≤ (3*(regulatorRun R.family M per n)⁻¹)^2)
    (dep:q ≤ ord)(oc:1 ≤ seats)(slots:Fintype.card marks ≤ seats)(fit:(∑v,costs v) ≤ shelf)
    {K:ℝ}{E:ℕ}(income:(q₀) ≤ K*(3*(regulatorRun R.family M per n)⁻¹)^E):
    let g₀:=regulatorRun R.family M per n
    let h:=((2:ℝ)^(ord+shelf+1))^2*max 1 K
    let debt:=(∑v,costs v)+1+2+E
    (∀(x:Wallet (room marks))(W:Config G (R.family.side n per)),Poly.pass (bare (L) x W)=WilsonOriginalTwoFlatIRMounted.value B costs T (g) x W) ∧
    ∃C₀ C₁:ℝ,0 ≤ C₀ ∧ 0 ≤ C₁ ∧ C₀ ≤ h*(3*g₀⁻¹)^debt ∧ C₁ ≤ h*(3*g₀⁻¹)^debt ∧
      (L).Paid (one) (P).p.B (width) C₀ ∧ Gross (L) (one) (P).p.B (width) C₁:=by
  have ⟨grant,fee⟩:=WilsonOriginalTwoFlatIRInvoice.original R hk D Q π Γ Ψ c books lo ahead actors pieces grades
    ord shelf seats source H simple live large pass hospital shelved load onset
  have gap:(g)=regulatorRun R.family M per n:=by rw [(c.1.walk n lo live.le).beta];rfl
  rw [←gap] at time income ⊢
  exact WilsonOriginalTwoFlatIRMounted.original B costs T
    (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J n)).le dep oc slots fit (P).p grant
    (fee.trans (mul_le_mul_of_nonneg_left time (by positivity))) income

end YM.Integration.WilsonOriginalTwoFlatIRPurchase
