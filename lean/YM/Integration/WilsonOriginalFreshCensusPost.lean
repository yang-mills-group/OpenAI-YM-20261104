import YM.Integration.WilsonOriginalFreshRosterWallet
import YM.Integration.WilsonThermometerRestoredCompactHard
import YM.Integration.WilsonOriginalOccupiedRaffleIndependent
import YM.Integration.WilsonMeasuredSemesterSubpower
import YM.Integration.WilsonOlderFreshHardSite

/-! Fresh finite-census enrollment of the complete real marked log at a prescribed
Wilson date. The invoice uses its original base radii and support reserve. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFreshCensusPost
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  {V ι:Type} [Fintype V] [DecidableEq V] [Countable ι] {X:V → Type}
  [∀ v,AddCommGroup (X v)] [∀ v,Module ℝ (X v)]
  (passport:Earn.Passport (R.family.side (i+1) per) V)
  (A:∀v, Set (X v)) (K:∀v, Submodule ℝ (X v))
  (M:ι → Row passport (Stock.census V) G (Wallet A)) (base:V → ℝ) (grades:V → ℕ) (order shelf:ℕ)
  (voter:Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))

local notation "marks" => Stock.census V
local notation "H" => Ψ (i+1)
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "oldG" => Coat.gStep (H).beta
local notation "newG" => Coat.gStep (Ψ i).beta
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "lamp" => rendered M (H).p oldG
local notation "physical" => fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M oldG t U)
local notation "teacher" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead A M order voter

open WilsonRootedKioskOccupiedSlip



open Filter MintClock
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "D₀" => (∑v:V,grades v)+1
local notation "fee" => WilsonOriginalThreeCompactWallet.fee G (H).p (Page.temperature G 1 χ) oldG
  (scale/4) order op.count shelf (D₀)
local notation "cost" => 8*(budgetR R i)^op.count
local notation "Ptype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K
  grades order shelf op.count i hi (physical)

include simple course cut hospital cal chamber voter in
theorem original (count:op.count ≤ Burn.horizon k+2) (level:shelf ≤ R.alloy.B.a.clock.J i)
    (depth:order ≤ R.alloy.B.a.clock.J (i+1)) {C tol:ℝ} (cp:0 ≤ C) (tp:0 < tol)
    (stock:Scene.Armada M base grades scale C order op.count shelf) (table:Tableau K A M)
    (x₀:Wallet A) (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ) (pass:Pass D Q R.alloy R.kit)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (openDate:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i) :
    ∃ P:Ptype, P.passport=passport ∧ P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      P.modelIndex=ι ∧ HEq P.model M ∧
      P.input.hard.Paid P.w (H).p.B (H).p.supportExponent
        (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      (cost)*P.rent ≤ tol ∧
      (∀v,(P.w v)⁻¹=(base v)⁻¹*(max 1 C)*(max 1 (Ω)+|fee|/Willow.haloSlack (H).p.B)) ∧
      (∀v,(P.w v)⁻¹ ≤ (base v)⁻¹*(max 1 C)*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2))) ∧
      ∀t, (Tint.Patrol.picture P.model P.input).density t=(physical) t := by
  have booked:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i:=hk.trans (R.alloy.B.a.fits.mono hi)
  have next:R.alloy.B.a.clock.J i ≤ R.alloy.B.a.clock.J (i+1):=R.alloy.B.a.fits.mono (Nat.le_succ i)
  have native:=WilsonOriginalOccupiedRaffleIndependent.original R simple warm (f:=i+1) course
    (Nat.le_succ_of_le hi) cut (jet:=Burn.horizon k) ((Nat.le_add_right _ 2).trans (booked.trans next)) depth (level.trans next)
    (count.trans (booked.trans next)) (D₀) halo
  let size:=max 1 C
  let raw:=Stoop.radius base size
  let shrink:=max 1 (Ω)+|fee|/Willow.haloSlack (H).p.B
  let w:=Stoop.radius raw shrink
  let b:=shrink⁻¹*(size⁻¹*C)
  have roof:4 ≤ (Ω):=MintClock.Page.roofers ..
  obtain ⟨pos,one,unit,afford,trial,gross,margin,inverse⟩:=
    WilsonOriginalFreshRosterWallet.original M base grades (H).p stock cp
      (show 0 < (Ω) by linarith only [roof]) native.1
  have resident:=WilsonOlderFreshHardSite.original R chamber.ready D Q π Γ Ψ course chamber.station
    (Nat.le_succ_of_le hi) atBare cut
  let τ:=min 1 (tol/(1+|cost|))
  have den:0 < 1+|cost|:=by linarith only [abs_nonneg (cost)]
  have born:0 < τ:=lt_min zero_lt_one (div_pos tp den)
  have limit:τ*(1+|cost|) ≤ tol:=(le_div_iff₀ den).mp (min_le_right ..)
  obtain ⟨P,rad,rental,_,site,blank,event,weather,idx,model,hard⟩:=
    WilsonThermometerRestoredCompactHard.original R simple hk D Q π Γ Ψ course scroll books hi cut
      op lesson cal ahead chamber hospital passport A K M w grades order shelf voter count level
      trial table x₀ unit afford born (min_le_left ..) resident pos one (by rfl) gross margin
  have charged:=WilsonMeasuredSemesterSubpower.charged R hk D Q π Γ Ψ course books hi cut ahead
    A K grades order shelf op.count (physical) P 1 (by norm_num:0<(1:ℝ)) openDate pass hospital level
    (by simpa only [event] using count)
  simp only [pow_one,Real.rpow_one,event,weather] at charged
  have actual:max 1 (Ω) ≤ χ:=max_le (R.alloy.B.a.fits.delayed _).le charged
  refine ⟨P,site,blank,event,weather,idx,model,hard,?_,?_,?_,P.represented⟩
  · rw [rental]
    exact (mul_le_mul_of_nonneg_right ((le_abs_self (cost)).trans (by linarith:|cost| ≤ 1+|cost|)) born.le).trans
      ((mul_comm ..).le.trans limit)
  · intro v
    rw [rad]
    exact inverse v
  · intro v
    rw [rad,inverse v]
    exact mul_le_mul_of_nonneg_left (add_le_add actual native.2)
      (mul_nonneg (inv_nonneg.mpr (stock.positive v).le) (zero_le_one.trans (le_max_left ..)))

end YM.Integration.WilsonOriginalFreshCensusPost
end
