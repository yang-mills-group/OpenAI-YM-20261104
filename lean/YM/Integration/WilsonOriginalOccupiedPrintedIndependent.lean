import YM.Integration.WilsonOriginalOccupiedRaffleIndependent
import YM.Integration.WilsonOriginalOccupiedIncidence
import YM.Integration.WilsonOriginalOccupiedFiledFare
import YM.Integration.WilsonOlderFreshThermometerReceipt
import YM.Integration.WilsonReceivedClosePhysicalBirths

/-! The three finite dated slots, their true filed optical slice and its receiving wages. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedPrintedIndependent
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash WilsonOriginalThreeCompactProduct
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

local notation "H" => Ψ (i+1)
local notation "g" => Coat.gStep (H).beta
variable {I:Type} [Fintype I] {q:ℕ} (owner:I→Fin 3) (grades:Fin 3→ℕ)
  (sites:Fin 3→Site (R.family.side (i+1) per))
  (T:(z:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner z)) q (Poetry.Agenda.seed (G:=G) (U:=R.metals.K) (F:=R.metals.p.profile) (K:=R.metals.p.kernel) D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))))
  (A:Fin 3→Set ℂ) (charge:I→ℂ) (order shelf:ℕ)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "S₀" => (fun _:Fin 3=>(⊥:Submodule ℝ ℂ))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "wage" => WilsonOriginalPointCompactSalary.invoice owner grades sites T charge
local notation "physical" => (fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) t U))

attribute [local irreducible] Poetry.Agenda.seed


open Pressure MintClock
local notation "width₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "heat" => Page.temperature G 1 χ
local notation "billing" => WilsonOriginalThreeCompactWallet.fee G (H).p heat (g) (width₀/4)
    order op.count shelf ((∑v:Fin 3,grades v)+1)


open Filter
local notation "batch" x:max => (fun U=>((H).eval U:ℂ) • ∏v:Fin 3,(1+Poly.send ((J).fire v) (value owner
  (fun z=>WilsonOriginalPointCompactFaces.amount owner grades sites T A charge z (g) x U) v)))
local notation "ready" l:max => WilsonMeasuredSemesterSubpower.onset R l (by norm_num:0<(1:ℝ))
local notation "facePole" => ((∑v:Fin 3,grades v)+1)
local notation "printed" => WilsonOlderFreshThermometerReceipt.Printed (N:=N) R hk D Q π Γ Ψ books hi op lesson
  ahead owner grades sites T A charge order shelf
local notation "Ptype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A (S₀) grades
  order shelf op.count i hi (physical)
local notation "made" P:max => Oak.student (n:=per) R hk D Q π Γ books hi (P).op (P).lesson ahead A
  (P).model order (P).voter
include course cut hospital in
theorem original (a:ℕ)(pass:Pass D Q R.alloy R.kit)(way:WayStation R.kit)(p:ℕ)
    (hardFloor:6*op.count ≤ R.alloy.B.a.clock.J i)(deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple op.count p order k deep aged (by norm_num:0<(1:ℝ)) ≤ i)
    (shelved:shelf ≤ R.alloy.B.a.clock.J i)(load:op.count ≤ Burn.horizon k+2)
    (one:ready 1 ≤ i)(more:ready op.count ≤ i)
    (cooled:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ i+1)
    {cap ticket τ:ℝ}(rent:τ ≤ 1)(paid:printed cap ticket τ)(x:Wallet A)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(depth:order ≤ R.alloy.B.a.clock.J (i+1))
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (fresh:(eventually_atTop.mp (WilsonOriginalOccupiedIncidence.original R simple 3 a
      (order+shelf+1+facePole) (facePole+2))).choose ≤ i)
    (cash0:0 ≤ 1+ceiling I cap ticket)(cash:1+ceiling I cap ticket ≤ (R.alloy.B.a.clock.hatBeta i)^a):
    ∃(P:Ptype)(row:WilsonOriginalOccupiedWindow.Slice R J (Ψ i)),
      P.passport=Passport.point sites ∧ P.rent=τ ∧ P.op=op ∧ P.lesson=lesson ∧
      row.w=P.w ∧ row.hard=1 ∧ WilsonOriginalOccupiedSalary.debit row.regular row.hard ≤ 10*χ ∧
      (∀v,(row.w v)⁻¹ ≤ (1+ceiling I cap ticket)*
        (χ+2^(order+shelf+1+facePole)*χ^(facePole+2))) ∧
      (∀s:(J).Mode,(WilsonOriginalOccupiedSalary.debit row.regular row.hard)^s.val.card ≤
        (R.alloy.B.a.clock.hatBeta i)^((a+facePole+5)*3)*Poly.toll row.w s) ∧
      row.A.density row.x=LocalComparison.actualPush R.family N per i (batch x) ∧
      ∀U,row.A.E.log row.x U=(rendered (made P) (Ψ i).p (g)).log x U+P.output.old.log x U:=by
  obtain ⟨P,rentP,_,_,homes,_,po,pl,_,_,_,exactW,_,field⟩:=paid
  have count: P.op.count=op.count:=congrArg _ po
  have source:∀s:(J).Mode,(∑v∈s.val,grades v)+1 ≤ facePole:=fun s=>Nat.succ_le_succ
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s.val) (fun _ _ _=>Nat.zero_le _))
  have hit:=WilsonOriginalOccupiedFiledSlice.original R hk D Q π Γ Ψ books hi cut ahead A (S₀)
    grades order shelf op.count (physical) P simple way course facePole p source hardFloor deep aged
    (by norm_num:0<(1:ℝ)) (by simpa only [count] using opened) x
  obtain ⟨row,ww,reg,hard,all,lamps,_⟩:=hit
  have batchEq:(physical) x=batch x:=by
    funext U
    exact (congrFun (P.represented x) U).symm.trans (field x U)
  have cold:=(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec (i+1)
    cooled N per cut
  have small:Pert.Asymptotics.regulatorRun R.family N per (i+1) ≤ 1:=by linarith only [cold.1,cold.2]
  have fare:=WilsonOriginalOccupiedFiledFare.original R hk D Q π Γ Ψ course books hi cut ahead A (S₀)
    grades order shelf op.count (physical) P pass hospital shelved (by simpa only [count] using load) one (by simpa only [count] using more)
    (rentP.trans_le rent) p 1 (by
      rw [one_mul]; change (Pert.Asymptotics.regulatorRun R.family N per (i+1))^p ≤ 1
      exact pow_le_one₀ cold.1.le small)
  have amount:WilsonOriginalOccupiedSalary.debit row.regular row.hard ≤ 10*χ:=by simpa only [reg,hard] using fare
  have tall:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J (i+1):=hk.trans (R.alloy.B.a.fits.mono (hi.trans (Nat.le_succ i)))
  have HΩ:=WilsonMeasuredSemesterSubpower.charged R hk D Q π Γ Ψ course books hi cut ahead A (S₀) grades order shelf
    op.count (physical) P 1 (by norm_num:0<(1:ℝ)) one pass hospital shelved (by simpa only [count] using load)
  simp only [pow_one,Real.rpow_one,po,pl] at HΩ
  have pace:max 1 Ω ≤ χ:=max_le (R.alloy.B.a.fits.delayed _).le HΩ
  have raw:=(WilsonOriginalOccupiedRaffleIndependent.original R simple warm course (hi.trans (Nat.le_succ i))
    cut (by omega:Burn.horizon k ≤ R.alloy.B.a.clock.J (i+1)) depth
    (shelved.trans (R.alloy.B.a.fits.mono (Nat.le_succ i))) (load.trans tall) facePole halo).2
  have roof:∀v,(row.w v)⁻¹ ≤ (1+ceiling I cap ticket)*(χ+2^(order+shelf+1+facePole)*χ^(facePole+2)):=by
    intro v
    rw [ww,exactW]
    exact mul_le_mul_of_nonneg_left (add_le_add pace raw) cash0
  refine ⟨P,row,homes,rentP,po,pl,ww,hard,amount,roof,?_,all.trans (congrArg (LocalComparison.actualPush R.family N per i) batchEq),lamps⟩
  intro s
  have card:s.val.card ≤ 3:=by simpa only [Fintype.card_fin] using Finset.card_le_univ s.val
  exact (eventually_atTop.mp (WilsonOriginalOccupiedIncidence.original R simple 3 a
    (order+shelf+1+facePole) (facePole+2))).choose_spec i fresh s card row.w row.positive
    (zero_le_one.trans (le_max_left ..)) amount cash0 cash roof

end YM.Integration.WilsonOriginalOccupiedPrintedIndependent
end
