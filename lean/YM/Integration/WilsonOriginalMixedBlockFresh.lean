import YM.Integration.WilsonOriginalFreshCensusPost
import YM.Integration.WilsonOriginalMixedBlockIncome
import YM.Integration.WilsonOriginalMixedBlockTable
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
namespace YM.Integration.WilsonOriginalMixedBlockFresh
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

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Filter MintClock Multi
local notation "H" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] {O:I→Type} [∀i,Countable (O i)]
    (passport:Earn.Passport (R.family.side (i+1) per) V)
    (B:I→Earn.Binder passport (Stock.census V))
    (X:(i:I)→O i→Earn.Row (Passport.point (fun _:Unit=>(B i).center)) (Stock.census Unit) G (Wallet disk))
    (grades:V→ℕ) (order shelf:ℕ) (base:V→ℝ) (cash:I→ℝ)
    (values:I → ℝ → Config G (R.family.side (i+1) per)→ℂ)
local notation "student" => mounted B X
local notation "A" => WilsonOriginalMixedBlockRows.room V
local notation "K₀" => (fun _:V=>(⊥:Submodule ℝ ℂ))
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (H).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "C₀" => WilsonOriginalMixedBlockIncome.bill B (σ₀) cash base
local notation "D₀" => (∑v:V,grades v)+1
local notation "law" => fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (student) (gf) t U)
local notation "Ptype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  (A) (K₀) grades order shelf op.count i hi (law)

include simple course cut hospital cal chamber in
theorem original (rooted:∀j z,(X j z).binder=WilsonOlderFreshGraphPointWallet.point (B j).center)
    (linear:∀j z,∃c:ℂ,∀x:Wallet disk,(X j z).paint x=c*WilsonThermometerRegisteredCapturedSector.amplitude disk x)
    (earned:∀i,Scene.Armada (X i) (fun _:Unit=>1) (fun _:Unit=>∑v∈(B i).mode.val,grades v)
      (σ₀) (cash i) order op.count shelf)
    (declared:∀j y,0 < y → ∀(x:Wallet disk) U,
      HasSum (fun z=>(X j z).nominal y x U) ((x ()).val*values j y U))
    (wpos:∀v,0 < base v) (slots:Fintype.card V ≤ op.count) (count:op.count ≤ Burn.horizon k+2)
    (fit:(∑v,grades v) ≤ shelf) (level:shelf ≤ R.alloy.B.a.clock.J i) (stage:order+1 ≤ op.stage)
    (expense:order+(∑v,grades v) ≤ Burn.horizon k+2)
    {tol:ℝ} (tp:0 < tol) (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (pass:Pass D Q R.alloy R.kit)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i):
    ∃F:Ptype, F.passport=passport ∧ F.inputIndex=Empty ∧ F.op=op ∧ F.lesson=lesson ∧
      F.modelIndex=((j:I)×O j) ∧ HEq F.model (student) ∧
      F.input.hard.Paid F.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      (8*(budgetR R i)^op.count)*F.rent ≤ tol ∧
      (∀v,(F.w v)⁻¹ ≤ (base v)⁻¹*(max 1 (C₀))*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2))) ∧
      (∀ y:ℝ,0 < y → ∀(x:Wallet (A)) U,
        Spill.Foundry.uncut (student) y x U=∑j,Poly.send (B j).mode
          ((∏v∈(B j).mode.val,(x v).val)*values j y U)) ∧
      ∀(x:Wallet (A)) U,(Tint.Patrol.picture F.model F.input).density x U =
        ((H).eval U:ℂ) • ∏j,(1+Poly.send (B j).mode ((∏v∈(B j).mode.val,(x v).val)*values j (gf) U)):=by
  let M:=mounted B X
  have stock:=WilsonOriginalMixedBlockIncome.funded B X rooted grades (σ₀) cash earned base wpos slots fit
  have tested:=WilsonOriginalMixedBlockRows.tested B X linear
  have opened:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i:=hk.trans (R.alloy.B.a.fits.mono hi)
  have orderFit:order ≤ R.alloy.B.a.clock.J i:=(Nat.le_add_right _ _).trans (expense.trans opened)
  have voter:Mentor.Cruise.Voter M (σ₀) order op.count op.stage k (R.alloy.B.a.clock.J i):=by
    refine ⟨fun z=>⟨stock.honor z,stock.purchases.spend z,((stock.purchases.usable z).1).trans orderFit,?_⟩,
      stock.quota,stage,fun club=>?_⟩
    · rw [(stock.purchases.usable z).2]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (f:=grades) (subset_univ _) (fun _ _ _=>Nat.zero_le _)).trans (fit.trans level)
    · rw [Press.tall M club grades stock.purchases.usable]
      exact (Nat.add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg (f:=grades) (subset_univ _) (fun _ _ _=>Nat.zero_le _)) order).trans expense
  have cp:0 ≤ (C₀):=budget_nonneg (stock.suggests 0)
  let seed:Wallet (A):=fun _=>⟨1,by simp [WilsonOriginalMixedBlockRows.room,disk]⟩
  obtain ⟨F,homes,empty,co,date,idx,model,hard,rent,_,rad,physical⟩:=
    WilsonOriginalFreshCensusPost.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson
    cal ahead chamber hospital passport (A) (K₀) M base grades order shelf voter count level
    (orderFit.trans (R.alloy.B.a.fits.mono (Nat.le_succ i))) cp tp stock tested seed atBare warm pass halo onset
  have ticket (y:ℝ)(hy:0 < y)(x:Wallet (A))(U:Config G (R.family.side (i+1) per)):=
    WilsonOriginalMixedBlockTable.original B X y x U (fun j=>(∏v∈(B j).mode.val,(x v).val)*values j y U)
      (fun j=>declared j y hy _ U)
  have positive:0 < (gf):=by
    rw [(course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  refine ⟨F,homes,empty,co,date,idx,model,hard,rent,rad,fun y hy x U=>(ticket y hy x U).1,?_⟩
  intro x U
  exact (congrFun (physical x) U).trans
    (congrArg (fun d=>((H).eval U:ℂ) • d) (ticket (gf) positive x U).2)

end YM.Integration.WilsonOriginalMixedBlockFresh
end
