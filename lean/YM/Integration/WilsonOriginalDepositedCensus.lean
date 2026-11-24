import YM.Integration.WilsonOriginalMixedBlockFresh
import YM.Integration.WilsonGeneralArityCopyAccount
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
namespace YM.Integration.WilsonOriginalDepositedCensus
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

open WilsonOlderFreshGraphSlate
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
    (passport:Earn.Passport (R.family.side (i+1) per) V)
    (B:I→Earn.Binder passport (Stock.census V)) (grades:V→ℕ)
    (order shelf q:ℕ) (base:V→ℝ)
local notation "dₛ" z:max => (∑v∈(B z).mode.val,grades v)
variable (T:∀z:I,Copy G (∑v∈(B z).mode.val,grades v) q
    (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))))
local notation "point" z:max => WilsonOlderFreshGraphPointWallet.point (B z).center
local notation "A" => WilsonOriginalMixedBlockRows.room V
local notation "K₀" => (fun _:V=>(⊥:Submodule ℝ ℂ))
local notation "gf" => Coat.gStep (H).beta
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "D₀" => (∑v:V,grades v)+1
local notation "ink" z:max y:max U:max => ∑'h:(T z).Roster,
  WilsonGeneralArityCopyAccount.term (T z) (B z).center y U h
local notation "value" z:max y:max x:max U:max => (∏v∈(B z).mode.val,(x v).val)*(ink z y U)
local notation "law" => fun (x:Wallet (A))(U:Config G (R.family.side (i+1) per))=>
  ((H).eval U:ℂ) • ∏z:I,(1+Poly.send (B z).mode (value z (gf) x U))
local notation "Ftype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  (A) (K₀) grades order shelf op.count i hi (law)
local notation "gain" => WilsonOriginalMixedBlockIncome.bill B (σ₀) (fun z=>1+∑j,(T z).fare j) base

private theorem identical {G:Gauge} {n:Side}{V α I₀ I₁:Type}[Fintype V][DecidableEq V]{p₀ p₁:Earn.Passport n V}
    {M₀:I₀ → Earn.Row p₀ (Stock.census V) G α}{M₁:I₁ → Earn.Row p₁ (Stock.census V) G α}
    (ap:p₀=p₁)(idx:I₀=I₁)(same:HEq M₀ M₁)(g:ℝ)(x:α)(U:Config G n):
    Spill.Foundry.uncut M₀ g x U=Spill.Foundry.uncut M₁ g x U:=by
  subst p₁
  subst I₁
  rw [eq_of_heq same]

include simple course cut hospital cal chamber in
theorem original (qfit:q ≤ order) (occupied:1 ≤ op.count)
    (wpos:∀v,0 < base v) (slots:Fintype.card V ≤ op.count) (count:op.count ≤ Burn.horizon k+2)
    (fit:(∑v,grades v) ≤ shelf) (level:shelf ≤ R.alloy.B.a.clock.J i) (stage:order+1 ≤ op.stage)
    (expense:order+(∑v,grades v) ≤ Burn.horizon k+2)
    {tol:ℝ} (tp:0 < tol) (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (pass:Pass D Q R.alloy R.kit)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i):
    ∃F:Ftype, F.passport=passport ∧ F.inputIndex=Empty ∧ F.op=op ∧ F.lesson=lesson ∧
      F.input.hard.Paid F.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      (8*(budgetR R i)^op.count)*F.rent ≤ tol ∧
      (∀v,(F.w v)⁻¹ ≤ (base v)⁻¹*(max 1 (gain))*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2))) ∧
      (∀y:ℝ,0 < y → ∀(x:Wallet (A)) U,
        Spill.Foundry.uncut F.model y x U=∑z:I,Poly.send (B z).mode (value z y x U)) ∧
      ∀x,(Tint.Patrol.picture F.model F.input).density x=(law) x:=by
  let L:=(fun z:I=>(T z).rows (point z) disk)
  let cash:=fun z:I=>1+(T z).cost (point z)
  let values:=fun (z:I)(y:ℝ)(U:Config G (R.family.side (i+1) per))=>ink z y U
  have offers (z:I):=WilsonGeneralArityCopyAccount.original (T z) (B z).center
    (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))).le qfit occupied
    ((Finset.sum_le_sum_of_subset_of_nonneg (f:=grades) (subset_univ _) (fun _ _ _=>Nat.zero_le _)).trans fit)
  obtain ⟨F,atHome,empty,event,calendar,idx,same,forced,fee,wage,slate,posted⟩:=
    WilsonOriginalMixedBlockFresh.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson cal ahead
      chamber hospital passport B L grades order shelf base cash values (fun z=>(offers z).2.1)
      (fun z=>(offers z).2.2.1) (fun z=>(offers z).1) (fun z y _=>(offers z).2.2.2 y)
      wpos slots count fit level stage expense tp warm atBare pass halo onset
  let M:=WilsonOriginalMixedBlockRows.mounted B L
  have capture:(fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (gf) t U))=(law):=by
    funext x U
    exact (congrFun (F.represented x) U).symm.trans (posted x U)
  generalize moved:(law)=newLaw
  rw [←moved,←capture]
  refine ⟨F,atHome,empty,event,calendar,forced,fee,?_,?_,F.represented⟩
  · simpa only [cash,WilsonOlderFreshGraphPointWallet.cost] using wage
  · intro y hy x U
    exact (identical atHome idx same y x U).trans (slate y hy x U)

end YM.Integration.WilsonOriginalDepositedCensus
end
