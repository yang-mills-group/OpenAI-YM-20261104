import YM.Integration.WilsonOlderFreshGraphWallet
import YM.Integration.WilsonOlderFreshIssuedIntake

/-! Fresh submission of a funded independent column above a genuine nonbare
date. Boot supplies the whole original quiet vacuum, all original owners,
and their mandatory mask-slip alternatives. The charged objects are the
published group words, without a previously installed occupied row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphHost
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m i N per k d:ℕ}
  (hk:Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (hi:m  ≤  i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ hi)
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
variable {P:Earn.Passport (R.family.side (i+1) per) Unit} (A:Unit→Set ℂ)
variable {J₀:Type}[Countable J₀] (M₀:J₀→Row P (Stock.census Unit) G (Wallet A))
local notation "S₀"=> (fun _:Unit=>(⊥:Submodule ℝ ℂ))
local notation "P₀"=> Ψ (i+1)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon
local notation "head"=> (fun (x:Wallet A) (U:Config G (R.family.side (i+1) per))=> (↑((P₀).eval U):ℂ) •
  Poly.pass (Spill.Foundry.uncut M₀ (Coat.gStep (P₀).beta) x U))
local notation "post"=>WilsonOriginalReceivedChain.Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead A S₀
  (fun _=>d) school.order school.horizon school.pieces i hi (head)

include history scroll chamber warm top cal hospital in
theorem original (simple:G.Simple) (nonbare:i<N)
    {τ c w:ℝ} (pos:0<τ) (bounded:τ ≤ 1) (unit:c ≤ 1) (afford:c ≤ (Ω₀)⁻¹)
    (shape:op.count=school.pieces)
    (stock:Scene.Armada M₀ (fun _=>w) (fun _=>d) σ₀ c school.order op.count school.horizon)
    (vote:Cruise.Voter M₀ σ₀ school.order op.count op.stage k (R.alloy.B.a.clock.J i))
    (audit:Tableau S₀ A M₀)
    (cut:ℕ) (width:Sycamore.Boot.need cut school  ≤  R.alloy.B.a.clock.J (i+1))
    (test:Wallet A):
    ∃ F:post,F.passport=P ∧ F.w=(fun _=>w) ∧ F.cost=c ∧ F.rent=τ ∧
      F.modelIndex=J₀ ∧ HEq F.model M₀ ∧
      (∀ (a:ℝ) (B:ℕ),F.input.old.Paid (fun _=>w) B a 0) ∧
      F.input.hard.Paid (fun _=>w) (P₀).p.B (P₀).p.supportExponent
        (forcedDivisor R.family (i+1)*(R.alloy.B.a.clock.hatBeta (i+1))^(-(cut:ℝ))) := by
  have reserve:school.horizon   ≤   R.alloy.B.a.clock.J i:=
    (Nat.le_add_left _ _).trans (school.tall.trans (hk.trans (R.alloy.B.a.fits.mono hi)))
  have stock1:Scene.Armada M₀ (fun _=>w) (fun _=>d) σ₀ 1 school.order school.pieces school.horizon:=by
    rw [←shape]
    exact stock.higher unit
  obtain ⟨Z,entry⟩:=Sycamore.Boot.launching R hk D Q₀ π Γ Ψ history scroll books chamber
    (hi.trans i.le_succ) nonbare A S₀ (fun _=>w) (fun _=>d) school M₀ stock1 audit warm top cut width
  have zero (a:ℝ) (B:ℕ):Z.old.Paid (fun _=>w) B a 0:=Spill.Foundry.empty_lit (P₀) Z a B
  have forced:=entry.crown
  have hard:Z.hard.Paid (fun _=>w) (P₀).p.B (P₀).p.supportExponent
      (forcedDivisor R.family (i+1)):=by
    apply Hard.mono _ forced
    have one : 1 ≤ R.alloy.B.a.clock.hatBeta (i+1) := (R.alloy.B.a.fits.delayed (i+1)).le
    exact mul_le_of_le_one_right (Graces.glyphBound R.alloy.B.a (i+1)).1.le
      (Real.rpow_le_one_of_one_le_of_nonpos one (neg_nonpos.mpr (Nat.cast_nonneg _)))
  have reg:=Z.old.loan_monotone (zero (P₀).p.supportExponent (P₀).p.B) pos.le
  obtain ⟨J,count,out,stamp⟩:=Oak.Buffered.arrive R simple hk D Q₀ π Γ Ψ history scroll books chamber
    hi nonbare op lesson cal ahead hospital A S₀ M₀ Z (fun _=>w) (fun _=>d) school.order school.horizon
    vote τ c (shape.trans_le school.sense) reserve stock audit test entry.clothes.seeds entry.clothes.supplementary
    reg (Hard.mono _ hard (Graces.glyphBound R.alloy.B.a (i+1)).2) unit pos bounded
  let F:post:={
    op:=op
    capacity:=shape
    lesson:=lesson
    passport:=P
    modelIndex:=J₀
    inputIndex:=Empty
    outputIndex:=J
    modelCount:=inferInstance
    outputCount:=count
    model:=M₀
    input:=Z
    output:=out
    w:=(fun _=>w)
    cost:=c
    rent:=τ
    affordable:=afford
    active:=pos
    small:=bounded
    voter:=vote
    salary:=stock
    tests:=audit
    oldTests:=entry.clothes.seeds
    hardTests:=entry.clothes.supplementary
    regular:=Z.old.loan_monotone (zero _ _) pos.le
    forced:=hard
    represented:=fun x=>funext (fun U=>(entry.face x U).2.2)
    issued:=stamp }
  exact ⟨F,rfl,rfl,rfl,rfl,rfl,HEq.rfl,zero,forced⟩
end YM.Integration.WilsonOlderFreshGraphHost
end
