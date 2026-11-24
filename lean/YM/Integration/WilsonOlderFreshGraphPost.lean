import YM.Integration.WilsonOlderFreshGraphHost
import YM.Integration.WilsonOlderFreshGraphHostTarget
import YM.Integration.WilsonOlderFreshGraphSlate

/-! Fresh submission of a funded independent column above a genuine nonbare
date. Boot supplies the whole original quiet vacuum, all original owners,
and their mandatory mask-slip alternatives. The charged objects are the
published group words, without a previously installed occupied row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphPost
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m i N per k Q d:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ hi)
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
variable {P:Earn.Passport (R.family.side (i+1) per) Unit}(S:Earn.Binder P (Stock.census Unit))
variable (σ:ℝ) (T:WilsonOlderFreshGraphSlate.Copy G d Q σ) (A:Unit→Set ℂ)
local notation "M₀"=> T.rows S A
local notation "S₀"=> (fun _:Unit=>(⊥:Submodule ℝ ℂ))
local notation "P₀"=> Ψ (i+1)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon
local notation "head"=> (fun (x:Wallet A) (U:Config G (R.family.side (i+1) per))=> (↑((P₀).eval U):ℂ) •
  Poly.pass (Spill.Foundry.uncut M₀ (Coat.gStep (P₀).beta) x U))
local notation "post"=>WilsonOriginalReceivedChain.Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead A S₀
  (fun _=>d) school.order school.horizon school.pieces i hi (head)

include history scroll chamber warm top cal hospital in
theorem original (simple:G.Simple) (nonbare:i<N) (issuedWidth:σ=σ₀) (σpos:0 ≤ σ) (cap:∀t,‖value A t‖ ≤ 1)
    {τ c w:ℝ} (pos:0<τ) (bounded:τ ≤ 1) (unit:c ≤ 1) (afford:c ≤ (Ω₀)⁻¹)
    (surplus:0<c) (w0:0<w) (fee:w*T.cost S ≤ c) (seats:1 ≤ op.count)
    (shape:op.count=school.pieces) (phase:school.order+1 ≤ op.stage) (enrolled:Q  ≤  school.order)
    (order:d  ≤  school.horizon) (budget:school.order+d ≤ Burn.horizon k+2)
    (cut:ℕ) (width:Sycamore.Boot.need cut school  ≤  R.alloy.B.a.clock.J (i+1))
    (test:Wallet A):
    WilsonOlderFreshGraphHostTarget.Landed (d:=d) (N:=N) R hk D Q₀ π Γ Ψ books hi school ahead A
      (J₀:=T.Roster) (P:=P) M₀ τ c w cut := by
  have right:=hk.trans (R.alloy.B.a.fits.mono hi)
  have reserve:school.horizon ≤ R.alloy.B.a.clock.J i:=
    (Nat.le_add_left _ _).trans (school.tall.trans right)
  have qo:Q ≤ R.alloy.B.a.clock.J i:=enrolled.trans
    ((Nat.le_add_right school.order school.horizon).trans (school.tall.trans right))
  exact WilsonOlderFreshGraphHost.original R hk D Q₀ π Γ Ψ history scroll books chamber hi warm top
    school op lesson cal ahead hospital A M₀ simple nonbare pos bounded unit afford shape
    (by rw [←issuedWidth];exact T.earnings S A σpos cap w c w0 surplus fee enrolled seats order)
    (by rw [←issuedWidth];exact T.voted S A cap seats phase budget qo (order.trans reserve)) (T.assays S A) cut width test
end YM.Integration.WilsonOlderFreshGraphPost
end
