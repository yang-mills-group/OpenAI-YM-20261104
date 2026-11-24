import YM.Integration.WilsonOlderFreshGraphHost
import YM.Integration.WilsonOlderFreshUnaryStock
/-! Plant one grouped ordinary source on its original nonbare time and
vacuum. All Laurent charges in its physical row, including its constant
angular face, remain in the original model. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshUnaryCourse
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
theorem original (simple:G.Simple)(nonbare:i<N)(pass:Pass D Q₀ R.alloy R.kit)
    {τ b:ℝ}(pos:0<τ)(fraction:τ≤1)(cost:0≤b)
    (shape:op.count=school.pieces)(ready:school.order+1≤op.stage)(pole:d ≤ school.horizon)
    (stock:Scene.Armada M₀ (fun _:Unit=>(1:ℝ)) (fun _=>d) σ₀ b school.order op.count school.horizon)
    (audit:Tableau S₀ A M₀)
    (cut:ℕ)(width:Sycamore.Boot.need cut school ≤ R.alloy.B.a.clock.J (i+1))(test:Wallet A):
    ∃(c w:ℝ)(F:post),0<c ∧ c≤1 ∧ c≤(Ω₀)⁻¹ ∧ 0<w ∧ w⁻¹=max 1 (Ω₀)*(1+b) ∧
      F.passport=P ∧ F.w=(fun _=>w) ∧ F.cost=c ∧ F.rent=τ ∧ F.modelIndex=J₀ ∧ HEq F.model M₀ ∧
      (∀ (a:ℝ)(B:ℕ),F.input.old.Paid (fun _=>w) B a 0) ∧
      F.input.hard.Paid (fun _=>w) (P₀).p.B (P₀).p.supportExponent
        (forcedDivisor R.family (i+1)*(R.alloy.B.a.clock.hatBeta (i+1))^(-(cut:ℝ))) :=by
  have right:=hk.trans (R.alloy.B.a.fits.mono hi)
  have licensed:=school.tall.trans right
  have rank:school.order+d≤Burn.horizon k+2:=(Nat.add_le_add_left pole _).trans school.tall
  have reserve:school.horizon ≤ R.alloy.B.a.clock.J i:=(Nat.le_add_left ..).trans licensed
  have vote:=WilsonOlderFreshUnaryVoter.original M₀ (fun _:Unit=>(1:ℝ)) d school.order op.count school.horizon
    σ₀ b stock ready rank ((Nat.le_add_right ..).trans licensed) (pole.trans reserve)
  let iw:=history.1.walk i hi nonbare.le
  let jw:=history.1.walk (i+1) (Nat.le_succ_of_le hi) nonbare
  let pay:=(WilsonMovingMentorIncomingSlots.original R history hi nonbare).2.2.choose
  have band:(Ψ (i+1)).beta∈Shoot.band R.alloy.B.a (i+1):=jw.beta ▸
    (R.makes.wilson.represents N per (i+1) nonbare).band
  have receipt:=Mentor.Cruise.Semester.tight D R.rolls Q₀ R.alloy R.kit φ books pass op
    (Oak.era R hk D Q₀ π Γ hi op lesson) (R.alloy.B.a.S.oneStep i per).exact_size M₀
    school.order vote ahead jw.truep.point pay iw.truep.point hospital (shape.trans_le school.sense) school.horizon reserve band
  obtain ⟨c,w,cp,small,allowed,wp,inverse,armed⟩:=WilsonOlderFreshUnaryStock.funded M₀
    (fun _:Unit=>(1:ℝ)) d school.order op.count school.horizon σ₀ b stock cost receipt.2.paysAbove
  simp only [mul_one] at armed
  obtain ⟨F,file⟩:=WilsonOlderFreshGraphHost.original R hk D Q₀ π Γ Ψ history scroll books chamber hi
    warm top school op lesson cal ahead hospital A M₀ simple nonbare pos fraction small allowed shape
    armed vote audit cut width test
  exact ⟨c,w,F,cp,small,allowed,wp,inverse,file⟩

end YM.Integration.WilsonOlderFreshUnaryCourse
end
