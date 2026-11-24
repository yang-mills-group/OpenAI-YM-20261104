import YM.Integration.WilsonOlderFreshUnaryCourse

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshAuxiliaryPost
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m i N per k:ℕ}
  (hk:Burn.horizon k+2    ≤    R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (hi:m   ≤   i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ hi)
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))

def actors : Unit → Set ℂ:=fun _=>Set.univ
def zeroRows (G:Gauge)(n:Side):Empty → Row (Passport.point (fun _:Unit=>(0:Site n)))
    (Stock.census Unit) G (Wallet actors):=Empty.elim

private theorem treasury (G:Gauge)(n:Side)(σ:ℝ)(order seats shelf:ℕ)(one:1 ≤ seats):
    Scene.Armada (zeroRows G n) (fun _=>1) (fun _=>0) σ 0 order seats shelf:=by
  refine ⟨⟨?_,?_⟩,by simp,?_,?_,fun i=>i.elim⟩
  · intro s
    have h:=Finset.card_le_univ s.val
    exact (by simpa using h : s.val.card ≤ 1).trans one
  · simp
  · intro u
    refine ⟨fun e=>e.elim,?_,by simp⟩
    convert (summable_zero : Summable (0:Empty → ℝ)) using 1
  · exact ⟨fun i=>i.elim,fun i=>i.elim⟩

def booked (G:Gauge){n:Side}(P:RG.Rep G n)(t:Wallet actors)(U:Config G n):
    Poly (Stock.census Unit) := (↑(P.eval U):ℂ) •
      Poly.pass (Spill.Foundry.uncut (zeroRows G n) (Coat.gStep P.beta) t U)

include history chamber warm top cal hospital in
theorem original (simple:G.Simple)(active:i<N)(pass:Pass D Q₀ R.alloy R.kit)
    (seats:1 ≤ op.count)(shape:op.count=school.pieces)(stage:school.order+1 ≤ op.stage)
    (width:Sycamore.Boot.need 0 school  ≤  R.alloy.B.a.clock.J (i+1)):
    Nonempty (WilsonOriginalReceivedChain.Post (N:=N) (V:=Unit) (X:=fun _=>ℂ)
       R hk D Q₀ π Γ Ψ books ahead actors (fun _=>(⊥:Submodule ℝ ℂ)) (fun _=>0)
       school.order school.horizon op.count i hi (booked G (Ψ (i+1)))):=by
  let test:Wallet actors:=fun _=>⟨0,Set.mem_univ _⟩
  have tab:Tableau (fun _:Unit=>(⊥:Submodule ℝ ℂ)) actors (zeroRows G (R.family.side (i+1) per)):=
    ⟨fun e=>e.elim⟩
  have stock:=treasury G (R.family.side (i+1) per) σ₀ school.order op.count school.horizon seats
  obtain ⟨_,_,F,_⟩:=WilsonOlderFreshUnaryCourse.original (d:=0) (N:=N) R hk D Q₀ π Γ Ψ history
    scroll books chamber hi warm top school op lesson cal ahead hospital actors (zeroRows G _)
    simple active pass (τ:=1) zero_lt_one le_rfl (b:=0) le_rfl shape stage (Nat.zero_le _) stock tab 0 width test
  rw [shape]
  exact ⟨F⟩

end YM.Integration.WilsonOlderFreshAuxiliaryPost
end
