import YM.Integration.WilsonOlderFreshGraphPointPost

/-! The substantive payment and the physical post concern the same finite
film, the same selected root and the same top cutoff that are used on the
independently prescribed normalized graph. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphNamedPost
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
variable (y:Site (R.family.side (i+1) per))
local notation "S"=>WilsonOlderFreshGraphPointWallet.point y
local notation "letterPost"=>Earn.Passport.point (fun _:Unit=>y)

variable (A:Unit→Set ℂ)
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:d<dmax)
    (w:Letter (R.family.labels.level d)) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon
include history scroll chamber warm top cal hospital in
theorem original (simple:G.Simple) (nonbare:i<N) (cap:∀t,‖value A t‖ ≤ 1)
    {τ H:ℝ} (pos:0<τ) (bounded:τ ≤ 1) (positive:0<Ω₀)
    (printed:∃ T:WilsonOlderFreshGraphSlate.Copy G d Q σ₀,
      (∑j,T.fare j) ≤ H ∧ WilsonOlderFreshGraphDatedSalary.Published R L a depth (i+1) w ⟨⟨N,nonbare⟩,f⟩ T)
    (seats:1 ≤ op.count) (shape:op.count=school.pieces) (phase:school.order+1 ≤ op.stage)
    (enrolled:Q ≤ school.order) (order:d ≤ school.horizon) (budget:school.order+d ≤ Burn.horizon k+2)
    (cut:ℕ) (width:Sycamore.Boot.need cut school ≤ R.alloy.B.a.clock.J (i+1))
    (test:Wallet A):
    ∃(T:WilsonOlderFreshGraphSlate.Copy G d Q σ₀)(c amp:ℝ), 0<c ∧ 0<amp ∧ amp⁻¹ ≤ max 1 Ω₀ * (1+H) ∧
      WilsonOlderFreshGraphDatedSalary.Published R L a depth (i+1) w ⟨⟨N,nonbare⟩,f⟩ T ∧
      WilsonOlderFreshGraphHostTarget.Landed (d:=d) (N:=N) R hk D Q₀ π Γ Ψ books hi school ahead A
        (J₀:=T.Roster) (P:=letterPost) (T.rows S A) τ c amp cut:=by
  obtain ⟨T,price,named⟩:=printed
  have awake:=Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
  obtain ⟨c,amp,r₀,w₀,wage,issued⟩:=WilsonOlderFreshGraphPointPost.original R hk D Q₀ π Γ Ψ history scroll
    books chamber hi warm top school op lesson cal ahead hospital y σ₀ T A simple nonbare rfl awake.le cap
    pos bounded positive price seats shape phase enrolled order budget cut width test
  exact ⟨T,c,amp,r₀,w₀,wage,named,issued⟩
end YM.Integration.WilsonOlderFreshGraphNamedPost
end
