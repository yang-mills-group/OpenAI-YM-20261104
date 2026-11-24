import YM.Integration.WilsonOriginalCensusMaterialPosting
import YM.Integration.WilsonOriginalCensusPublicationClock

/-! Publication on the elected opportunity, using only its original calendar and the prior opening. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPublicationLesson
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
variable {n:ℕ}{I:Type}[Fintype I]
  (passport:Earn.Passport (R.family.side (i+1) per) (Fin n))
  (B:I→Earn.Binder passport (Stock.census (Fin n)))(grades:Fin n→ℕ)
  (order shelf q:ℕ)(H₀:Fin n→ℝ)
  (M:WilsonOriginalCensusDatedMaterial.Material R N (i+1) q grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) B)
open WilsonOriginalCensusPublicationClock WilsonOriginalCensusMaterialPosting

include simple course cut hospital cal chamber in
theorem original (pieces stages p:ℕ)(load:Load k q order shelf p grades pieces stages)
    (ready:Open R simple grades pieces stages load i)
    (seats:op.count=pieces)(stage:op.stage=stages)
    (size:∀v,0 < H₀ v){tol:ℝ}(tp:0 < tol)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (pass:Pass D Q R.alloy R.kit)(way:WayStation R.kit):
    Posted R hk D Q π Γ Ψ books hi op lesson ahead passport B grades order shelf q H₀ M tol:=by
  apply WilsonOriginalCensusMaterialPosting.original R simple hk D Q π Γ Ψ course scroll books hi
    cut op lesson cal ahead chamber hospital passport B grades order shelf q H₀ M load.qfit
    (seats ▸ load.occupied) size (by simpa only [Fintype.card_fin,seats] using load.slots)
    (seats ▸ load.count) load.fit ready.level (stage ▸ load.stage) load.expense tp warm atBare pass
    ready.halo ready.onset p way (seats ▸ ready.hard) load.deep load.aged
  · simpa only [seats] using ready.opened
  · simpa only [seats] using ready.more
  · exact ready.cooled
  · exact ready.fresh

end YM.Integration.WilsonOriginalCensusPublicationLesson
end
