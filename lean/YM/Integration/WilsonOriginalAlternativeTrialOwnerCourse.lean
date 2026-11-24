import YM.Integration.WilsonOriginalAlternativeTrialGuardField
import YM.Integration.WilsonOriginalAlternativeTrialOwnerField
import YM.Integration.WilsonOriginalAlternativeTrialOwnerClock
import YM.Integration.WilsonOriginalAlternativeTrialPaidCourse
import YM.Integration.WilsonOriginalAlternativeTrialChainSites
import YM.Integration.WilsonOriginalAlternativeTrialAnySettlement
import YM.Integration.WilsonOriginalAlternativeTrialSpan
import YM.Integration.WilsonOriginalAlternativeTrialTrace
import YM.Integration.WilsonOriginalAlternativeTrialRatedWallet
import YM.Integration.WilsonOriginalAlternativeTrialChainClock
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialOwnerCourse
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V]
  (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m  ≤  i)
  (physical : Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) → Config G (R.family.side (i+1) per) → Poly (Stock.census V))


local notation "D_" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "K_" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) grades order shelf seats i floor physical)
local notation "J_" => Stock.census V
local notation "A_" => Tint.Patrol.picture P.model P.input
local notation "W_" => Ψ (i+1)
local notation "α_" => (W_).p.supportExponent
local notation "κ_" => LocalComparison.forcedDivisor R.family (i+1)



variable (upper:i+1  ≤  N) (ref:∀ j, R.family.ref (grades j)  ≤  i+1)
  (o:V→Site (R.family.side (i+1) per)) (v:∀j,R.family.label (grades j)) (z:V→ℂ)
local notation "tuned_" => (fun j=>z j • v j)
local notation "top_" => WilsonOriginalAlternativeTrialSource.source R grades N per (i+1) o v z
local notation "O_" => Passport.point o


open WilsonReceivedFirstTrace
open Pert.Asymptotics
variable (reg:Registration (m:=m) (N:=N) (k:=k) R D Q π Γ Ψ books ahead
  (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) shelf seats)
local notation "actor_" j:max f:max t:max => Post (N:=N) R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats j f t
local notation "history_" j:max age:max => WilsonReceivedCloseHistory.history (N:=N) R D_ (top_) j age
local notation "g_" => regulatorRun R.family N per

open Filter WilsonThermometerMixedCollarSubpower
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "mesh" => R.family.S.a
variable (pace:WilsonWindowReportingPace.Slow R.kit)(forecast:WilsonReportLampForecast.Ready R.family.path.levels)
open WilsonThermometerMixedCollarSubpower

def earliest (Gsimple:G.Simple)(span:ℕ):ℕ:=
  max (eventually_atTop.mp (WilsonOriginalAlternativeTrialGuardField.original R grades Gsimple pace forecast)).choose
    (eventually_atTop.mp (WilsonOriginalAlternativeTrialScales.original R Gsimple span)).choose

variable (U:Post (N:=N) R hk D Q π Γ Ψ books ahead
    (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
    grades order shelf seats i floor (WilsonOriginalAlternativeTrialSource.source R grades N per (i+1) o v z))
  (c:Countable U.inputIndex) (f:ℕ)(fi:f ≤ i)(mf:m ≤ f)
  (L:Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
    (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) grades order shelf seats f mf
    (WilsonReceivedCloseHistory.history (N:=N) R (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
      (WilsonOriginalAlternativeTrialSource.source R grades N per (i+1) o v z) f fi))
  (cl:Countable L.inputIndex)

local notation "Ω_" => Oak.expenseReal R hk D Q π Γ books mf L.op L.lesson ahead order shelf
local notation "w_" => Stoop.radius L.w (Ω_^6)
local notation "fired_" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)
local notation "h_" j:max => WilsonMeasuredSingletonForce.row (F:=R.family.labels.level (grades j)) L.output.hard fired_ j
local notation "learner_" => Oak.student (n:=per) R hk D Q π Γ books mf L.op L.lesson ahead D_ L.model order L.voter
local notation "gallery_" => Tint.Patrol.report learner_ L.output (Coat.gStep (Ψ (f+1)).beta)

include ref in
/-- Pays the authentic trial source's complete signed hard part, including original
quiet partners, at the very centers in the accepted finite chain. -/
theorem original (way:WayStation R.kit) (q:ℕ)(ε:ℝ)
    (trace:Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
      f mf (fi.trans_lt upper) (history_ f fi) L cl)
    (span power:ℕ)(B:ℝ)(positive:0 ≤ B)
    (after:earliest R grades pace forecast reg.simple span ≤ f)
    (geometry:(R.family.S.a f)/(R.family.S.a (i+1)) ≤ (H f)^span)
    (income:∀j,(R.family.labels.level (grades j)).coeffSize (tuned_ j) ≤ B*(H (i+1))^power)
    (started:∀j,(U.w j)⁻¹ ≤ (H f)^(2*(6+power)+1))
    (placed:(R.family.path.levels.params (i+1)).supportExponent=100)
    (origin:U.passport=Passport.point o)(sites:V→Site (R.family.side f per))
    (pins:∀j,o j=(R.family.S.toDepth (fi.trans (Nat.le_succ i)) per).embed (sites j))
    (paid:ℕ)(stage:paid+6*seats ≤ R.alloy.B.a.clock.J f):
    let size:=(1+Real.log (H f))*(scale (H f))^3
    let bill:=WilsonOriginalAlternativeTrialOwnerClock.allowance power span B*size
    ∀j:V,let h:=h_ j
      let M:=(L.w j)⁻¹*(H (f+1))^(-(paid:ℝ))
      (w_ j)⁻¹ ≤ Real.exp bill ∧
      h.Format (sites j) R.family.params (Ψ f) ∧
      h.remBound (sites j) (Ψ f) (LocalComparison.forcedDivisor R.family f) M ∧ h.x=0 ∧ h.regular=0 ∧
      (∀a X,h.forced a X=(L.output.hard.hard fired_ a X).part ((J_).fire j)) ∧
      (∀ tested:ℝ, 0 ≤ tested → tested ≤ w_ j → 2*(tested*M) ≤ Real.exp 1) ∧
      ∀X,h.density (sites j) (R.family.localSection (grades j)) (Ψ f) X/((Ψ f).eval X:ℂ)=
        actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.arm R grades N per (i+1) o v z j)
          (fi.trans (Nat.le_succ i)) X-((gallery_).E.log fired_ X).part ((J_).fire j) ∧
      ‖h.density (sites j) (R.family.localSection (grades j)) (Ψ f) X/((Ψ f).eval X:ℂ)‖ ≤ Real.exp bill:=by
  intro size bill j h M
  have ltK:=fi.trans (Nat.le_succ i)
  have before:=(le_max_left _ _).trans after
  obtain ⟨heat,scales,time⟩:=(eventually_atTop.mp (WilsonOriginalAlternativeTrialScales.original R reg.simple span)).choose_spec f
    ((le_max_right _ _).trans after) (i+1) ltK geometry
  have guard:=(eventually_atTop.mp (WilsonOriginalAlternativeTrialGuardField.original R grades reg.simple pace forecast)).choose_spec
    (i+1) (before.trans ltK) N per upper ref placed o v z j
  have later:=WilsonOriginalAlternativeTrialChainClock.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace j
  have term:((i-f:ℕ):ℝ)*Real.log 2 ≤ (span:ℝ)*Real.log (H f):=by
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le_sub_right (Nat.le_succ i) f))
      (Real.log_nonneg (by norm_num))).trans time
  have salaries:=WilsonOriginalAlternativeTrialOwnerClock.original power span (i-f)
    (R.family.path.levels.fits.delayed f).le (R.family.path.levels.fits.delayed (i+1)).le
    heat scales term positive (income j) (later.trans (mul_le_mul_of_nonneg_right (started j) (Real.exp_nonneg _)))
  have row:=WilsonOriginalAlternativeTrialOwnerField.original R hk D Q π Γ Ψ reg.course books mf ahead
    grades order shelf seats o v z fi upper L way paid stage j _ guard
  have address:=WilsonOriginalAlternativeTrialChainSites.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace fi sites (by intro a; rw [origin]; exact pins a) j
  rw [←address]
  obtain ⟨fmt,fee,zero,empty,owners,entrance,field⟩:=row
  exact ⟨salaries.1,fmt,fee,zero,empty,owners,entrance,fun X=>⟨(field X).1,((field X).2).trans salaries.2⟩⟩

end YM.Integration.WilsonOriginalAlternativeTrialOwnerCourse
end
