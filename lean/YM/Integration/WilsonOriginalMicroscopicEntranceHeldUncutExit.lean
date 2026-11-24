import YM.Integration.WilsonOriginalMicroscopicEntranceHeldGuardedExit
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldTrialUnmask
import YM.Integration.WilsonOriginalAlternativeTrialIntegrable
import YM.Integration.WilsonMeasuredPublicEntranceHeldDifference

/-! Both genuine K charges under the same clear, possibly nonconstant, earlier field on the already enrolled post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldUncutExit
open MeasureTheory Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
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


open Multi WilsonOriginalAlternativeTrialFunded
local notation "homes_" => (L.passport.coarser (R.family.path.levels.clock.op f per).ratio).origin
local notation "fed_" s:max => actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v z fired_ s) (fi.trans (Nat.le_succ i))
local notation "soft_" j:max X:max => ((gallery_).E.log fired_ X).part ((J_).fire j)

open WilsonOriginalAlternativeTrialPhaseSalary (share share_pos)
open WilsonOriginalAlternativeTrialPhaseCurrency (amount mass units)

open WilsonOriginalAlternativeTrialPhaseSalary (share share_pos reserve reserve_pos within)

open WilsonAddressedFiniteGuardTrial (printed)
open WilsonOriginalMicroscopicEntranceHeldHalo (spring)

/-- The signed original K trial on a genuine clear earlier field, with the same counted programme
and the same physical dose on every proper face. -/
theorem original (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)(q:ℕ)(ε:ℝ)
    (trace:Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
      f mf (fi.trans_lt upper) (history_ f fi) L cl)
    (span power p:ℕ)(C e:ℝ)(cp:0≤C)(ep:0<e)(wages:∀j,(U.w j)⁻¹ ≤ (H f)^(capital power))
    (growth:scale (H (i+1)) ≤ 2*scale (H f))(width:((i+1-f:ℕ):ℝ)*Real.log 2 ≤ (span:ℝ)*Real.log (H f))
    (pos:0<f)(age:cold (V:=V) R reg.simple power span p C (share V e) cp (share_pos V ep) ≤ f-1)
    (stage:6*seats ≤ R.alloy.B.a.clock.J f)(wide:5 ≤ (Ψ f).p.B)
    (origin:U.passport=Passport.point o)(sites:V→Site (R.family.side f per))
    (pins:∀j,o j=(R.family.S.toDepth (fi.trans (Nat.le_succ i)) per).embed (sites j))
    (distant:∀j k:V,j≠k → (Ψ f).p.B^2+1 ≤ separation (sites j) (sites k))
    (u:ℕ)(uf:u≤f)(mu:m≤u)(old:earlier (V:=V) R reg.simple power span p C (share V e) cp (share_pos V ep) ≤ u)
    (outer:((f-u:ℕ):ℝ) ≤ C*(1+Real.log (H f)))
    (s:(J_).Mode)(endpoint:Config G (R.family.side u per))(clear:flags (Ψ u).p.threshold endpoint=∅)
    (fixed:WilsonSingleHardRadius.first R reg.simple ≤ u)
    (B:ℝ)(nonneg:0≤B)(tol:ℝ)(tolp:0<tol)
    (income:∀a,(R.family.labels.level (grades a)).coeffSize (z a • v a)≤B*(H (i+1))^power)
    (support:(R.family.path.levels.params (i+1)).supportExponent≤100)
    (top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (safe:WilsonCenteredCaptureClock.first R reg.simple ≤ i+1)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R reg.simple
      (p+WilsonAddressedFiniteGuardCapital.power R grades power univ) tolp)).choose ≤ i+1):
    let held:=uf.trans (fi.trans (Nat.le_succ i))
    let raw:=actualTransport R.family (N:=N) (printed R grades (N:=N) o v z fired_ s) held endpoint
    let printedAt:=actualTransport R.family (N:=N) (fun W=>∏a∈s.val,soft_ a W) uf endpoint
    let withdrawn:=actualTransport R.family (N:=N) (fun W=>(fed_ s) W-∏a∈s.val,soft_ a W) uf endpoint
    let halo:=WilsonAddressedFiniteGuardHearing.hearing R grades o v z fired_ s
      (show u+1 ≤ i+1 by omega) (N:=N) endpoint
    let active:=e*(regulatorRun R.family N per f)^p
    let guard:=spring R u N per endpoint*WilsonAddressedFiniteGuardEars.fare R (K:=i+1) grades B tol p s.val
    raw-printedAt=withdrawn+halo ∧ ‖withdrawn‖≤active ∧ ‖halo‖≤guard ∧ ‖raw-printedAt‖≤active+guard:=by
  intro held raw printedAt withdrawn halo active guard
  have returned:=WilsonOriginalMicroscopicEntranceHeldGuardedExit.original R hk D Q π Γ Ψ books ahead grades order shelf seats i floor
    upper o v z reg U c f fi mf L cl way ticket q ε trace span power p C e cp ep wages growth width pos age
    stage wide origin sites pins distant u uf mu old outer s endpoint clear
  have regPay:=WilsonOriginalAlternativeTrialIntegrable.original R hk D Q π Γ Ψ reg.course books mf ahead grades
    order shelf seats o v z fi upper L way stage fired_ s
  have written:=WilsonOriginalAlternativeTrialSource.bounded R grades N per (i+1) o v z fired_ s
  have stated:=WilsonMeasuredPublicEntranceHeldDifference.withdraw R upper (fi.trans (Nat.le_succ i)) uf
    (WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v z fired_ s)
    (fun W=>∏a∈s.val,soft_ a W) ⟨written.1,_,written.2⟩ regPay.2 endpoint
  have light:=WilsonOriginalMicroscopicEntranceHeldTrialUnmask.original R π Γ Ψ reg.course upper top reg.simple way D Q ticket
    mu (le_refl u) fixed safe grades o v z fired_ s power p nonneg tolp late (show u+1 ≤ i+1 by omega) support income endpoint
  have identity:raw-printedAt=withdrawn+halo:=by
    change withdrawn=_ at stated
    rw [stated]
    dsimp only [raw,printedAt,halo,WilsonAddressedFiniteGuardHearing.hearing,held]
    ring
  refine ⟨identity,returned,light,?_⟩
  rw [identity]
  exact (norm_add_le ..).trans (add_le_add returned light)

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldUncutExit
end
