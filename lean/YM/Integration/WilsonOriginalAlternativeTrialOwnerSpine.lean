import YM.Integration.WilsonOriginalAlternativeTrialPeerPurchase
import YM.Integration.WilsonOriginalAlternativeTrialUnitExpense
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialOwnerSpine
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

open WilsonOriginalAlternativeTrialOwnerCourse (earliest)
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

local notation "wage_" => (fun j=>min 1 (w_ j))
local notation "homes_" => (L.passport.coarser (R.family.path.levels.clock.op f per).ratio).origin

include ref in
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
    let bill:=WilsonOriginalAlternativeTrialOwnerClock.allowance power span B*WilsonMeasuredPublicEntranceCropClock.span (H f)
    (homes_)=sites ∧
    (gallery_).E.Paid wage_ (Ψ f).p.B ((Ψ f).p.supportExponent+2) 1 ∧
    (gallery_).K.Paid wage_ (Ψ f).p.B (Ψ f).p.supportExponent
        (((H (f+1))^paid)⁻¹*LocalComparison.forcedDivisor R.family f) ∧
    (∀j,0 < wage_ j ∧ wage_ j ≤ 1 ∧ (wage_ j)⁻¹ ≤ Real.exp bill) ∧
    ∀j:V,let h:=h_ j
      let M:=(L.w j)⁻¹*(H (f+1))^(-(paid:ℝ))
      h.Format (sites j) R.family.params (Ψ f) ∧
      h.remBound (sites j) (Ψ f) (LocalComparison.forcedDivisor R.family f) M ∧ h.x=0 ∧ h.regular=0 ∧
      (∀a X,h.forced a X=(L.output.hard.hard fired_ a X).part ((J_).fire j)) ∧
      0 ≤ M ∧ 2*((wage_ j)*M) ≤ Real.exp 1 ∧
      ∀X,h.density (sites j) (R.family.localSection (grades j)) (Ψ f) X/((Ψ f).eval X:ℂ)=
        actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.arm R grades N per (i+1) o v z j)
          (fi.trans (Nat.le_succ i)) X-((gallery_).E.log fired_ X).part ((J_).fire j) ∧
      ‖h.density (sites j) (R.family.localSection (grades j)) (Ψ f) X/((Ψ f).eval X:ℂ)‖ ≤ Real.exp bill:=by
  intro bill
  have rows:=WilsonOriginalAlternativeTrialOwnerCourse.original R hk D Q π Γ Ψ books ahead grades order shelf seats i floor
    upper ref o v z reg pace forecast U c f fi mf L cl way q ε trace span power B positive after geometry income started placed origin sites pins paid stage
  have addresses:=WilsonOriginalAlternativeTrialChainSites.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace fi sites (by intro j; rw [origin]; exact pins j)
  obtain ⟨soft,wp,hard,_⟩:=WilsonOriginalAlternativeTrialAnyWallet.original R hk D Q π Γ Ψ reg.course books mf
    (fi.trans_lt upper) ahead D_ K_ grades order shelf seats (history_ f fi) L way paid stage
  have positiveW(j:V):0 < wage_ j:=lt_min zero_lt_one (wp j)
  refine ⟨funext addresses,WilsonOriginalAlternativeTrialUnitExpense.lamps (gallery_).E wp soft,
    WilsonOriginalFiledHardRebill.smaller (gallery_).K positiveW (fun j=>min_le_right 1 (w_ j)) hard,?_,?_⟩
  · intro j
    refine ⟨positiveW j,min_le_left ..,?_⟩
    change (min 1 (w_ j))⁻¹ ≤ Real.exp bill
    by_cases small:w_ j ≤ 1
    · simpa only [min_eq_right small,bill,WilsonMeasuredPublicEntranceCropClock.span] using (rows j).1
    · rw [min_eq_left (le_of_not_ge small),inv_one]
      apply Real.one_le_exp
      apply mul_nonneg (WilsonOriginalAlternativeTrialPeerPurchase.allowance power span B)
      have staged:1 ≤ H f:=(R.family.path.levels.fits.delayed f).le
      have logH:=Real.log_nonneg staged
      unfold WilsonMeasuredPublicEntranceCropClock.span scale
      have high:=le_max_left 0 (Real.log (Real.log (H f)))
      positivity
  · intro j h M
    obtain ⟨_,fmt,fee,zero,empty,all,covered,field⟩:=rows j
    refine ⟨fmt,fee,zero,empty,all,?_,covered (wage_ j) (positiveW j).le (min_le_right ..),?_⟩
    · exact mul_nonneg (inv_nonneg.mpr (L.salary.positive j).le)
        (Real.rpow_nonneg (zero_lt_one.trans (R.family.path.levels.fits.delayed (f+1))).le _)
    · exact field

end YM.Integration.WilsonOriginalAlternativeTrialOwnerSpine
end
