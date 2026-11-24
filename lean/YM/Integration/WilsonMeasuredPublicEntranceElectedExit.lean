import YM.Integration.WilsonOriginalAlternativeTrialPublicFlat
import YM.Integration.WilsonOriginalAlternativeTrialOwnerSpine
import YM.Integration.WilsonAddressedFiniteGuardHearing
import YM.Integration.WilsonMeasuredPublicEntranceHeldDifference
import YM.Integration.WilsonMeasuredPublicEntranceSignedEar
import YM.Integration.WilsonMeasuredPublicEntrancePeerTests
/-! The actual returned K pupil, its complete original occupation, and the signed unmasking at the same earlier flat. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceElectedExit
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

open WilsonOriginalAlternativeTrialCoveredChain (later first)
open QuadraticLocal.Tint QuadraticLocal.Advent.Oak QuadraticLocal.Earn Filter MeasureTheory
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonAddressedFiniteGuardTrial (printed)
open WilsonMeasuredPublicEntranceSignedEar (weighted)
private abbrev portfolio {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Marker.Census V}{o:V→Site n}{b:BudgetPoint}
    (_:Lamps T I G b o J):Type:=I

include ref in
theorem original (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)(q:ℕ)(ε:ℝ)
    (trace:Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
      f mf (fi.trans_lt upper) (history_ f fi) L cl)
    (span power p l:ℕ)(C e cap:ℝ)(cp:0≤C)(ep:0<e)(wages:∀j,(U.w j)⁻¹ ≤ (H f)^(capital power))
    (growth:scale (H (i+1)) ≤ 2*scale (H f))(width:((i+1-f:ℕ):ℝ)*Real.log 2 ≤ (span:ℝ)*Real.log (H f))
    (pos:0<f)(age:later (V:=V) R reg.simple span power p C e cp ep ≤ f-1)
    (stage:6*seats ≤ R.alloy.B.a.clock.J f)(wide:5 ≤ (Ψ f).p.B)
    (origin:U.passport=Passport.point o)(sites:V→Site (R.family.side f per))
    (pins:∀j,o j=(R.family.S.toDepth (fi.trans (Nat.le_succ i)) per).embed (sites j))
    (distant:∀j k:V,j≠k → (Ψ f).p.B^2+1 ≤ separation (sites j) (sites k))
    (j:ℕ)(jf:j<f)(old:first (V:=V) R reg.simple span power p (l+Fintype.card V*l) C e cap cp ep ≤ j)
    (outer:((f-j:ℕ):ℝ) ≤ C*(1+Real.log (H f)))
    (path:∀j,Unit×(V×Bool) → Site (R.family.side j per))(anchor:Unit×(V×Bool))
    (at_f:path f=(sites∘Prod.fst)∘Prod.snd)
    (line:∀a,j≤a → a<f → path a=(R.family.path.levels.clock.op a per).ratio.parent ∘ path (a+1))
    (capd:(R.family.path.rep N per j).p.supportExponent ≤ cap)
    (pairs:∀a:Unit×(V×Bool),coverNumber (R.family.path.rep N per j).p.B ({path j anchor,path j a}:Support _) ≤ l)
    (s:(J_).Mode)
    (u:ℕ)(mu:m≤u)(uj:u≤j)(fixed:WilsonSingleHardRadius.first R reg.simple ≤ u)
    (B:ℝ)(nonneg:0≤B)(tol:ℝ)(tolp:0<tol)
    (after:WilsonOriginalAlternativeTrialOwnerCourse.earliest R grades pace forecast reg.simple span≤f)
    (geom:R.family.S.a f/R.family.S.a (i+1)≤(H f)^span)
    (income:∀j,(R.family.labels.level (grades j)).coeffSize (tuned_ j)≤B*(H (i+1))^power)
    (support:(R.family.path.levels.params (i+1)).supportExponent=100)
    (fine:0≤(Ψ f).p.supportExponent+2)
    (top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (safe:WilsonCenteredCaptureClock.first R reg.simple ≤ i+1)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R reg.simple
      (p+WilsonAddressedFiniteGuardCapital.power R grades power univ) tolp)).choose ≤ i+1):
    let hold:=uj.trans jf.le
    let uk:=hold.trans (fi.trans (Nat.le_succ i))
    let cloud:=actualTransport R.family (N:=N) (printed R grades (N:=N) o v z fired_ s) uk 1
    let regAt:=actualTransport R.family (N:=N) (fun W=>∏a∈s.val,soft_ a W) hold 1
    let withdrawn:=actualTransport R.family (N:=N) (fun W=>(fed_ s) W-∏a∈s.val,soft_ a W) hold 1
    let halo:=WilsonAddressedFiniteGuardHearing.hearing R grades o v z fired_ s
      (show u+1≤ i+1 by omega) (N:=N) 1
    let fee:=(e*(g_ f)^p)*(2*((shards (J_) s).card:ℝ)+1)
    let haloFee:=WilsonAddressedFiniteGuardEars.fare R (K:=i+1) grades B tol p s.val
    cloud-regAt=withdrawn+halo ∧ ‖withdrawn‖≤fee ∧ ‖halo‖≤haloFee ∧ ‖cloud-regAt‖≤fee+haloFee:=by
  intro hold uk cloud regAt withdrawn halo fee haloFee
  have refunded:=WilsonOriginalAlternativeTrialPublicFlat.original R hk D Q π Γ Ψ books ahead grades order shelf seats i floor
    upper o v z reg U c f fi mf L cl way ticket q ε trace span power p l C e cap cp ep wages growth width pos age
    stage wide origin sites pins distant j jf old outer path anchor at_f line capd pairs s u mu uj fixed
  have delivered:=WilsonOriginalAlternativeTrialOwnerSpine.original R hk D Q π Γ Ψ books ahead grades order shelf seats i floor
    upper ref o v z reg pace forecast U c f fi mf L cl way q ε trace span power B nonneg after geom income wages
    support origin sites pins 0 (by simpa using stage)
  obtain ⟨_,paid,_,widths,_⟩:=delivered
  letI : Countable L.modelIndex:=L.modelCount
  letI : Countable L.outputIndex:=L.outputCount
  letI learned:Countable (portfolio (rendered learner_ (Ψ f).p (Coat.gStep (Ψ (f+1)).beta))):=
    Scene.crewC L.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books L.op (Oak.era R hk D Q π Γ mf L.op L.lesson)
      (R.alloy.B.a.S.oneStep f per).exact_size L.model order L.voter L.lesson.entry L.lesson.studied ahead)
  let field:=fun a W=>soft_ a W
  let payout:=fun a=>min 1 (w_ a)
  have admitted(a:V):WilsonMeasuredPublicEntranceOrder.BoundedAt R.family (field a):=
    (WilsonMeasuredPublicEntrancePeerTests.trial R (Ψ f) (homes_) a (gallery_).E fired_ payout
      (fun v=>(widths v).1) fine paid).1
  have regular:Integrable (fun W=>((R.family.path.rep N per f).eval W:ℂ)*(∏a∈s.val,field a W)) (prior G _):=by
    have booked:=WilsonMeasuredPublicEntranceSignedEar.weighted_integrable R ((fi.trans (Nat.le_succ i)).trans upper)
      (WilsonMeasuredPublicEntranceOrder.collection R.family field admitted s.val.toList)
    convert booked using 1
    funext W
    change _=_*(s.val.toList.map (fun a=>field a W)).prod
    rw [Finset.prod_map_toList]
  have written:=WilsonOriginalAlternativeTrialSource.bounded R grades N per (i+1) o v z fired_ s
  have complete:funded (WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v z fired_ s):=
    ⟨written.1,_,written.2⟩
  have stated:=WilsonMeasuredPublicEntranceHeldDifference.withdraw R upper (fi.trans (Nat.le_succ i)) hold
    (WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v z fired_ s)
    (fun W=>∏a∈s.val,field a W) complete regular 1
  have light:=WilsonAddressedFiniteGuardHearing.original R π Γ Ψ reg.course upper top reg.simple way D Q ticket
    mu (le_refl u) fixed safe grades o v z fired_ s power p nonneg tolp late (show u+1≤ i+1 by omega)
    (show (R.family.path.levels.budget (i+1)).supportExponent≤100 by exact support.le) income
  have haloBound:‖halo‖≤haloFee:=light.1
  have math:cloud-regAt=withdrawn+halo:=by
    change withdrawn=_ at stated
    rw [stated]
    dsimp only [halo,cloud,regAt,WilsonAddressedFiniteGuardHearing.hearing,uk]
    ring
  refine ⟨math,refunded,haloBound,?_⟩
  rw [math]
  exact (norm_add_le _ _).trans (add_le_add refunded haloBound)

end YM.Integration.WilsonMeasuredPublicEntranceElectedExit
end
