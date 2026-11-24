import YM.Integration.WilsonOriginalAlternativeTrialFunded
import YM.Integration.WilsonOriginalAlternativeTrialFlatSettlement
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialFlatChain
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

def later (simple:G.Simple)(span power p:ℕ)(C e:ℝ)(cp:0≤C)(ep:0<e):ℕ:=
  WilsonOriginalAlternativeTrialFlatSettlement.onset (V:=V) R simple (capital power) p (calendar C span) e (calendar_nonneg cp span) ep
def first (simple:G.Simple)(span power p:ℕ)(C e:ℝ)(cp:0≤C)(ep:0<e):ℕ:=
  WilsonOriginalAlternativeTrialFlatWallet.start (V:=V) R simple 1 (capital power*WilsonOriginalAlternativeTrialAnyEarlier.degree V) p (calendar C span) e (calendar_nonneg cp span) ep

theorem salary (q:ℕ)(ε:ℝ)(trace:Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
      f mf (fi.trans_lt upper) (history_ f fi) L cl)(j:V):
    (w_ j)⁻¹ ≤ (U.w j)⁻¹*Real.exp ((9*((i+1-f:ℕ):ℝ)+6)*(scale (H (i+1)))^3):=by
  have step:=WilsonOriginalAlternativeTrialChainClock.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace j
  apply step.trans
  have pos:0 ≤ scale (H (i+1)):=by unfold WilsonThermometerMixedCollarSubpower.scale;linarith only [le_max_left 0 (Real.log (Real.log (H (i+1))))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (U.salary.positive j).le)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg pos 3)
  have mono:((i-f:ℕ):ℝ) ≤ ((i+1-f:ℕ):ℝ):=by exact_mod_cast Nat.sub_le_sub_right (Nat.le_succ i) f
  linarith only [mono]

theorem original (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)(q:ℕ)(ε:ℝ)
    (trace:Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
      f mf (fi.trans_lt upper) (history_ f fi) L cl)
    (span power p:ℕ)(C e:ℝ)(cp:0≤C)(ep:0<e)(wages:∀j,(U.w j)⁻¹ ≤ (H f)^(capital power))
    (growth:scale (H (i+1)) ≤ 2*scale (H f))(width:((i+1-f:ℕ):ℝ)*Real.log 2 ≤ (span:ℝ)*Real.log (H f))
    (pos:0<f)(age:later (V:=V) R reg.simple span power p C e cp ep ≤ f-1)
    (stage:6*seats ≤ R.alloy.B.a.clock.J f)(wide:5 ≤ (Ψ f).p.B)
    (origin:U.passport=Passport.point o)(sites:V→Site (R.family.side f per))
    (pins:∀j,o j=(R.family.S.toDepth (fi.trans (Nat.le_succ i)) per).embed (sites j))
    (distant:∀j k:V,j≠k → (Ψ f).p.B^2+1 ≤ separation (sites j) (sites k))
    (j:ℕ)(jf:j<f)(old:first (V:=V) R reg.simple span power p C e cp ep ≤ j)
    (outer:((f-j:ℕ):ℝ) ≤ C*(1+Real.log (H f)))
    (s:(J_).Mode)(Z:Support (R.family.side j per))(center:Site (R.family.side j per))(home:center∈Z)
    (homes:∀a∈s.val,WilsonOriginalOccupiedCorridor.sites R sites jf.le a∈Z)
    (u:ℕ)(mu:m≤u)(uj:u≤j)(fixed:WilsonSingleHardRadius.first R reg.simple ≤ u):
    let fee:=Poly.toll (WilsonOriginalOccupiedCorridor.wallet R w_ jf.le) s
    let covered:=4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ j).p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta j*(LocalComparison.forcedDivisor R.family j)
    ‖actualTransport R.family (N:=N) (fun W=>(fed_ s) W-∏a∈s.val,soft_ a W) (uj.trans jf.le) 1‖ ≤
      (e*(regulatorRun R.family N per f)^p)*(2*((shards (J_) s).card:ℝ)+covered):=by
  have a:=WilsonOriginalAlternativeTrialChainSites.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace fi sites (by intro v; rw [origin]; exact pins v)
  have same:(homes_)=sites:=funext a
  have apart (x y:V)(different:x≠y):(Ψ f).p.B^2+1 ≤ separation (homes_ x) (homes_ y):=by
    rw [a x,a y]; exact distant x y different
  have shared:∀x∈s.val,WilsonOriginalOccupiedCorridor.sites R (homes_) jf.le x∈Z:=by rw [same]; exact homes
  have length:=WilsonOriginalAlternativeTrialSpan.original (R.family.path.levels.fits.delayed f).le outer width
  apply WilsonOriginalAlternativeTrialFlatSettlement.original R hk D Q π Γ Ψ reg.course books mf ahead grades order shelf seats o v z fi upper L way ticket reg.simple
    (capital power) p (calendar C span) e (calendar_nonneg cp span) ep pos age stage wide apart j jf old length U.w wages growth _ s Z center home shared u mu uj fixed
  exact salary R hk D Q π Γ Ψ books ahead grades order shelf seats i floor upper o v z reg U c f fi mf L cl q ε trace

end YM.Integration.WilsonOriginalAlternativeTrialFlatChain
end
