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
namespace YM.Integration.WilsonOriginalAlternativeTrialFunded
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
open Multi Comparison.RG02.Cumulants
open WilsonOriginalAlternativeTrialAnyEarlier (degree)

def calendar (C:ℝ)(span:ℕ):ℝ:=C+72*((span:ℝ)/Real.log 2)+48
theorem calendar_nonneg {C:ℝ}(cp:0≤C)(span:ℕ):0≤calendar C span:=by
  have pos:0<Real.log 2:=Real.log_pos (by norm_num)
  unfold calendar
  positivity
def capital (power:ℕ):ℕ:=2*(6+power)+1
def cold (simple:G.Simple)(power span p:ℕ)(C e:ℝ)(cp:0≤C)(ep:0<e):ℕ:=
  WilsonOriginalAlternativeTrialAnySettlement.onset (V:=V) R simple (capital power) p (calendar C span) e (calendar_nonneg cp span) ep
def earlier (simple:G.Simple)(power span p:ℕ)(C e:ℝ)(cp:0≤C)(ep:0<e):ℕ:=
  WilsonOriginalAlternativeTrialAnyEarlier.start (V:=V) R simple 1 (capital power*degree V) p (calendar C span) e (calendar_nonneg cp span) ep

/-- The chosen upper and every lower report use the original physical history and the same counted enrolment. -/
def Purchased (q:ℕ)(ε:ℝ)(span power:ℕ)(B:ℝ):Prop:=
    let first:=WilsonOriginalAlternativeTrialPaidCourse.floorAge R grades pace forecast reg.simple span power B
    ∃U:actor_ i floor (top_),∃c:Countable U.inputIndex,
      U.rent=1 ∧ U.cost=0 ∧ U.passport=O_ ∧ U.op=P.op ∧ U.lesson=P.lesson ∧
      (∀x a W,(U.input.hard.hard x a W)=Poly.bead J_ (((W_).activities.K a W:ℝ):ℂ)) ∧
      ∀f (fi:f ≤ i)(mf:m ≤ f),first ≤ f → mesh f/mesh (i+1) ≤ (H f)^span →
        (∀v,(U.w v)⁻¹ ≤ (H f)^(2*(6+power)+1)) ∧ scale (H (i+1)) ≤ 2*scale (H f) ∧
        (((i+1-f:ℕ):ℝ)*Real.log 2 ≤ (span:ℝ)*Real.log (H f)) ∧
        ∃L:actor_ f mf (history_ f fi),∃cl:Countable L.inputIndex,
          Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
            f mf (fi.trans_lt upper) (history_ f fi) L cl ∧ L.rent ≤ 1+∑j∈Finset.Ico f i,ε*(g_ (j+2))^q ∧
          ∀(p:ℕ)(C e:ℝ)(cp:0≤C)(ep:0<e),0<f → cold (V:=V) R reg.simple power span p C e cp ep ≤ f-1 →
          6*seats ≤ R.alloy.B.a.clock.J f → 5 ≤ (Ψ f).p.B →
          ∀(u:ℕ)(uf:u ≤ f)(_mu:m ≤ u),earlier (V:=V) R reg.simple power span p C e cp ep ≤ u →
          ((f-u:ℕ):ℝ) ≤ C*(1+Real.log (H f)) →
          ∀(sites:V→Site (R.family.side f per)),(∀j,o j=(R.family.S.toDepth (fi.trans (Nat.le_succ i)) per).embed (sites j)) →
          (∀j k:V,j≠k → (Ψ f).p.B^2+1 ≤ separation (sites j) (sites k)) →
          ∀(s:(J_).Mode)(W:Config G (R.family.side u per)),flags (Ψ u).p.threshold W=∅ →
            let x:=WilsonOriginalAlternativeFiniteSource.fired (V:=V)
            let student:=Oak.student (n:=per) R hk D Q π Γ books mf L.op L.lesson ahead D_ L.model order L.voter
            let A:=Tint.Patrol.report student L.output (Coat.gStep (Ψ (f+1)).beta)
            let read:=actualTransport R.family (N:=N)
              (WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v z x s) (fi.trans (Nat.le_succ i))
            ‖actualTransport R.family (N:=N) (fun U=>read U-∏j∈s.val,(A.E.log x U).part ((J_).fire j)) uf W‖ ≤
              (2*(e*(g_ f)^p))*(shards (J_) s).card

include ref in
theorem original (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (packed:order+shelf ≤ Burn.horizon k+2)
    (q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)(eu:ε ≤ 1)
    (late:WilsonReceivedMeasuredStampPrice.opening R reg.simple q order k deep aged ep ≤ m+1)
    (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)
    (positive:∀j,m ≤ j → j ≤ N → 0<g_ j ∧ g_ j ≤ 1)
    (placed:(R.family.path.levels.params (i+1)).supportExponent=100)
    (span power:ℕ)(B:ℝ)(income:∀j,(R.family.labels.level (grades j)).coeffSize (tuned_ j) ≤ B*(H (i+1))^power):
    Purchased R hk D Q π Γ Ψ books ahead grades order shelf seats i floor physical P upper o v z reg pace forecast q ε span power B:=by
  unfold Purchased
  intro first
  obtain ⟨U,c,rent,cost,sites,op,lesson,quiet,reach⟩:=WilsonOriginalAlternativeTrialPaidCourse.original R hk D Q π Γ Ψ books ahead
    grades order shelf seats i floor physical P upper ref o v z reg pace forecast path pass month fits packed q deep aged ep eu late positive placed span power B income
  refine ⟨U,c,rent,cost,sites,op,lesson,quiet,?_⟩
  intro f fi mf after window
  obtain ⟨wages,growth,width,L,cl,trace,fare,salary⟩:=reach f fi mf after window
  refine ⟨wages,growth,width,L,cl,trace,fare,?_⟩
  intro p C e cp ep it age active wide u uf mu old outer homes stamps distant s W clear
  have inherited:=WilsonOriginalAlternativeTrialChainSites.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace fi homes (by intro j; rw [sites]; exact stamps j)
  have apart (j l:V)(h:j≠l): (Ψ f).p.B^2+1 ≤ separation ((L.passport.coarser (R.family.path.levels.clock.op f per).ratio).origin j)
      ((L.passport.coarser (R.family.path.levels.clock.op f per).ratio).origin l):=by
    rw [inherited j,inherited l]
    exact distant j l h
  have length:=WilsonOriginalAlternativeTrialSpan.original (R.family.path.levels.fits.delayed f).le outer width
  exact WilsonOriginalAlternativeTrialAnySettlement.original R hk D Q π Γ Ψ reg.course books mf ahead grades order shelf seats o v z fi upper L way ticket reg.simple
    (capital power) p (calendar C span) e (calendar_nonneg cp span) ep it age active wide apart u uf mu old length U.w wages growth salary s W clear

end YM.Integration.WilsonOriginalAlternativeTrialFunded
end
