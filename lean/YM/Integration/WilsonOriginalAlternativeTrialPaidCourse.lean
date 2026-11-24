import YM.Integration.WilsonOriginalAlternativeTrialTrace
import YM.Integration.WilsonOriginalAlternativeTrialRatedWallet
import YM.Integration.WilsonOriginalAlternativeTrialChainClock
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialPaidCourse
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
def floorAge (simple:G.Simple)(span power:ℕ)(B:ℝ):ℕ:=
  (eventually_atTop.mp (WilsonOriginalAlternativeTrialRatedWallet.original R grades simple pace forecast span power B)).choose

include ref in
theorem original (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (packed:order+shelf ≤ Burn.horizon k+2)
    (q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)(eu:ε ≤ 1)
    (late:WilsonReceivedMeasuredStampPrice.opening R reg.simple q order k deep aged ep ≤ m+1)
    (positive:∀j,m ≤ j → j ≤ N → 0<g_ j ∧ g_ j ≤ 1)
    (placed:(R.family.path.levels.params (i+1)).supportExponent=100)
    (span power:ℕ)(B:ℝ)(income:∀j,(R.family.labels.level (grades j)).coeffSize (tuned_ j) ≤ B*(H (i+1))^power):
    let first:=floorAge R grades pace forecast reg.simple span power B
    ∃U:actor_ i floor (top_),∃c:Countable U.inputIndex,
      U.rent=1 ∧ U.cost=0 ∧ U.passport=O_ ∧ U.op=P.op ∧ U.lesson=P.lesson ∧
      (∀x a W,(U.input.hard.hard x a W)=Poly.bead J_ (((W_).activities.K a W:ℝ):ℂ)) ∧
      ∀f (fi:f ≤ i)(mf:m ≤ f),first ≤ f → mesh f/mesh (i+1) ≤ (H f)^span →
        (∀v,(U.w v)⁻¹ ≤ (H f)^(2*(6+power)+1)) ∧ scale (H (i+1)) ≤ 2*scale (H f) ∧
        (((i+1-f:ℕ):ℝ)*Real.log 2 ≤ (span:ℝ)*Real.log (H f)) ∧
        ∃L:actor_ f mf (history_ f fi),∃cl:Countable L.inputIndex,
          Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
            f mf (fi.trans_lt upper) (history_ f fi) L cl ∧ L.rent ≤ 1+∑j∈Finset.Ico f i,ε*(g_ (j+2))^q ∧
          let Ω:=Oak.expenseReal R hk D Q π Γ books mf L.op L.lesson ahead order shelf
          ∀v,((Stoop.radius L.w (Ω^6)) v)⁻¹ ≤ (U.w v)⁻¹*
            Real.exp ((9*((i+1-f:ℕ):ℝ)+6)*(scale (H (i+1)))^3):=by
  intro first
  obtain ⟨U,c,w,rent,cost,sites,op,lesson,keys,reach⟩:=WilsonOriginalAlternativeTrialTrace.original R hk D Q π Γ Ψ books ahead
    grades order shelf seats i floor physical P upper ref o v z reg path pass month fits packed q deep aged ep eu
    (show (0:ℝ)<1 by norm_num) le_rfl late positive
  refine ⟨U,c,rent,cost,sites,op,lesson,keys,?_⟩
  intro f fi mf after window
  have budget:α_=100:=by
    rw [(reg.course.1.walk (i+1) (floor.trans (Nat.le_succ _)) upper).truep.point]
    exact placed
  obtain ⟨height,width,salary⟩:=(eventually_atTop.mp (WilsonOriginalAlternativeTrialRatedWallet.original
    R grades reg.simple pace forecast span power B)).choose_spec f after (i+1) (fi.trans (Nat.le_succ _)) window
  have allpay:∀j,(U.w j)⁻¹≤(H f)^(2*(6+power)+1):=by
    rw [w,budget]
    exact salary N per upper ref placed o tuned_ income
  obtain ⟨L,cl,trace,checkout⟩:=reach f fi mf
  refine ⟨allpay,height,width,L,cl,trace,checkout,?_⟩
  intro Ω j
  have step:=WilsonOriginalAlternativeTrialChainClock.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace j
  apply step.trans
  have pos:0 ≤ WilsonThermometerMixedCollarSubpower.scale (H (i+1)):=by unfold WilsonThermometerMixedCollarSubpower.scale;linarith only [le_max_left 0 (Real.log (Real.log (H (i+1))))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (U.salary.positive j).le)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg pos 3)
  have mono:((i-f:ℕ):ℝ) ≤ ((i+1-f:ℕ):ℝ):=by exact_mod_cast Nat.sub_le_sub_right (Nat.le_succ i) f
  linarith only [mono]

end YM.Integration.WilsonOriginalAlternativeTrialPaidCourse
end
