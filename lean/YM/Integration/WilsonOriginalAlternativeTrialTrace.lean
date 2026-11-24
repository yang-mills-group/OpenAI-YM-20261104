import YM.Integration.WilsonOriginalAlternativeTrialBirth
import YM.Integration.WilsonReceivedFirstTraceHistory

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialTrace
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

include ref in
/-- The tested finite restarted row, its authentic initial wallet, and every
earlier counted post with its actual old/forced returns on the one census. -/
theorem original (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order  ≤  Burn.horizon k+1) (packed:order+shelf  ≤  Burn.horizon k+2)
    (q:ℕ) (deep:2*q+8  ≤  order) (aged:q+3  ≤  3*k+2) {ε τ:ℝ}
    (ep:0<ε) (eu:ε ≤ 1) (pos:0<τ) (small:τ ≤ 1)
    (late:WilsonReceivedMeasuredStampPrice.opening R reg.simple q order k deep aged ep  ≤  m+1)
    (positive:∀ j,m ≤ j → j ≤ N → 0<g_ j ∧ g_ j ≤ 1):
    let w:=WilsonOriginalAlternativeTrialWallet.radius R grades N per (i+1) o tuned_ (α_+1+1) τ
    ∃U:actor_ i floor (top_),∃c:Countable U.inputIndex,
      U.w=w ∧ U.rent=τ ∧ U.cost=0 ∧ U.passport=O_ ∧ U.op=P.op ∧ U.lesson=P.lesson ∧
      (∀x a W,(U.input.hard.hard x a W)=Poly.bead J_ (((W_).activities.K a W:ℝ):ℂ)) ∧
      ∀ f (fi : f ≤ i) (mf : m ≤ f),∃L:actor_ f mf (history_ f fi),∃cl:Countable L.inputIndex,
        Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
          f mf (fi.trans_lt upper) (history_ f fi) L cl ∧ L.rent ≤ τ+∑a∈Finset.Ico f i,ε*(g_ (a+2))^q :=by
  intro w
  obtain ⟨U,c,weight,rent,cost,sites,op,lesson,keys⟩:=WilsonOriginalAlternativeTrialBirth.original
    R hk D Q π Γ Ψ books ahead grades order shelf seats i floor physical P upper ref o v z
    reg.simple reg.course reg.scroll reg.chamber reg.hospital reg.load
    (reg.narrow.trans (R.alloy.B.a.fits.mono floor)) pos small
  refine ⟨U,c,weight,rent,cost,sites,op,lesson,keys,?_⟩
  intro f fi mf
  obtain ⟨L,cl,chain,bill⟩:=WilsonReceivedFirstTrace.descent R hk D Q π Γ Ψ books ahead D_ K_ grades
    order shelf seats reg floor (top_) U c upper q ε path pass month fits packed deep aged ep eu late
    positive f fi mf
  exact ⟨L,cl,chain,rent ▸ bill⟩

end YM.Integration.WilsonOriginalAlternativeTrialTrace
