import YM.Integration.WilsonOriginalAlternativeTrialFunded
import YM.Integration.WilsonOriginalAlternativeTrialIntegrable
import YM.Integration.WilsonOriginalMicroscopicEntrancePublicTrial

/-! Both original endpoint prices on the physical f grid, with the independently bought K pupil identified. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePurchasedField
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

variable {G : Gauge} (R : Run G) {m N per k f n : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (grades : (Fin 3) → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ (f+n))
  (physical : Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3)) → Config G (R.family.side ((f+n)+1) per) → Poly (Stock.census (Fin 3)))


local notation "D_" => (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3))
local notation "K_" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=Fin 3))
open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=Fin 3)) grades order shelf seats (f+n) floor physical)
local notation "J_" => Stock.census (Fin 3)
local notation "A_" => Tint.Patrol.picture P.model P.input
local notation "W_" => Ψ ((f+n)+1)
local notation "α_" => (W_).p.supportExponent
local notation "κ_" => LocalComparison.forcedDivisor R.family ((f+n)+1)



variable (upper:(f+n)+1 ≤ N) (ref:∀ j, R.family.ref (grades j) ≤ (f+n)+1)
  (o:(Fin 3)→Site (R.family.side f per)) (v:∀j,R.family.label (grades j))
local notation "sites_" => WilsonOriginalMicroscopicEntranceGridRow.pin R (Nat.le_add_right f (n+1)) o
local notation "z_" => WilsonOriginalMicroscopicEntranceGridRow.factor R grades ((f+n)+1)
local notation "tuned_" => (fun j=>z_ j • v j)
local notation "top_" => WilsonOriginalAlternativeTrialSource.source R grades N per ((f+n)+1) sites_ v z_
local notation "O_" => Passport.point sites_


open WilsonReceivedFirstTrace
open Pert.Asymptotics
variable (reg:Registration (m:=m) (N:=N) (k:=k) R D Q π Γ Ψ books ahead
  (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3)) shelf seats)
local notation "actor_" j:max f:max t:max => Post (N:=N) R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats j f t
local notation "history_" j:max age:max => WilsonReceivedCloseHistory.history (N:=N) R D_ (top_) j age
local notation "g_" => regulatorRun R.family N per

open Filter WilsonThermometerMixedCollarSubpower
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "mesh" => R.family.S.a
variable (pace:WilsonWindowReportingPace.Slow R.kit)(forecast:WilsonReportLampForecast.Ready R.family.path.levels)
open Multi Comparison.RG02.Cumulants
open WilsonOriginalAlternativeTrialAnyEarlier (degree)


open MeasureTheory WilsonOriginalMicroscopicEntranceTwoExits WilsonOriginalAlternativeTrialFunded
open Comparison.RG02.Cumulants
open WilsonOriginalMicroscopicEntrancePublicTrial
local notation "fi" => Nat.le_add_right f n
local notation "fired_" => WilsonOriginalAlternativeFiniteSource.fired (V:=Fin 3)
local notation "table_" L:max mf:max => Tint.Patrol.report
  (Oak.student (n:=per) R hk D Q π Γ books mf (L).op (L).lesson ahead D_ (L).model order (L).voter)
  (L).output (Coat.gStep (Ψ (f+1)).beta)

theorem original (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(way:WayStation R.kit)
    (q:ℕ)(ε:ℝ)(span power:ℕ)(B:ℝ)
    (bought:Purchased R hk D Q π Γ Ψ books ahead grades order shelf seats (f+n) floor physical P upper
      sites_ v z_ reg pace forecast q ε span power B)
    (mf:m ≤ f)(initial:WilsonOriginalAlternativeTrialPaidCourse.floorAge R grades pace forecast reg.simple span power B ≤ f)
    (optical:mesh f/mesh ((f+n)+1) ≤ (H f)^span):
    ∃U:actor_ (f+n) floor (top_),∃c:Countable U.inputIndex,∃L:actor_ f mf (history_ f (fi)),∃cl:Countable L.inputIndex,
      U.passport=(O_) ∧ U.op=P.op ∧ U.lesson=P.lesson ∧
      Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
        f mf ((fi).trans_lt upper) (history_ f (fi)) L cl ∧
      ∀p:ℕ,∀C e:ℝ,∀(cp:0 ≤ C)(ep:0<e),0<f → cold (V:=Fin 3) R reg.simple power span p C e cp ep ≤ f-1 →
        6*seats ≤ R.alloy.B.a.clock.J f → 5 ≤ (Ψ f).p.B →
        ∀u:ℕ,∀(uf:u ≤ f),m ≤ u → earlier (V:=Fin 3) R reg.simple power span p C e cp ep ≤ u →
        ((f-u:ℕ):ℝ) ≤ C*(1+Real.log (H f)) →
        (∀j k:Fin 3,j≠k → (Ψ f).p.B^2+1 ≤ separation (o j) (o k)) →
        ∀s:(J_).Mode,
        let bK:=fun W:Config G (R.family.side f per)=>∏j∈s.val,((table_ L mf).E.log fired_ W).part ((J_).fire j)
        Integrable (fun U=>(R.family.path.rep N per f).eval U • bK U) (prior G _) ∧
        ∀W,flags (Ψ u).p.threshold W=∅ →
        ‖actualTransport R.family (N:=N) (trialFace R grades (N:=N) (n:=n+1) o v s-bK) uf W‖ ≤ 
          (2*(e*(g_ f)^p))*(shards (J_) s).card:=by
  obtain ⟨U,c,_,_,passport,op,lesson,_,service⟩:=bought
  obtain ⟨_,_,_,L,cl,chain,_,paid⟩:=service f (fi) mf initial optical
  refine ⟨U,c,L,cl,passport,op,lesson,chain,?_⟩
  intro p C e cp ep positive late active wide u uf mu age journey apart s bK
  have due:=WilsonOriginalAlternativeTrialIntegrable.original R hk D Q π Γ Ψ course books mf ahead grades
    order shelf seats (sites_) v (z_) (fi) upper L way active fired_ s
  refine ⟨due.2,?_⟩
  intro W clear
  have receipt:=paid p C e cp ep positive late active wide u uf mu age journey o (fun _=>rfl) apart s W clear
  let response:=WilsonOriginalMicroscopicEntranceEarlier.face
    (WilsonOriginalMicroscopicEntranceGridRow.entered R grades (N:=N) (n:=n+1) o v) s
  have equal:WilsonOriginalAlternativeTrialSource.mode R grades N per ((f+n)+1) sites_ v z_ fired_ s=response:=by
    funext X
    simp only [response,WilsonOriginalAlternativeTrialSource.mode,WilsonOriginalAlternativeFiniteSource.fired,
      one_mul,WilsonOriginalMicroscopicEntranceEarlier.face,WilsonOriginalAlternativeTrialSource.arm,
      WilsonOriginalMicroscopicEntranceGridRow.entered,WilsonOriginalMicroscopicGuardedTrial.guarded]
    rfl
  change ‖actualTransport R.family (N:=N) (fun X=>actualTransport R.family (N:=N) response
    (Nat.le_add_right f (n+1)) X-bK X) uf W‖ ≤ _
  simpa only [equal,bK] using receipt

end YM.Integration.WilsonOriginalMicroscopicEntrancePurchasedField
end
