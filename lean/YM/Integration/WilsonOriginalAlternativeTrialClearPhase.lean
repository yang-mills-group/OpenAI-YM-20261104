import YM.Integration.WilsonOriginalAlternativeTrialPhysicalPhase
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialClearPhase
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
    (entries:Finset (J_).Mode)(phase:(J_).Mode→ℂ)(r:V→ℝ)(rp:∀a,0≤r a)
    (base dose:V→ℂ)(nz:∀a,dose a≠0)(charged:∀a,z a=dose a*base a):
    let raw:=fun (s:(J_).Mode) (W:Config G (R.family.side f per))=>
      units r grades s*(actualTransport R.family (N:=N)
        (WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v base fired_ s) (fi.trans (Nat.le_succ i)) W-
        (mass dose s)⁻¹*(∏a∈s.val,soft_ a W))
    let total:=fun W=>∑s∈entries,phase s*raw s W
    Integrable (fun W=>(R.family.path.rep N per f).eval W • total W) (prior G _) ∧
    (∀X:Config G (R.family.side u per), actualTransport R.family (N:=N) total uf X=
      ∑s∈entries,phase s*actualTransport R.family (N:=N) (raw s) uf X) ∧
    ∀W:Config G (R.family.side u per),flags (Ψ u).p.threshold W=∅ →
    ‖actualTransport R.family (N:=N) total uf W‖ ≤ (e*(regulatorRun R.family N per f)^p)*
      ∑s∈entries,‖phase s‖*∏a∈s.val,((r a)^(grades a)*‖(dose a)⁻¹‖):=by
  intro raw total
  let factor:=fun s:(J_).Mode=>∏a∈s.val,amount r grades dose a
  let row:=fun (s:(J_).Mode) (W:Config G (R.family.side f per))=>(fed_ s) W-∏a∈s.val,soft_ a W
  have inputEq(s:(J_).Mode):WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v z fired_ s=
      WilsonOriginalAlternativeTrialSource.mode R grades N per (i+1) o v (fun a=>dose a*base a) fired_ s:=by rw [funext charged]
  have exactRow(s:(J_).Mode)(W:Config G (R.family.side f per)):factor s*row s W=raw s W:=by
    unfold factor row raw
    rw [inputEq s]
    exact WilsonOriginalAlternativeTrialPhaseCurrency.signed R grades N per (i+1) o v base dose (fi.trans (Nat.le_succ i))
      fired_ s r nz (fun X=>∏a∈s.val,soft_ a X) W
  let bank:=fun W=>∑s∈entries,(phase s*factor s)*row s W
  have recorded:bank=total:=by
    funext W
    unfold bank total
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_assoc,exactRow]

  have due(s:(J_).Mode):Integrable (fun W=>(R.family.path.rep N per f).eval W • row s W) (prior G _):=by
    have both:=WilsonOriginalAlternativeTrialIntegrable.original R hk D Q π Γ Ψ reg.course books mf ahead grades
      order shelf seats o v z fi upper L way stage fired_ s
    apply (both.1.sub both.2).congr (ae_of_all _ fun W=>?_)
    change (R.family.path.rep N per f).eval W • (fed_ s) W -
      (R.family.path.rep N per f).eval W • (∏a∈s.val,soft_ a W) = (R.family.path.rep N per f).eval W • row s W
    simp only [row,smul_sub]
  have linear:=WilsonOriginalConditionalPhaseSum.original R entries (fun s=>phase s*factor s) row due uf
  refine ⟨?_,?_,?_⟩
  · rw [←recorded]
    exact (linear 1).1
  · intro X
    rw [←recorded,show actualTransport R.family (N:=N) bank uf X=_ from (linear X).2]
    apply Finset.sum_congr rfl
    intro s _
    have rawEq:raw s=fun W=>factor s*row s W:=funext fun W=>(exactRow s W).symm
    rw [rawEq,WilsonMeasuredPublicEntranceGridCurrency.transport]
    exact mul_assoc ..
  · intro W clear
    have stamped:=WilsonOriginalAlternativeTrialChainSites.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
      reg floor (top_) U c upper q ε trace fi sites (by intro j;rw [origin];exact pins j)
    have apart(a b:V)(ne:a≠b):(Ψ f).p.B^2+1 ≤ separation (homes_ a) (homes_ b):=by
      rw [stamped a,stamped b]
      exact distant a b ne
    have length:=WilsonOriginalAlternativeTrialSpan.original (R.family.path.levels.fits.delayed f).le outer width
    have salary:=WilsonOriginalAlternativeTrialFlatChain.salary R hk D Q π Γ Ψ books ahead grades order shelf seats i floor
      upper o v z reg U c f fi mf L cl q ε trace
    have gp:0≤(regulatorRun R.family N per f)^p:=pow_nonneg (by dsimp [regulatorRun];positivity) _
    rw [←recorded,show actualTransport R.family (N:=N) bank uf W=_ from (linear W).2]
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have ear:=WilsonOriginalAlternativeTrialAnySettlement.original R hk D Q π Γ Ψ reg.course books mf ahead grades order
      shelf seats o v z fi upper L way ticket reg.simple (capital power) p (calendar C span) (share V e) (calendar_nonneg cp span) (share_pos V ep)
      pos age stage wide apart u uf mu old length U.w wages growth salary s W clear
    have cap:2*((shards (J_) s).card:ℝ) ≤ reserve V:=by linarith only [within s]
    have price:‖actualTransport R.family (N:=N) (row s) uf W‖ ≤ e*(regulatorRun R.family N per f)^p:=by
      apply ear.trans
      calc (2*(share V e*(regulatorRun R.family N per f)^p))*((shards (J_) s).card:ℝ)
            = (share V e*(regulatorRun R.family N per f)^p)*(2*((shards (J_) s).card:ℝ)):=by ring
           _ ≤ (share V e*(regulatorRun R.family N per f)^p)*reserve V:=
             mul_le_mul_of_nonneg_left cap (mul_nonneg (share_pos V ep).le gp)
           _ = e*(regulatorRun R.family N per f)^p:=by unfold share;field_simp [(reserve_pos V).ne']
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left price (norm_nonneg _)).trans_eq
    rw [mul_comm ‖phase s*factor s‖,show ‖phase s*factor s‖=_ from WilsonOriginalAlternativeTrialPhaseCurrency.cost r grades dose rp (phase s) s]

end YM.Integration.WilsonOriginalAlternativeTrialClearPhase
end
