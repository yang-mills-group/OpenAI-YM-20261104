import YM.Integration.WilsonOriginalAlternativeTrialOwnerCourse
import YM.Integration.WilsonOriginalAlternativeTrialPeerCash
import YM.Integration.WilsonOriginalAlternativeTrialOwnerReading
import YM.Integration.WilsonOriginalAlternativeTrialAnyWallet
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialPeerPurchase
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Source Push.AbsoluteSums

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


private abbrev portfolio {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Marker.Census V}{o:V→Site n}{b:BudgetPoint}
    (_:Lamps T I G b o J):Type:=I

private theorem min_paid {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Marker.Census V}{o:V→Site n}{b:BudgetPoint}
    (E:Lamps T I G b o J){w:V→ℝ}{B:ℕ}{α cost:ℝ}(wp:∀v,0<w v)(earned:E.Paid w B α cost):
    E.Paid (fun v=>min 1 (w v)) B α cost:=by
  have price(v:V):0 < min 1 (w v):=lt_min zero_lt_one (wp v)
  obtain ⟨budget,nonneg,controls,spent⟩:=earned.budget
  refine ⟨budget,nonneg,controls,fun site=>budget_mono (spent site) ?_ ?_⟩
  · intro j;split <;> first | exact mul_nonneg (mul_nonneg (Poly.worth price _).le (nonneg _)) (Real.exp_nonneg _) | rfl
  · intro j;split
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Finset.prod_le_prod
        (fun j _=>(price j).le) (fun j _=>min_le_right 1 (w j))) (nonneg _)) (Real.exp_nonneg _)
    · rfl

def arity(V:Type)[Fintype V]:ℕ:=max 1 (Fintype.card V)

theorem allowance (power span:ℕ)(B:ℝ):0 ≤ WilsonOriginalAlternativeTrialOwnerClock.allowance power span B:=by
  have lp:0 ≤ Real.log 2:=Real.log_nonneg (by norm_num)
  unfold WilsonOriginalAlternativeTrialOwnerClock.allowance
  positivity

def gates (simple:G.Simple)(span power p t:ℕ)(B gap e:ℝ)(gp:0 ≤ gap)(ep:0<e):ℕ×ℕ:=
  let income:=WilsonOriginalAlternativeTrialPeerCash.original R simple (J_) grades (arity V) t p
    (lt_of_lt_of_le zero_lt_one (le_max_left ..)) (le_max_right ..) pace forecast
    (WilsonOriginalAlternativeTrialOwnerClock.allowance power span B) gap e (allowance power span B) gp ep
  (income.choose,(eventually_atTop.mp income.choose_spec).choose)
variable (U:Post (N:=N) R hk D Q π Γ Ψ books ahead
    (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
    grades order shelf seats i floor (WilsonOriginalAlternativeTrialSource.source R grades N per (i+1) o v z))
  (c:Countable U.inputIndex) (j₀:ℕ)
variable (fi:(j₀+1) ≤ i)(mf:m ≤ (j₀+1))
  (L:Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
    (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) grades order shelf seats (j₀+1) mf
    (WilsonReceivedCloseHistory.history (N:=N) R (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
      (WilsonOriginalAlternativeTrialSource.source R grades N per (i+1) o v z) (j₀+1) fi))
  (cl:Countable L.inputIndex)

local notation "Ω_" => Oak.expenseReal R hk D Q π Γ books mf L.op L.lesson ahead order shelf
local notation "w_" => Stoop.radius L.w (Ω_^6)
local notation "fired_" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)
local notation "h_" j:max => WilsonMeasuredSingletonForce.row (F:=R.family.labels.level (grades j)) L.output.hard fired_ j
local notation "learner_" => Oak.student (n:=per) R hk D Q π Γ books mf L.op L.lesson ahead D_ L.model order L.voter
local notation "gallery_" => Tint.Patrol.report learner_ L.output (Coat.gStep (Ψ ((j₀+1)+1)).beta)


local notation "homes_" => (L.passport.coarser (R.family.path.levels.clock.op (j₀+1) per).ratio).origin
local notation "fed_" j:max => actualTransport R.family (N:=N)
  (WilsonOriginalAlternativeTrialSource.arm R grades N per (i+1) o v z j) (fi.trans (Nat.le_succ i))
local notation "soft_" j:max X:max => ((gallery_).E.log fired_ X).part ((J_).fire j)
local notation "P_" => R.family.path.rep N per (j₀+1)
local notation "due_" => LocalComparison.forcedDivisor R.family (j₀+1)

include ref in
/-- Clear earlier fields hear the purchased K-trial error against each
actual mix of its uncut regular peers and the independently filed P peers. -/
theorem original (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)(q:ℕ)(ε:ℝ)
    (trace:Chain R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats reg floor (top_) U c upper q ε
      (j₀+1) mf (fi.trans_lt upper) (history_ (j₀+1) fi) L cl)
    (span power p t:ℕ)(B gap e:ℝ)(bp:0 ≤ B)(gp:0 ≤ gap)(ep:0<e)
    (after:WilsonOriginalAlternativeTrialOwnerCourse.earliest R grades pace forecast reg.simple span ≤ (j₀+1))
    (geometry:(R.family.S.a (j₀+1))/(R.family.S.a (i+1)) ≤ (H (j₀+1))^span)
    (income:∀j,(R.family.labels.level (grades j)).coeffSize (tuned_ j) ≤ B*(H (i+1))^power)
    (started:∀j,(U.w j)⁻¹ ≤ (H (j₀+1))^(2*(6+power)+1))
    (placed:(R.family.path.levels.params (i+1)).supportExponent=100)
    (reached:(R.family.path.levels.params (j₀+1)).supportExponent=100)
    (origin:U.passport=Passport.point o)(sites:V→Site (R.family.side (j₀+1) per))
    (pins:∀j,o j=(R.family.S.toDepth (fi.trans (Nat.le_succ i)) per).embed (sites j))
    (stage:6*seats ≤ R.alloy.B.a.clock.J (j₀+1))
    (b:ℕ)(mb:m≤b)(bt:b≤(j₀+1))
    (gated:(gates R grades pace forecast reg.simple span power p t B gap e gp ep).1 ≤ b)
    (late:(gates R grades pace forecast reg.simple span power p t B gap e gp ep).2 ≤ j₀)
    (time:(((j₀+1)-b:ℕ):ℝ) ≤ gap*(1+Real.log (H (j₀+1)))^4)
    (X:∀j,Coefficient (R.family.labels.level (grades j)) (R.family.side (j₀+1) per))(bank:V→ℝ)
    (bp₀:∀j,0 ≤ bank j)(refs:∀j,R.family.ref (grades j) ≤ (j₀+1))
    (fit:∀j,(X j).Format (sites j) R.family.params (P_))(errors:∀j,(X j).remBound (sites j) (P_) (due_) (bank j))
    (salaries:∀j,WilsonSeparatedPrefixCanonicalMounted.salary R grades (j₀+1) per X bank j ≤ (H (j₀+1))^t)
    (trial:Finset V)(owner:V)(s:(J_).Mode)(present:owner∈s.val):
    let raw:V → Config G (R.family.side (j₀+1) per) → ℂ:=fun j Z=>if j∈trial then soft_ j Z else
      (X j).exponentialEntry (sites j) (R.family.localSection (grades j)) (P_) Z
    ∀ Z:Config G (R.family.side b per),flags (Ψ b).p.threshold Z=∅ →
    ‖actualTransport R.family (N:=N) (fun W=>((fed_ owner) W-soft_ owner W)*∏j∈s.val.erase owner,raw j W) bt Z‖ ≤
      ((H (j₀+1))^p)⁻¹ + (e*(regulatorRun R.family N per (j₀+1))^p)*(Multi.shards (J_) s).card:=by
  intro raw Z clear
  let amount:=WilsonOriginalAlternativeTrialOwnerClock.allowance power span B
  have earn:=WilsonOriginalAlternativeTrialPeerCash.original R reg.simple (J_) grades (arity V) t p
    (lt_of_lt_of_le zero_lt_one (le_max_left ..)) (le_max_right ..) pace forecast amount gap e (allowance power span B) gp ep
  have rates:=(eventually_atTop.mp earn.choose_spec).choose_spec j₀ late
  have showUp:=WilsonOriginalAlternativeTrialOwnerCourse.original R hk D Q π Γ Ψ books ahead grades order shelf seats
    i floor upper ref o v z reg pace forecast U c (j₀+1) fi mf L cl way q ε trace span power B bp after geometry income started
    placed origin sites pins 0 (by simpa only [zero_add] using stage)
  have address:=WilsonOriginalAlternativeTrialChainSites.original R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats
    reg floor (top_) U c upper q ε trace fi sites (by intro j; rw [origin]; exact pins j)
  obtain ⟨soft,wp,_,_⟩:=WilsonOriginalAlternativeTrialAnyWallet.original R hk D Q π Γ Ψ reg.course books mf
    (fi.trans_lt upper) ahead D_ K_ grades order shelf seats (history_ (j₀+1) fi) L way 0 (by simpa only [zero_add] using stage)
  let w:V→ℝ:=fun j=>min 1 (w_ j)
  have widths(j:V):0<w j ∧ w j ≤ 1:=⟨lt_min zero_lt_one (wp j),min_le_left ..⟩
  have staged:1 ≤ H (j₀+1):=(R.family.path.levels.fits.delayed (j₀+1)).le
  have nonneg:0 ≤ WilsonMeasuredPublicEntranceCropClock.span (H (j₀+1)):=by
    unfold WilsonMeasuredPublicEntranceCropClock.span scale
    have logH:=Real.log_nonneg staged
    have high:=le_max_left 0 (Real.log (Real.log (H (j₀+1))))
    positivity
  have paidW(j:V):(w j)⁻¹ ≤ Real.exp (amount*WilsonMeasuredPublicEntranceCropClock.span (H (j₀+1))):=by
    by_cases small:w_ j ≤ 1
    · simpa only [w,min_eq_right small,amount,WilsonMeasuredPublicEntranceCropClock.span] using (showUp j).1
    · rw [show w j=1 from min_eq_left (le_of_not_ge small),inv_one]
      exact Real.one_le_exp (mul_nonneg (allowance power span B) nonneg)
  letI : Countable L.modelIndex:=L.modelCount
  letI : Countable L.outputIndex:=L.outputCount
  letI learned:Countable (portfolio (rendered learner_ (Ψ (j₀+1)).p (Coat.gStep (Ψ ((j₀+1)+1)).beta))):=
    Scene.crewC L.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books L.op (Oak.era R hk D Q π Γ mf L.op L.lesson)
      (R.alloy.B.a.S.oneStep (j₀+1) per).exact_size L.model order L.voter L.lesson.entry L.lesson.studied ahead)
  let peers:=WilsonMeasuredPublicEntranceTrialPeerBoard.field (N:=N) R (J_) grades (homes_) (Ψ (j₀+1)) X (gallery_).E fired_ trial
  have same:peers=raw:=by
    funext j W
    by_cases hit:j∈trial <;> simp only [peers,WilsonMeasuredPublicEntranceTrialPeerBoard.field,raw,hit,if_true,if_false,address j]
    rfl
  obtain ⟨_,format,remn,primary,empty,_,fee,seen⟩:=showUp owner
  have reader:=rates N per m k b (fi.trans (Nat.le_succ i) |>.trans upper) bt gated mb way D Q π Γ Ψ reg.course ticket
    reached (homes_) X w bank _ _ (gallery_).E fired_ trial widths bp₀ refs
    (fun j=>(address j).symm ▸ fit j) (fun j=>(address j).symm ▸ errors j) salaries paidW
    (min_paid (gallery_).E wp soft) time owner s present (h_ owner)
    ((address owner).symm ▸ format) ((address owner).symm ▸ remn) primary empty
    (fun W=>(address owner).symm ▸ (seen W).2) (fee (w owner) (widths owner).1.le (min_le_right ..)) Z clear
  change ‖WilsonOriginalAlternativeHearing.held R.family N per (fun W=>WilsonMeasuredCoefficientTransport.account (h_ owner) (Ψ (j₀+1)) W*
    ∏j∈s.val.erase owner,peers j W) bt Z‖ ≤ _ at reader
  rw [same,WilsonOriginalAlternativeTrialOwnerReading.original R hk D Q π Γ Ψ reg.course books mf ahead grades order
    shelf seats o v z fi upper L way stage owner (fun W=>∏j∈s.val.erase owner,raw j W) b bt Z] at reader
  exact reader

end YM.Integration.WilsonOriginalAlternativeTrialPeerPurchase
end
