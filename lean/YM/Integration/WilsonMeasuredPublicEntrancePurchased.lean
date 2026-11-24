import YM.Integration.WilsonMeasuredPublicEntranceEntered
import YM.Integration.WilsonOriginalAlternativeTrialFunded
/-! The authentic registered course purchases the separate K-born trial and all of its
true returns before the earlier endpoint or its occupied face is read. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePurchased
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V]
  (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m ≤ i)
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



variable (upper:i+1 ≤ N) (ref:∀ j, R.family.ref (grades j) ≤ i+1)
  (o:V → Site (R.family.side (i+1) per)) (v:∀j,R.family.label (grades j)) (z:V → ℂ)
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

variable (k₀:ℕ)(fi:k₀+1 ≤ i)(mf:m ≤ k₀+1)
local notation "fired_" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)
open Multi WilsonOriginalAlternativeTrialFunded
open WilsonOriginalAlternativeTrialCoveredChain (later first)
open QuadraticLocal.Tint QuadraticLocal.Advent.Oak QuadraticLocal.Earn Filter MeasureTheory
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonAddressedFiniteGuardTrial (printed)
open WilsonMeasuredPublicEntranceSignedEar (weighted)
private abbrev portfolio {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Marker.Census V}{o:V → Site n}{b:BudgetPoint}
    (_:Lamps T I G b o J):Type:=I


open Labels Source RG12 Extra.Histories Motion Bandage Trace.Physical.GermGraph
open WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open WilsonThermometerReflectedTrajectory WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale
open WilsonThermometerMarchSource WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open RG05Readout RG05Readout.Native RG05Readout.Address Ac GridApprox.Nil MergeProof MergeProof.Accent
open RG05Readout.Many RG05Readout.Pantry Records WilsonThermometerUnitFilingCoarse
open WilsonAddressedAlignedColumn WilsonReflectedPublicOrientedFaces
local notation "C₀" => R.family
local notation "G₀" => R.family.path.levels
local notation "S₀" => Stock.census V
local notation "X" => Unit×(V×Bool)
local notation "wage_" => (fun a=>min 1 (w_ a))
local notation "hard_" j:max => WilsonMeasuredSingletonForce.row (F:=R.family.labels.level (grades j)) L.output.hard fired_ j

local notation "ord" => WilsonMeasuredPublicEntranceFixedBill.order
include P mf ref in
theorem _root_.YM.Integration.WilsonMeasuredPublicEntrancePurchased.original
    (route:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(packed:order+shelf ≤ Burn.horizon k+2)
    (q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)(eu:ε ≤ 1)
    (gate:WilsonReceivedMeasuredStampPrice.opening R reg.simple q order k deep aged ep ≤ m+1)
    (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)
    (positive:∀x,m ≤ x→x ≤ N→0<g_ x ∧ g_ x ≤ 1)
    (span power:ℕ)(B:ℝ)(nonneg:0 ≤ B)
    (after:WilsonOriginalAlternativeTrialOwnerCourse.earliest R grades pace forecast reg.simple span ≤ (k₀+1))
    (geom:R.family.S.a (k₀+1)/R.family.S.a (i+1) ≤ (H (k₀+1))^span)
    (income:∀j,(R.family.labels.level (grades j)).coeffSize (tuned_ j) ≤ B*(H (i+1))^power)

    (support:(R.family.path.levels.params (i+1)).supportExponent=100)
    (elected:WilsonOriginalAlternativeTrialPaidCourse.floorAge R grades pace forecast reg.simple span power B ≤ k₀+1)
    (stage:6*seats ≤ R.alloy.B.a.clock.J (k₀+1))
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(cater:Cater (C₀) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (G₀))(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (n apron box requested gross t j l:ℕ)(np:0<n)(size:Fintype.card V ≤ n)(gap:ℝ)(gp:0 ≤ gap)
    (late:(eventually_atTop.mp (WilsonMeasuredPublicEntrancePooledEar.original R grades reg.simple pace nested
      cater bank forecast shop n apron box (ord requested) gross t np size (WilsonOriginalAlternativeTrialOwnerClock.allowance power span B)
      gap (WilsonOriginalAlternativeTrialPeerPurchase.allowance power span B) gp)).choose ≤ j)
    (height:j+2 ≤ (k₀+1))
    (clock:ℝ)(positiveClock:0 ≤ clock)
    (radiusStart:later (V:=V) R reg.simple span power (ord requested) clock 1 positiveClock zero_lt_one ≤ k₀)
    (housingStart:first (V:=V) R reg.simple span power (ord requested) (l+Fintype.card V*l) clock 1 100 positiveClock zero_lt_one ≤ j+1)
    (olderSpan:(((k₀+1)-(j+1):ℕ):ℝ) ≤ clock*(1+Real.log (H (k₀+1))))
    (top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (safe:WilsonCenteredCaptureClock.first R reg.simple ≤ i+1)
    (haloStart:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R reg.simple
      (ord requested+WilsonAddressedFiniteGuardCapital.power R grades power univ) zero_lt_one)).choose ≤ i+1)
    (meter:(eventually_atTop.mp (WilsonMeasuredPublicEntranceElectedMeter.original R grades reg.simple B requested)).choose ≤ k₀+1)
    (arms:∀a,Arm R (grades a) N per (k₀+1) (i+1))(dose:V → ℂ)
    (pins:o=WilsonReflectedPublicTrialRoster.root R grades arms (fi.trans (Nat.le_succ i)))
    (col:v=WilsonReflectedPublicTrialRoster.weight R grades arms)
    (factor:z=WilsonReflectedPublicTrialRoster.factor R (i+1) grades dose)
    (rows:V → Three G ((C₀).side (k₀+1) per))
    (x₀ e₀:∀a,Coefficient ((C₀).labels.level (grades a)) ((C₀).side (k₀+1) per))
    (w₀:V → ℝ)(path:∀a,X → Site ((C₀).side a per))(anchor:X):
    let fk:=fi.trans (Nat.le_succ i)
    let loc:=fun a=>(arms a).o
    let P₀:=(C₀).path.rep N per (k₀+1)
    let b:=j+1
    (∀a,let Ω:=orbitCost ((C₀).labels.level (grades a))
      let w:=WilsonReflectedPublicMountedInvoice.wage R (k₀+1)
      WilsonReflectedPublicGuardedColumns.Joined R (arms a) fk upper (dose a) (rows a) w (Ω*(1+w))
        ((2+Ω)*((H (k₀+1))^(WilsonMeasuredPublicEntranceFixedBill.depth grades (ord requested)+grades a))⁻¹) (x₀ a) (e₀ a)) → 
    (∃raw:V → Config G ((C₀).side (k₀+1) per) → ℂ,∃ω,∃F:Config G ((C₀).side (k₀+1) per) → Poly (S₀),
      Served P₀ raw ω F loc w₀ P₀.p.supportExponent 1) → 
    ((G₀).params (k₀+1)).supportExponent=100 → (∀a,0<w₀ a) → 
    (∀a,(C₀).ref (grades a) ≤ (k₀+1)) → (∀a,(w₀ a)⁻¹ ≤ (H (k₀+1))^gross) → 
    5 ≤ P₀.p.B → (∀a b:V,a≠b → P₀.p.B^2+1 ≤ separation (loc a) (loc b)) → 
    (C₀).S.a j/(C₀).S.a (k₀+1) ≤ (H (k₀+1))^apron → l ≤ box → path (k₀+1)=(loc∘Prod.fst)∘Prod.snd → 
    (∀a,j+1 ≤ a → a<(k₀+1) → path a=((G₀).clock.op a per).ratio.parent ∘ path (a+1)) → 
    (∀v,coverNumber ((C₀).path.rep N per b).p.B ({path b anchor,path b v}:Support _) ≤ l) → 
    ((G₀).clock.op j per).ratio.parent (path b anchor)=0 → 
    (((k₀+1)-b:ℕ):ℝ) ≤ gap*(1+Real.log (H (k₀+1)))^4 → (Ψ b).p.supportExponent ≤ 100 → 
    ∀(liveF:(k₀+1)<N)(V₀:∀a,Sight (C₀) (grades a) per)(r₀:∀a,Emblems (C₀) (grades a))
      (home:∀a,Opened (C₀) (grades a) (k₀+1) per)
      (_enrolled:∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) (k₀+1) N per (grades a)
        (digits R N per 0) (V₀ a) (r₀ a))
      (names:∀a,(C₀).label (grades a))(turn:V → Motion)(θ:V → ℂ),
    let raw:=fun a=>offer R (names a) (home a) liveF.le
    let arm:=fun a=>marked R (N:=N) 0 (turn a) (loc a) (V₀ a) (r₀ a) (reduce (raw a)) (k₀+1)
    WilsonThermometerReflectedRoster.filed R grades (fun _=>0) turn loc (fun a=>reduce (raw a)) V₀ r₀ S₀ liveF.le t → 
    (∀a,‖θ a‖ ≤ 1) → (∀a,θ a/(charge (raw a):ℂ)=dose a) → (∀a,(rows a).2.1=θ a•(arm a).2.1) → 
    ∀(u:ℕ),m ≤ u → (C₀).ref 0 ≤ u → ∀uj:u ≤ j,Opened (C₀) 0 u per → Opened (C₀) 0 j per → 
    WilsonSingleHardRadius.first R reg.simple ≤ u → ∀s:(S₀).Mode,
    let held:=uj.trans ((Nat.le_add_right j 2).trans height)
    let rawN:=fun W=>∏a∈s.val,dose a*(C₀).O N per (displayed R (grades a) (names a) (turn a))
      (WilsonThermometerReflectedTrajectory.anchorAt R (loc a) N) W
    let trial:=WilsonAddressedFiniteGuardTrial.printed R grades (N:=N) o v z fired_ s
    let road:=held.trans fk
    let enter:=fun W=>actualTransport (C₀) (N:=N) rawN upper W-trial W
    let read:=actualTransport (C₀) (N:=N) enter road 1
    read=actualTransport (C₀) (N:=N) rawN (held.trans liveF.le) 1-
      actualTransport (C₀) (N:=N) trial road 1 ∧ ‖read‖ ≤ ((H (k₀+1))^requested)⁻¹:=by
  intro fk loc P₀ b owned filed sup wp refs originalW big apart ap rooms start line pair centered window oldp
    liveF V₀ r₀ home enrolled names turn θ raw arm upperRoster small charged same
  have bought:=WilsonOriginalAlternativeTrialFunded.original R hk D Q π Γ Ψ books ahead grades order shelf seats i floor
    physical P upper ref o v z reg pace forecast route pass month fits packed q deep aged ep eu gate
    way ticket positive support span power B income
  obtain ⟨U,c,_,_,origin,_,_,_,reach⟩:=bought
  obtain ⟨wages,growth,short,L,cl,trace,_,_⟩:=reach (k₀+1) fi mf elected geom
  intro u mu ref₀ uj first last early s held rawN trial road enter read
  have priced:=WilsonMeasuredPublicEntranceEntered.original R hk D Q π Γ Ψ books ahead grades order shelf seats i
    floor upper ref o v z reg pace forecast U c k₀ fi mf L cl way ticket q ε trace span power B nonneg after
    geom income wages support origin stage nested cater bank shop n apron box requested gross t j l np size gap gp
    late height clock positiveClock growth short radiusStart housingStart olderSpan top safe haloStart meter arms dose
    pins col factor rows x₀ e₀ w₀ path anchor owned filed sup wp refs originalW big apart ap rooms start line pair
    centered window oldp liveF V₀ r₀ home enrolled names turn θ upperRoster small charged same u mu ref₀ uj first
    last early s
  exact ⟨priced.1,priced.2.2.2.2.2.2⟩

end YM.Integration.WilsonMeasuredPublicEntrancePurchased
end
