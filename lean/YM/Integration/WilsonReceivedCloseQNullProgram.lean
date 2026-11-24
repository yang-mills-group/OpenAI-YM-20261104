import YM.Integration.WilsonReceivedCloseQOrbitProgram
import YM.Integration.WilsonReceivedCloseQNullDates
import YM.Integration.WilsonReceivedCompactQUnitSplit
import YM.Integration.WilsonReceivedCloseQCaptureProgram
import YM.Integration.WilsonReceivedCompactQOrbitReturn

/-! One funded physical Q capture, on the whole orbit of reporter-site translations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseQNullProgram
open XSpace
open WilsonLimitConstruction OPE.Therm Further.PhysicalPeriodLimitF933
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open Pert.Asymptotics Extra.Histories WilsonOriginalReceivedChain
open scoped Classical BigOperators
open VowsR QuadraticLocal.Affinity Sycamore
variable {G:Gauge} (R:Run G) (simple:G.Simple)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  {φ:ℕ→ℕ} (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books) {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
  (house:Treehouse.VariableHouse R D Q scroll books ZΘ ahead profile)
  (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (hire:∀d,MintClock.Employment D φ d (R.rolls.L d))
  {B:MS.Local.Physical.Deck G} 
  (request upperJ:Request (Fin 3)) (freshQ upperQ:MS.Land.Prescription B)
  (u upperLabels:(Fin 3)→MS.Rake.Label B) (μ upperClock:ℝ) (extra upperExtra:(Fin 3)→ℕ)
  (K upperOrder:ℕ) (old fresh:Finset (Fin 3)) (sep:Disjoint old fresh)
local notation "axes" => Fintype.card (Fin 3)
local notation "uGrade" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels
local notation "lGrade" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "roomSize" => axes*uGrade
local notation "rank" => max (ActualOriginalQLayout.rankCap R upperLabels) (ActualOriginalQLayout.rankCap R u)
local notation "ch" => house.licence.employed
local notation "d₀" => WilsonReceivedCloseQNamedSalary.degree R simple request freshQ u μ extra D income K Q
  books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
  (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder
local notation "currency" => WilsonReceivedCloseQNamedSalary.currency R simple request freshQ u μ extra D income K Q
  books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
  (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder
variable (desired sourcePower span shape:ℕ) (height angleCap cap ε:ℝ) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "comparison" => desired+1+(sourcePower+((2*d₀+1)*3+1)+87)
local notation "fraction" => (1 / ((3:ℝ)^comparison+3))
local notation "target" => comparison+1+((2*d₀+1)*axes+1)+axes
local notation "prec₀" => WilsonReceivedCloseQSchool.precision (d₀) axes (target)
local notation "p₁" => WilsonReceivedCloseQSchool.precision (d₀) axes ((target)+1)
local notation "o₀" => WilsonReceivedCloseQSchool.degree (d₀) axes (rank) ((target)+1)
local notation "k₀" => WilsonReceivedCloseQSchool.vacuum (d₀) axes (rank) (roomSize) ((target)+1)
local notation "Sch" => WilsonReceivedCloseQSchool.school (d₀) axes (rank) (roomSize) ((target)+1)
local notation "opAt" j:max h:max => (Sch).room (Push.PriceCompiler.step_paid R.alloy.B.a (j+1)) h
local notation "sales" => WilsonReceivedCloseQSchool.resources (d₀) axes (rank) (roomSize) ((target)+1)

variable (singer:MSbar.Heath.Voice G) (directions:Lattice.Order) (wallet:ℝ)

open WilsonReceivedCloseCompactStations WilsonReceivedGeometricCellReadout WilsonReceivedCloseCompactDualStations
local notation "packing" j:max per:max => WilsonReceivedCompactQSampling.Placements R j per
local notation "loss" N₀:max per₀:max date₀:max => fares (N:=N₀) (per:=per₀) (i:=date₀) R o₀ roomSize comparison desired sourcePower (2*d₀+1) fraction wallet
/-- A real lower reference post supplies the original homogeneous null-source return at every site.
The scalar decomposition is measured on that same earlier vacuum. -/
def Gates (N per m j:ℕ) (Ψ:∀ l,RG.Rep G (R.family.side l per)) (ε:ℝ) : Prop :=
  ∀ i, m ≤ i → i ≤ j →
    (∀y,WilsonOriginalNullFiledStep.Filed R.family 0 N per i Ψ y ε) ∧
    ∀ (fees:Fares) (y:Site (R.family.side i per)) (v:Values (Config G (R.family.side i per)))
      (h:Source.Coefficient (R.family.labels.level 0) (R.family.side i per)),
      Paid (N:=N) R (Ψ i) fees y v h → WilsonReceivedCompactQUnitSplit.Split R (Ψ i) y h (max fees.regular fees.primary)

/-- The true original source, its computed coefficients, the two registration meshes, and every supported
signed profile share their selection before the physical period and the submitted positions. -/
def AtDate (m:ℕ) : Prop :=
  ∀ j (floor:m≤j),PaceR.Close R shape cap m j →
    ∀ N (cut:j+1<N),∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (hk:Burn.horizon (k₀)+2 ≤ R.alloy.B.a.clock.J m)
      (_lesson:Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))),
      PlanV.Path D R.alloy Q (Burn.horizon (k₀)) N m π Γ ∧
      ∀ per,∃ Ψ:∀l,RG.Rep G (R.family.side l per),Concourse R.alloy R.kit R.T π Γ m N per (k₀) Ψ ∧
        Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
        WilsonReceivedCloseGeometricPlacedBooking.Entitled (N:=N) R hk D Q π Γ Ψ books ahead o₀ roomSize floor ∧
        Gates R N per m j Ψ ε ∧
        (∀ (upperOrders orders:packing j per→(Fin 3)→ℕ), (∀o v,upperOrders o v ≤ upperOrder) → (∀o v,orders o v ≤ K) →
          ∀ i (ib:i ≤ j) (mi:m ≤ i), ∃T:packing j per→Board (N:=N) R (Ψ i) (loss N per i) sourcePower wallet,
            (∀o,
          WilsonReceivedCloseQLocatedFile.Registered (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
            (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
            (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut)
            (op:=opAt j (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))))
            (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
            (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
            (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
            (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=o₀) (shelf:=roomSize)
            (upperSites:=o.1) (upperOrders:=upperOrders o) (sites:=o.2) (orders:=orders o)
            (old:=old) (fresh:=fresh) (span:=span) (height:=height) (angleCap:=angleCap)
            ib mi singer directions comparison desired sourcePower ε fraction wallet (T o)) ∧
          WilsonReceivedCompactQRadiused.Captured (b:=j) R (Ψ i) (loss N per i) sourcePower wallet simple T) ∧
        ∀ (upperOrders orders:packing j per→(Fin 3)→ℕ), (∀o v,upperOrders o v ≤ upperOrder) → (∀o v,orders o v ≤ K) →
          ∀ i (ib:i+1 ≤ j) (mi:m ≤ i), ∃T:packing j per→Dual (N:=N) R Ψ i (loss N per (i+1)) sourcePower wallet,
            (∀o,
          WilsonReceivedCloseQLocatedDualFile.Registered (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
            (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
            (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut)
            (op:=opAt j (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))))
            (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
            (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
            (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
            (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=o₀) (shelf:=roomSize)
            (upperSites:=o.1) (upperOrders:=upperOrders o) (sites:=o.2) (orders:=orders o)
            (old:=old) (fresh:=fresh) (span:=span) (height:=height) (angleCap:=angleCap)
            ib mi singer directions comparison desired sourcePower ε fraction wallet (T o)) ∧
          WilsonReceivedCompactQRadiusedHard.Captured (b:=j) R Ψ (loss N per (i+1)) sourcePower wallet simple T ∧
          WilsonReceivedCompactQOrbitReturn.Captured (b:=j) R Ψ (loss N per (i+1)) sourcePower wallet ib simple T

def Heard : Prop := ∀ᶠ m:ℕ in atTop,AtDate R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels
      μ upperClock extra upperExtra K upperOrder old fresh desired sourcePower span shape height angleCap cap ε
      singer directions wallet m

/-- Every sufficiently small real radius has its physical capture and an earlier step on the same course. -/
def AtRadius : Prop :=
  ∀test:Test 3,∃t:ℝ,0<t ∧ ∀r:ℝ,0<r → r≤t →
  let b:=WilsonCloseCaptureDate.level R.family.S r
  ∃m:ℕ,m+1=b ∧ WilsonReceivedCompactQRadiused.floor R simple test ≤ b ∧ |r| ≤ R.family.S.a b ∧ AtDate R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels
      μ upperClock extra upperExtra K upperOrder old fresh desired sourcePower span shape height angleCap cap ε
      singer directions wallet m

theorem original (booked:WilsonReceivedCloseQOrbitProgram.Heard R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels
      μ upperClock extra upperExtra K upperOrder old fresh desired sourcePower span shape height angleCap cap ε
      singer directions wallet)
    {σ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple σ W)
    (slow:WilsonWindowReportingPace.Slow R.kit) (lamp:WilsonReportLampForecast.Ready R.family.path.levels)
    (ep:0<ε) :
    Heard R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels
      μ upperClock extra upperExtra K upperOrder old fresh desired sourcePower span shape height angleCap cap ε
      singer directions wallet := by
  obtain ⟨deep₁,age₁,_⟩:=sales
  change 2*((p₁)+1)+8 ≤ o₀ at deep₁
  change (p₁)+4 ≤ 3*(k₀)+2 at age₁
  have horizon:comparison ≤ p₁:=by unfold WilsonReceivedCloseQSchool.precision;omega
  have deep : 2*(5+4+1)+8 ≤ o₀ := by omega
  have aged : 5+4+4 ≤ 3*(k₀)+2 := by omega
  have seat : axes ≤ Burn.horizon (k₀)+2 := by
    simp only [Fintype.card_fin]
    unfold WilsonReceivedCloseQSchool.vacuum Burn.horizon
    omega
  have timed:=WilsonReceivedCloseQNullDates.original R o₀ roomSize simple slow lamp deep aged funded ε ep
  filter_upwards [booked,timed] with m rates dates
  intro j floor close N cut
  obtain ⟨π,Γ,hk,lesson,path,perRooms⟩:=rates j floor close N cut
  refine ⟨π,Γ,hk,lesson,path,?_⟩
  intro per
  obtain ⟨Ψ,course,topline,booking,ordinary,dual⟩:=perRooms per
  refine ⟨Ψ,course,topline,booking,?_,ordinary,dual⟩
  intro i mi ib
  obtain ⟨M,paid⟩:=dates
  obtain ⟨eligible,calendar⟩:=paid i mi
  have live : i<N := by omega
  have walk:=course.1.walk i mi live.le
  let zero:packing j per→Fin 3→ℕ := fun _ _=>0
  obtain ⟨port,registered,_⟩:=ordinary zero zero (fun _ _=>Nat.zero_le _) (fun _ _=>Nat.zero_le _) i ib mi
  let origin:packing j per:=(fun _=>0,fun _=>0)
  obtain ⟨_,_,_,_,L,_⟩:=(registered origin).1
  constructor
  · intro y
    exact WilsonOriginalNullFiledStep.original R hk D Q π Γ Ψ books ahead _ _ _ o₀ roomSize _ mi _ L y 0
      (0:Fin 3) live simple course scroll (ch) (ch).station.1 house.licence.forecast seat (ch).ready M
      slow.2 lamp (funded.2.1.paid.fixed i).le 5 deep aged (by decide) eligible (ch).station ε ep calendar
  · intro fees y v h spent
    have support : (Ψ i).p.supportExponent ≤ 100 :=
      ((congrArg BudgetPoint.supportExponent walk.truep.point).trans (funded.2.1.paid.fixed i)).le
    exact WilsonReceivedCompactQUnitSplit.original R simple (Ψ i) walk.truep.point support calendar.landing
      fees y v h spent

theorem radii (paid:Heard R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels
      μ upperClock extra upperExtra K upperOrder old fresh desired sourcePower span shape height angleCap cap ε
      singer directions wallet) :
    AtRadius R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels
      μ upperClock extra upperExtra K upperOrder old fresh desired sourcePower span shape height angleCap cap ε
      singer directions wallet := by
  intro test
  exact WilsonReceivedCompactLowerCalendar.original R simple test paid

end YM.Integration.WilsonReceivedCloseQNullProgram

