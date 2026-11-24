import YM.Integration.WilsonReceivedCloseQGeometricIssue
import YM.Integration.WilsonWindowReportingPace

/-! Original curvature cohorts at three actual slots: the whole signed posterior price,
with its own measured forced term and the same filed table, before all placements and both regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseQGeometricProgram
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

/-- The same complete physical density and all of its proper faces are presented before the marked inputs are tested. -/
def Heard : Prop :=
  ∀ᶠ m:ℕ in atTop,∀ j (floor:m≤j),PaceR.Close R shape cap m j →
    ∀ N (cut:j+1<N),∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (hk:Burn.horizon (k₀)+2 ≤ R.alloy.B.a.clock.J m)
      (_lesson:Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))),
      PlanV.Path D R.alloy Q (Burn.horizon (k₀)) N m π Γ ∧
      ∀ per,∃ Ψ:∀l,RG.Rep G (R.family.side l per),Concourse R.alloy R.kit R.T π Γ m N per (k₀) Ψ ∧
        Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
        ∀ (upperSites:(Fin 3)→Site (R.family.side ((j+1)+1) per)) (sites:(Fin 3)→Site (R.family.side (j+1) per))
          (upperOrders orders:(Fin 3)→ℕ), (∀v,upperOrders v≤upperOrder) → (∀v,orders v≤K) →
          WilsonReceivedCloseQGeometricIssue.Receipt (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
            (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
            (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut)
            (op:=opAt j (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))))
            (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
            (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
            (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
            (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=o₀) (shelf:=roomSize)
            (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
            (old:=old) (fresh:=fresh) (span:=span) (height:=height) (angleCap:=angleCap)
            singer directions comparison desired sourcePower ε fraction wallet

include protection hp cp ep sep in
theorem original (whole:old∪fresh=univ) (load:gradeTotal old (fun _:Fin 3=>uGrade) (fun _:Fin 3=>lGrade) ≤ roomSize)
    (gradeCap:(∑v,(choice old (fun _:Fin 3=>uGrade) (fun _:Fin 3=>lGrade)) v) ≤ 14)
    {σ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple σ W)
    (slow:WilsonWindowReportingPace.Slow R.kit) (clear:MSbar.Heath.Clear G singer)
    (gate:WilsonReportingForestAngularReflection.posted R) (lamp:WilsonReportLampForecast.Ready R.family.path.levels) :
    Heard R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels
      μ upperClock extra upperExtra K upperOrder old fresh desired sourcePower span shape height angleCap cap ε
      singer directions wallet := by
  have initial := WilsonReceivedCloseQCoissuedProgram.original R simple D Q scroll books ahead house protection income hire
    request upperJ freshQ upperQ u upperLabels μ upperClock extra upperExtra K upperOrder old fresh sep comparison
    span shape height angleCap cap ε hp cp ep whole load
  have pos : (0:ℝ) < fraction := by positivity
  have three : (0:ℝ)≤(3:ℝ)^comparison := by positivity
  have half : fraction≤(1/2:ℝ) := (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by linarith)
  have accurate : fraction*((3:ℝ)^comparison+2)≤1 := by
    rw [one_div_mul_eq_div]
    exact (div_le_one (by positivity)).2 (by linarith)
  obtain ⟨deep₁,age₁,_⟩:=sales
  change 2*((p₁)+1)+8 ≤ o₀ at deep₁
  change (p₁)+4 ≤ 3*(k₀)+2 at age₁
  have booked:comparison≤p₁:=by unfold WilsonReceivedCloseQSchool.precision;omega
  have deep : 2*(comparison+1)+8 ≤ o₀ := by omega
  have aged : comparison+4 ≤ 3*(k₀)+2 := by omega
  have seatsPaid : axes ≤ Burn.horizon (k₀)+2 := by
    simp only [Fintype.card_fin]
    unfold WilsonReceivedCloseQSchool.vacuum Burn.horizon
    omega
  have clocks := WilsonReceivedGeometricPriorDates.scheduled R simple funded slow.2 singer clear D protection
    (choice old (fun _:Fin 3=>uGrade) (fun _:Fin 3=>lGrade)) o₀ roomSize k₀ gate comparison desired
    (sourcePower+((2*d₀+1)*3+1)) wallet pos lamp deep aged
  filter_upwards [initial,clocks] with m seen timed
  intro j floor corridor N cut
  obtain ⟨π,Γ,hk,lesson,route,read⟩ := seen j floor corridor N cut
  refine ⟨π,Γ,hk,lesson,route,?_⟩
  intro per
  obtain ⟨Ψ,course,topline,registered⟩ := read per
  refine ⟨Ψ,course,topline,?_⟩
  intro upperSites sites upperOrders orders hu hl
  have receipt := registered upperSites sites upperOrders orders hu hl
  apply WilsonReceivedCloseQGeometricIssue.original (course:=course) (q:=comparison) (tol:=ε)
    (purchase:=receipt) (gradeCap:=gradeCap) (funded:=funded) (slow:=slow.2) (clear:=clear) (strip:=protection)
    (law:=scroll) (enrolled:=ch) (fund:=house.licence.edges) (gate:=gate) (ready:=lamp)
    (surplus:=le_rfl) (load:=seatsPaid) (deep:=deep) (aged:=aged) (ep:=pos) (half:=half)
    (accurate:=accurate) (timed:=timed)

end YM.Integration.WilsonReceivedCloseQGeometricProgram
