import YM.Integration.WilsonOriginalBlissQChronology
import YM.Integration.WilsonPositionOriginalDressedQShortAppointment

/-! Both signed Q withdrawals on the original school. The official field, its measure and its independent source roster are chosen on one physical trajectory before tests. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalBlissShortCourse
open Function Filter Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison
open ComparisonDensity.Address MergeProof MergeProof.Replicums Comparison.Density.RenderM FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open ConnectedActivityE6 Push.PriceCompiler FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators
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
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak Tree TraceExtension

variable {G:Gauge}(R:Run G)(hG:G.Simple){B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (J:Request V)(Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B)(μ:ℝ)(extra:V→ℕ)(w:V→ℝ)
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls){ψ:ℕ→ℕ}(scroll:VowsR.LawScroll G ψ)
  (books:Mentor.Offices.Books root R.rolls seat ψ)(forecast:Mentor.Forecast root R.rolls seat ψ books)
  {ZΘ:ℝ}{profile:PhysicalNext.ThroughLaunch.Orders}
  (house:Treehouse.VariableHouse R root seat scroll books ZΘ forecast profile)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))
local notation "ch" => house.licence.employed
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll («R»:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u


def Paid (K grade q tailOrder:ℕ)(ε:ℝ):Prop:=
    ∃ C:ℝ,1 ≤ C ∧ ∃ b:ℕ,∀ᶠ first:ℕ in atTop,∀ N,first ≤ N →
      ∃ (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),
        PlanV.Path root R.alloy seat (Burn.horizon (grade+v+h)) N first π Γ ∧ ∀ p,
      ∃ H:(s:ℕ)→Rep G (R.family.side s p),Concourse R.alloy R.kit R.T π Γ first N p (grade+v+h) H ∧
        Topline (H N) (R.family.path.levels.clock.forcedAllowance N) ∧
        (∀i,first ≤ i → i ≤ N → (H i).beta=(R.family.path.rep N p i).beta ∧ (H i).eval=(R.family.path.rep N p i).eval) ∧
      ∀ m (floor:first ≤ m) (before:m<N)
        (op:Mentor.Opportunity (J₀ (m+1)) (J₀ m))(epoch:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) op),
      op.count=h → op.stage=grade+1 → epoch.vac=grade+v+h →
      let Ω:=Mentor.Cruise.Semester.expense root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
      4 ≤ Ω ∧ Ω ≤ (β̂ (m+1))^(Beaming.grain (J₀ m)) ∧
      ∃ (hk:Burn.horizon epoch.vac+2 ≤ J₀ first)
        (lesson:Oak.Lesson (N:=N) R hk root seat π Γ floor),
      ∀ (o:V→Site (R.family.side (m+1) p))(orders:V→ℕ), (∀i,orders i ≤ K) →
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ (Burn.horizon (grade+v+h)) (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let weights:=fun j=>w j/(a*Ω)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      (∀ s:(Stock.census V).Mode,Poly.toll weights s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*h)+1)    ≤    ε*g^q) ∧
      ∃ voter:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1)))
        grade op.count op.stage epoch.vac (J₀ m),
      let size:=(R.alloy.B.a.S.oneStep m p).exact_size
      let panel:=Pane.panel R.alloy m size
      let published:=Mentor.Cruise.publish root R.rolls seat R.alloy ψ books op epoch size X grade voter lesson.entry
      let receipt:=Mentor.Cruise.funded root R.rolls seat R.alloy ψ books op epoch size X grade voter lesson.entry lesson.studied forecast
      let E:=Mentor.Cruise.Semester.figure root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
      let L:=Width.treasured X panel.ratio published receipt (H m).p E.afterwards (Coat.gStep (H (m+1)).beta)
      (∀j,0<weights j) ∧
      WilsonRootedKioskOccupiedSlip.Gross L weights (H m).p.B ((H m).p.supportExponent+1)
        ((Spill.allOver (H m).p)^E.cap*Ω) ∧
      ∀ (_y:tastes D) (k e:ℝ),0<e  →  e   ≤   1  → 
        WilsonPositionOriginalDressedQMeasuredCut.Read R Q D u η orders
          (testInclusion (ActualRunQlocalNativeTuple.orbit D)) hG before L (w:=weights) (k:=k)
          (hard:=Time.quoteHard R.alloy.B.a m R.kit.book (H (m+1)).beta)
          (H m).p.B (Pressure.radiusB (β̂ (m+1))) ((β̂ (m+1))^tailOrder)⁻¹
          (max (max 1 k) (Ω^5+(Spill.allOver (R.alloy.B.a.budget m))^E.cap*Ω/
            Willow.haloSlack (R.alloy.B.a.budget m).B))
          (8*Ω*(e+Burn.young (β̂ (m+1)) epoch.vac +
            (Pressure.betaF G (β̂ m) (R.rolls.L (J₀ (m+1))))^Mentor.Tuition.need grade (Mentor.Tolerance (J₀ m))))
 
include house income active in
theorem original (K grade q target tailOrder:ℕ)(ranked:rank ≤ grade)(positive:∀j,0<w j){ε:ℝ}(εpos:0<ε):
    Paid R hG J Q u μ extra w root seat books forecast K grade q tailOrder ε:=by
  obtain ⟨C,cp,b,reading⟩:=WilsonPositionOriginalDressedQShortAppointment.original R hG J Q u μ extra w root seat
    (ch).ready (ch).station house.stamps income books forecast (ch).education active house.calendar
    house.licence.forecast (ch).station.1 K grade q target tailOrder ranked positive εpos
  obtain ⟨first₀,reading⟩:=Filter.eventually_atTop.mp reading
  have nonempty:0 < h:=Fintype.card_pos
  have quiet:0 < grade+v+h:=by omega
  have elected:=WilsonOriginalBlissQChronology.original R root seat scroll books forecast house _ quiet
  refine ⟨C,cp,b,?_⟩
  filter_upwards [elected,Filter.eventually_ge_atTop first₀] with first available early
  intro N live
  obtain ⟨π,Γ,hk,_,route,periods⟩:=available N live
  refine ⟨π,Γ,route,?_⟩
  intro p
  obtain ⟨H,course,top,actual⟩:=periods p
  refine ⟨H,course,top,actual,?_⟩
  intro m floor before op epoch count stage cap Ω
  obtain ⟨big,roof,paid⟩:=reading m (early.trans floor) op epoch count stage cap
  have hkey:Burn.horizon epoch.vac+2 ≤ J₀ first:=by rwa [cap]
  have line:PlanV.Path root R.alloy seat (Burn.horizon epoch.vac) N first π Γ:=by rwa [cap]
  have law:Concourse R.alloy R.kit R.T π Γ first N p epoch.vac H:=by rwa [cap]
  let lesson:Oak.Lesson (N:=N) R hkey root seat π Γ floor:=(Oak.tale R hkey root seat π Γ floor before line).some
  refine ⟨big,roof,hkey,lesson,?_⟩
  intro o orders small
  exact paid N p o orders small before π Γ H first floor law lesson.entry lesson.studied lesson.ticket top
    (actual (m+1) (floor.trans (Nat.le_succ m)) before).1 (actual m floor before.le).2

end YM.Integration.WilsonOriginalBlissShortCourse
end
