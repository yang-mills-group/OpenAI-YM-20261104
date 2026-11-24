import YM.Integration.WilsonThermometerRegisteredAllStation
import YM.Integration.WilsonThermometerFullSignedOrder

/-! The funded signed ordinary density on the original twice-operated three-name thermometer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerFullSignedAppointment
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i+1)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+2) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
  (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+2) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+2))
local notation "M₀" => primitive R A (i+2) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+2)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self (i+1)) o

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
  {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)

open FVA1Physical.TwoReset

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)

local notation "originalPost" => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks
  (WilsonThermometerCourseHearing.sectors) levels school.order school.horizon school.pieces (i+1) hi
  (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self (i+1)) o)

open private wide from YM.Integration.WilsonThermometerRegisteredFirstJoin
open WilsonOriginalThermometerTollBudget
open RG QuadraticLocal.Affinity

open WilsonReceivedCloseHistory
open WilsonOriginalReceivedChain


open WilsonThermometerCommonDetector
local notation "S₁" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "lowerPost" f:max => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels
  school.order school.horizon school.pieces i f (S₁)
local notation "young" f:max L:max => Oak.student (n:=per) R hk D Q π Γ books f (L).op (L).lesson ahead disks
  (L).model school.order (L).voter
local notation "issued" x:max f:max L:max => Air.craft (young f L) (fun v=>((young f L) v).paint x)
  levels (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))

open Push.Local Primitives.GCC.Anchor WilsonFiniteOrdinaryInverse WilsonThermometerCenteredAlgebra
open WilsonThermometerCourseHearing WilsonThermometerWeightedCapture
open WilsonThermometerRegisteredAllStation Source Labels Extra.Histories
local notation "cut" => (Nat.lt_succ_of_lt (Nat.lt_succ_self i))
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "F₀" => R.family.labels.level 0
local notation "M₁" => R.family.params
local notation "S₄" => R.family.localSection 0
local notation "native₀" => WilsonThermometerCourseIntake.incoming R A simple (cut).le o
local notation "weight" L:max f:max => Oak.expenseReal R hk D Q π Γ books f (L).op (L).lesson ahead school.order school.horizon
local notation "homes" L:max => ((L).passport.coarser (R.family.path.levels.clock.op i per).ratio).origin
local notation "pay₀" f:max L:max => rendered (young f L) (Ψ i).p (Coat.gStep (Ψ (i+1)).beta)
local notation "raw₀" f:max L:max => fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare (pay₀ f L) fired U)
local notation "stage₀" α:max => WilsonFullFaceSignedPower.constants (S₄) (M₁) α ((2:ℝ)^(school.order+school.horizon+2)+4)
local notation "half" => ((1:ℝ)/4)

def Billed (floor:m ≤ i) (L:lowerPost floor) (q target:ℕ) : Prop :=
  ∀(table:Poly J₀) (y:Site (R.family.side i per)) (Z:Support (R.family.side i per)),y∈Z →
    (∀v:Fin 3,(homes L) v∈Z) → ∀ rad:ℕ,(∀v:Fin 3,separation ((homes L) v) y≤rad) →
    rad≤(Ψ i).p.B → Z⊆halo (Ψ i).p.B {y} → ∀α:ℝ,(Ψ i).p.supportExponent≤α →
    Poly.price (fun v=>gf*L.w v) (inverseMass table)≤fee J₀ →
    ∃h:Coefficient (F₀) (R.family.side i per), h.Format y (M₁) (Ψ i) ∧
      h.remBound y (Ψ i) κ (|fee J₀*stage₀ α| * (4^q+2)*gf^target) ∧
      (∀U,h.density y (S₄) (Ψ i) U=(total (native₀ U) table).part full-
        ((Ψ i).eval U:ℂ)*(total ((raw₀ floor L) U) table).part full) ∧
      (F₀).coeffSize h.x ≤ |testPrice (F₀)*fee J₀*WilsonFullFaceSignedPower.inter*
        (Fintype.card (Multi.parts (J₀)).Mode:ℝ)*125| * gf^target

def gate (q:ℕ) (deep:2*(q+1)+8 ≤ school.order) (aged:q+4≤3*k+2) : ℕ :=
  (range (school.pieces+1)).sup fun c=>WilsonFirstReceivedEarnedFee.opening R simple c q school.order k deep aged
    (show (0:ℝ)<half by norm_num)

include history hospital in
theorem on_post (floor:m ≤ i) (L:lowerPost floor) (way:WayStation R.kit)
    (station:WilsonCenteredCaptureClock.first R simple ≤ i) (sec:R.t 0 ≤ i)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow.2 ready)).choose ≤ i)
    (late:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass:Pass D Q R.alloy R.kit) (q target:ℕ) (surplus:target+247≤q)
    (force:q≤R.alloy.B.a.clock.J i) (deep:2*(q+1)+8 ≤ school.order) (aged:q+4≤3*k+2)
    (opened:gate R simple school q deep aged ≤ i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i)
    {η:ℝ} (modest:η≤half) (visible:Visible R simple A hk D Q π Γ Ψ books school o ahead floor L q η) :
    Billed R simple A hk D Q π Γ Ψ books school o ahead floor L q target :=by
  obtain ⟨rented,aperture,load,narrow,_⟩:=visible
  have ww:=history.1.walk (i+1) (Nat.le_succ_of_le floor) cut
  have same:=congrArg Coat.gStep ww.beta
  have gp:0<gf:=same ▸ L.issued.Waffle.soon.1
  have small:gf≤1:=same ▸ L.issued.Waffle.soon.2.1
  have raised:((weight L floor)^L.op.count)≤(weight L floor)^school.pieces:=
    pow_le_pow_right₀ L.issued.Waffle.cool L.capacity.le
  have e:(8*(weight L floor)^L.op.count)*L.rent+half*gf^q≤gf^q:=by
    have free:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left raised (by norm_num:0≤(8:ℝ))) L.active.le).trans rented
    have first:=(free.trans (mul_le_mul_of_nonneg_right modest (pow_nonneg gp.le q)))
    linarith only [first,pow_nonneg gp.le q]
  have bounded:=e.trans (pow_le_one₀ gp.le small)
  have activated:WilsonFirstReceivedEarnedFee.opening R simple L.op.count q school.order k deep aged
      (show (0:ℝ)<half by norm_num) ≤ i:= by
    exact (Finset.le_sup (f:=fun c=>WilsonFirstReceivedEarnedFee.opening R simple c q school.order k deep aged
      (show (0:ℝ)<half by norm_num)) (Finset.mem_range.mpr (Nat.lt_succ_of_le L.capacity.le))).trans opened
  intro table y Z center inside rad near radius box α strength fee₁
  exact WilsonThermometerFullSignedOrder.original R A simple cut o hk D Q π Γ Ψ history books floor ahead
    school.order school.horizon school.pieces L way station sec slow.2 ready early late pass hospital narrow load
    q q force deep aged (show (0:ℝ)<half by norm_num) activated bounded table y Z center inside rad near
    radius box α strength 157 (aperture full) fee₁ target (by omega) e saved

include history scroll chamber hospital warm top cal in
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (stage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ j,R.family.ref (levels j) ≤ (i+2))
    (floor : m ≤ i) (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (q : ℕ) (deep : 2*(q+1)+8 ≤ school.order) (aged : (q+1)+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (funded : WilsonReceivedMeasuredStampPrice.opening R simple (q+1) school.order k deep aged zero_lt_one ≤ i+1)
    (hard : WilsonWindowOriginalHardRadius.Booked R.kit) (way : WayStation R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay) (p : ℕ)
    (lower : WilsonThermometerAppointedPhysical.activation R D simple income p ≤ i)
    (ordered : p+156 ≤ school.order+1) (ready : p+6*school.pieces ≤ Burn.horizon k+2)
    (extent : reach R ≤ R.alloy.B.a.clock.J (i+2)+1)
    (topReady : topAge R simple ≤ i)
    (detector : WilsonThermometerAppointedDetector.activation R simple q school.pieces ep ≤ i)
    (measured : (Ψ (i+1)).beta = (R.family.path.rep (i+2) per (i+1)).beta)
    (fits:school.order ≤ Burn.horizon k+1) (shelf:school.horizon ≤ R.alloy.B.a.clock.J m) (modest:ε≤half)
    (target:ℕ) (surplus:target+247≤q) (force:q≤R.alloy.B.a.clock.J i)
    (station:WilsonCenteredCaptureClock.first R simple ≤ i) (sec:R.t 0 ≤ i)
    (active:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow.2 active)).choose ≤ i)
    (halo:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (opened:gate R simple school q deep (by omega) ≤ i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i) :
    ∃ L:lowerPost floor, Visible R simple A hk D Q π Γ Ψ books school o ahead floor L q ε ∧
      Billed R simple A hk D Q π Γ Ψ books school o ahead floor L q target :=by
  obtain ⟨L,stamp⟩:=WilsonThermometerRegisteredAllStation.original R simple A hk D Q π Γ Ψ history scroll books chamber hi warm top
    school o op lesson cal ahead hospital fund slow late date checked near shape size space room stage ranks width refs floor
    pass path month q deep aged ep funded hard way training income p lower ordered ready extent topReady detector measured fits shelf
  exact ⟨L,stamp,on_post R simple A hk D Q π Γ Ψ history books school o ahead hospital slow floor L way station sec active early
    halo pass q target surplus force deep (by omega) opened saved modest stamp⟩


end YM.Integration.WilsonThermometerFullSignedAppointment
