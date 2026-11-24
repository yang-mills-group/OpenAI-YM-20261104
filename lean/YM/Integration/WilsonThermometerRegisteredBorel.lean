import YM.Integration.WilsonThermometerRegisteredCompact
import YM.Integration.WilsonThermometerRegisteredWindow

/-! Comparison with the declared numerical material at the joint axial chart of the measured field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredBorel
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
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
  (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+2) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+2))
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+2)
local notation "J₀" => Stock.census (Fin 3)
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
  {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)

open FVA1Physical.TwoReset

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)


open WilsonOriginalReceivedChain Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open WilsonThermometerCourseIntake

variable
  (strip : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
  (q depth : ℕ) (deep:2*(q+1)+8 ≤ school.order) (aged:q+4 ≤ 3*k+2)
  (H cap:ℝ) (cap_pos:0 ≤ cap)

open WilsonThermometerRegisteredPair OriginalForcedAddresses Extra.Trajectories
open WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading

local notation "earlier" => (show i < i+2 from by omega)
local notation "first" => (Nat.lt_succ_self (i+1))
local notation "g₁" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "g₂" => Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
local notation "stage" => ((Advent.budgetR R i)^2*(Advent.budgetR R (i+1))^7)


open WilsonOriginalThermometerTollBudget
local notation "K₀" => WilsonThermometerRegisteredOrdinary.gross R simple (f:=f) (F:=F) fund slow
local notation "e₀" => WilsonThermometerRegisteredOrdinary.power R simple (f:=f) (F:=F) fund slow
local notation "crop" => (E₁)*(Ω₀)


open WilsonThermometerRegisteredRate WilsonThermometerRegisteredCells WilsonThermometerAlignedCells
open MeasureTheory OPE OPE.Orbits XSpace.Rose Push.GridApprox

local notation "T₀" => Site (R.family.side (i+2) per)
local notation "N₀" => ((i+2,per):RG12.UVIndex)


open Ac OPE.Therm Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open RG16 MSbar.Heath
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare WilsonJointAxialRoster
open Multi Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade

local notation "degreeCap" => (school.order+school.horizon+2)

include history chamber warm top cal hospital in
/-- The comparison takes place on the original window with unrestricted exterior.
The real received numerator at its global axial extension connects the nominal to
the independent path material with the actual two dated inverse transfers. -/
theorem on_post (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (opStage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ v,R.family.ref (levels v) ≤ i+2)
    (floor:m ≤ i) (fit:k ≤ R.alloy.B.a.clock.J i)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:school.order ≤ Burn.horizon k+1) (shelved:school.horizon ≤ R.alloy.B.a.clock.J m)
    (load:school.pieces ≤ Burn.horizon k+2) (packed:school.order+school.horizon ≤ Burn.horizon k+2)
    (tender:WilsonReceivedMeasuredStampPrice.opening R simple q school.order k
      (show 2*q+8 ≤ school.order from by omega) (show q+3 ≤ 3*k+2 from by omega) zero_lt_one ≤ m+1)
    (held:0 < i) (fieldDate:WilsonThermometerRegisteredOrdinary.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (heard:WilsonThermometerRegisteredPair.opening R simple D school strip q 0 deep aged 1 1 zero_le_one
      (ε:=1) zero_lt_one ≤ i)
    (orderWanted:ℕ) (surplus:q=WilsonThermometerRegisteredRate.order orderWanted (e₀)+1)
    (heat:warmDate R simple ≤ m) (funded:priceDate R simple school orderWanted (e₀) ≤ i)
    (rootFee:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (stencil:reach R ≤ R.alloy.B.a.clock.J (i+2)+1)
    (volume:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (J:Voice G) (clear:Clear G J) (axes:Lattice.Order) (qW:ℕ)
    (dw:2*(qW+1)+8 ≤ school.order) (aw:qW+4 ≤ 3*k+2) {ε:ℝ} (ep:0<ε)
    (window:max (WilsonJointAxialRoster.opening R simple fund slow.2 J clear (Fintype.card (Fin 3)) degreeCap qW ep)
      (WilsonReceivedAxialFiling.opening R simple D φ strip school.order school.horizon (Fintype.card (Fin 3)) ep) ≤ i)
    (shapeWindow:max (WilsonReceivedAxialFinite.opening R simple qW ep)
      (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple strip) ≤ i)
    (paidWindow:WilsonThermometerRegisteredWindow.opening R simple D school.order school.horizon school.pieces
      strip qW dw aw ep ≤ i)
    (y:T₀×T₀)
    (P:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead
      WilsonThermometerCourseHearing.disks S₀ levels school.order school.horizon school.pieces i floor
      (WilsonThermometerCourseHearing.offered R A simple (earlier) (placement (R:=R) (N₀) y)))
    (loadW:P.op.count ≤ Burn.horizon k+2) :
    let V:=P.passport.coarser (R.family.path.levels.clock.op i per).ratio
    let H:=radius R (invoice (Fintype.card (Fin 3)) (qW+2*degreeCap)) 1 i
    let r:=amplitude R J H (i+2) per i
    let h:=(WilsonDegreeFourInheritedRange.height R (qW+2*degreeCap) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let tau:=angularCut (R.family.path.levels.clock.hatBeta i)
    ∀ U:Config G (R.family.side i per), U ∈ House.chilly (plaquettes V.origin H) tau →
      let ξ:=WilsonJointAxialWindow.direction V.origin h J axes r U
      let link:=WilsonCapturedPrimaryPotential.potential g₁ (r • ξ)
      ∀ t a b:Fin 3, a≠b → a≠t → b≠t → ∀ u:ℕ,2+u ≤ school.order+1 →
        let x:=without t
        let s:(J₀).Mode:=⟨{a,b},mem_univ _⟩
        let student:=Oak.student (n:=per) R hk D Q π Γ books floor P.op P.lesson ahead
          WilsonThermometerCourseHearing.disks P.model school.order P.voter
        let nominal:=(Poly.pass (bare (rendered student (Ψ i).p (Coat.gStep (Ψ (i+1)).beta)) x U)).part s
        let field:=WilsonThermometerRegisteredCompact.prescribed R A π Γ school t a b link y
        let E:=ε*(Pert.Asymptotics.regulatorRun R.family (i+2) per i)^qW+ε*g₁^school.order+ε*g₁^qW
        let E':=(8*(budgetR R i)^school.pieces)*P.rent+ε*g₁^qW
        Poly.toll P.w s * ‖nominal-field‖ ≤
          WilsonThermometerRegisteredWindow.bill s g₁ E u+WilsonThermometerRegisteredWindow.bill s g₁ E' u
              + Poly.toll P.w s*(price (rate R) (K₀) orderWanted (e₀)*g₁^orderWanted) := by
  intro V H r h tau U cold ξ link t a b ab at' bt' u enough x s student nominal field E E'
  let o:=placement (R:=R) (N₀) y
  have cutFloor:=R.alloy.B.a.fits.mono floor
  have narrow:=shelved.trans cutFloor
  obtain ⟨⟨z,range,axis⟩,healthy,changeField⟩:=WilsonThermometerRegisteredWindow.original
    R simple A hk D Q π Γ Ψ history books floor ahead school.order school.horizon school.pieces o P
    strip qW dw aw fund slow.2 J clear axes ep scroll chamber volume window shapeWindow paidWindow pass
    hospital narrow loadW fit refs held U cold
  let mid:=actualTransport R.family (N:=i+2)
    (WilsonThermometerRegisteredCells.raw A (N₀) a b (atOrigin y)) (Nat.le_add_right i 2)
    (Integral.sample g₁ (Stationary.arm G (R.family.side i per) 1 link))
  have originalBelow:Poly.toll P.w s * ‖nominal-mid‖ ≤ WilsonThermometerRegisteredWindow.bill s g₁ E u+
    WilsonThermometerRegisteredWindow.bill s g₁ E' u:=changeField t a b ab at' bt' u enough
  have second:‖mid-field‖ ≤ price (rate R) (K₀) orderWanted (e₀)*g₁^orderWanted:=by
    dsimp only [field,WilsonThermometerRegisteredCompact.prescribed]
    simp only [← WilsonThermometerNumericalStation.returned R A D π Γ (φ:=φ) school
      (placement (R:=R) (N₀) y) (without t)]
    exact WilsonThermometerRegisteredRate.original R simple A hk D Q π Γ Ψ history scroll books chamber hi
      warm top school o op lesson cal ahead hospital fund slow strip
      q 0 deep aged 1 1 zero_le_one late date checked near shape size space room opStage ranks width refs
      floor fit path pass month fits shelved load packed tender held fieldDate heard orderWanted surplus
      heat funded rootFee stencil t a b ab at' bt' link z range axis healthy
  have paid:0 ≤ Poly.toll P.w s:=Finset.prod_nonneg fun v _ => (P.salary.positive v).le
  calc
    _ ≤ Poly.toll P.w s*(‖nominal-mid‖+‖mid-field‖) := mul_le_mul_of_nonneg_left
      (norm_sub_le_norm_sub_add_norm_sub ..) paid
    _ = _ := mul_add .. 
    _ ≤ _ := add_le_add originalBelow (mul_le_mul_of_nonneg_left second paid)

end YM.Integration.WilsonThermometerRegisteredBorel
