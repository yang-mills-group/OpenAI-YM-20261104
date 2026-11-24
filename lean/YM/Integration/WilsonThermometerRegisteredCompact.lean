import YM.Integration.WilsonThermometerRegisteredRate
import YM.Integration.WilsonThermometerRegisteredCells
import YM.Integration.WilsonThermometerNumericalStation

/-! Both displacements of the compact physical test on the received nonbare pair detector. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCompact
universe u

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

def prescribed (t a b:Fin 3) (link:Stationary.Link G (R.family.side i per)) (y:T₀×T₀) : ℂ :=
  let o:=placement (R:=R) (N₀) y
  let bare:=WilsonThermometerNumericalStation.numerical R A π school o (without t)
  let formal:=WilsonOriginalCoveredEvolution.run R first π Γ (Burn.horizon k+2) school.order levels bare
  let target:=WilsonCoherentMayerWindingGrades.panel school.order (g₁:ℂ)
    (fun e=>formal i (Nat.le_succ i) _ (dvd_refl _) e link)
  target.part ⟨{a,b},mem_univ _⟩+target.part ((J₀).fire a)*target.part ((J₀).fire b)

include history scroll chamber warm top cal hospital fund slow in
/-- The true cell weights of an arbitrary compact test pair the signed double placement
against the same finite prescription. The same rooted budget applies to every summand. -/
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
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
    (heard:WilsonThermometerRegisteredPair.opening R simple D school strip q depth deep aged H cap cap_pos
      (ε:=1) zero_lt_one ≤ i)
    (orderWanted:ℕ) (surplus:q=WilsonThermometerRegisteredRate.order orderWanted (e₀)+1)
    (heat:warmDate R simple ≤ m) (funded:priceDate R simple school orderWanted (e₀) ≤ i)
    (rootFee:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (stencil:reach R ≤ R.alloy.B.a.clock.J (i+2)+1) :
      ∀ t a b:Fin 3, a≠b → a≠t → b≠t → ∀ link:Stationary.Link G (R.family.side i per),
      let B:=R.family.path.levels.budget i
      let β:=R.family.path.levels.clock.hatBeta i
      let angle:=Stationary.arm G (R.family.side i per) 1 link
      ∀ z:ℝ, |z| ≤ |H| * (Real.log β)^depth * ((B.B:ℝ)^2*B.threshold)/g₁ →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap * |z|) →
        let W:=Integral.sample g₁ angle
        flags (Ψ i).p.threshold W=∅ →
        ∀ (r:ℝ) (test:Test 3),
        ‖reduced A (N₀) (Nat.le_add_right i 2) r test a b W -
          ∑ y:T₀×T₀, WilsonThermometerAlignedCells.mass (R:=R) r (N₀) test y *
            prescribed R A π Γ school t a b link y‖ ≤
          (∫ x:Points 3,‖test x‖) * (price (rate R) (K₀) orderWanted (e₀)*g₁^orderWanted) := by
  intro t a b ab at' bt' link B β angle z tested probes W healthy r test
  let w:=WilsonThermometerAlignedCells.mass (R:=R) r (N₀) test
  let truePair (y:T₀×T₀):=actualTransport R.family (N:=i+2)
    (WilsonThermometerRegisteredCells.raw A (N₀) a b (atOrigin y)) (Nat.le_add_right i 2) W
  let filed:=prescribed R A π Γ school t a b link
  let E:=price (rate R) (K₀) orderWanted (e₀)*g₁^orderWanted
  have point (y:T₀×T₀):‖truePair y-filed y‖ ≤ E:=by
    have measured:=WilsonThermometerRegisteredRate.original R simple A hk D Q π Γ Ψ history scroll books chamber hi
      warm top school (placement (R:=R) (N₀) y) op lesson cal ahead hospital fund slow strip
      q depth deep aged H cap cap_pos late date checked near shape size space room opStage ranks width refs
      floor fit path pass month fits shelved load packed tender held fieldDate heard orderWanted surplus
      heat funded rootFee stencil t a b ab at' bt' link z tested probes healthy
    dsimp only [filed,prescribed]
    simp only [←WilsonThermometerNumericalStation.returned R A D π Γ (φ:=φ) school
      (placement (R:=R) (N₀) y) (without t)]
    exact measured
  have nonneg:0 ≤ E:=(norm_nonneg _).trans (point (0,0))
  change ‖(∑ y:T₀×T₀, w y*truePair y) - ∑ y:T₀×T₀, w y*filed y‖ ≤ _
  calc
    _ = ‖∑ y:T₀×T₀, w y*(truePair y-filed y)‖ := by simp_rw [mul_sub,sum_sub_distrib]
    _ ≤ ∑ y:T₀×T₀, ‖w y*(truePair y-filed y)‖ := norm_sum_le ..
    _ ≤ ∑ y:T₀×T₀, ‖w y‖*E := sum_le_sum fun y _=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (point y) (norm_nonneg _)
    _ = (∑ y:T₀×T₀,‖w y‖)*E := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (variation (R:=R) r (N₀) test) nonneg

end YM.Integration.WilsonThermometerRegisteredCompact
