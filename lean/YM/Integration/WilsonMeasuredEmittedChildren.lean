import YM.Integration.WilsonEmittedLandedGraphField
import YM.Integration.WilsonOlderFreshGraphFiledPreimages
/-! A single nonbare appointment issues the original signed post on every
affine child of the same physical vertex for the normalized upper column.
The finite templates are the issued copies of their actual child tests. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredEmittedChildren
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k Q d:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (floor:m ≤ j)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "i₁" => (j+1)
variable
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ (floor.trans (Nat.le_succ j)))
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ (floor.trans (Nat.le_succ j)) (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i₁+1))
variable (A:Unit→Set ℂ)
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:d<dmax)
    (w:Letter (R.family.labels.level d)) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖Annex.compress dmax f‖


variable (base:Site (R.family.side (j+1) per))
local notation "child" => Site (R.family.path.levels.S.block (j+1))
local notation "place" => fun z:child=>(R.family.path.levels.clock.op (j+1) per).ratio.assemble (base,z)
local notation "testAt" => fun z:child=>Dawn.throughW z dmax (Elm.growL R.family.path.levels (j+1)) f
local notation "salary" => fun z:child=>1+‖Annex.compress dmax (testAt z)‖
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G d Q σ₀
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
variable (p:ℕ) {ε:ℝ} (ep:0 < ε)
local notation "q₁" => (p+2)
private theorem divide_pos {ε:ℝ} (ep:0 < ε) : 0 < ε/16 := div_pos ep (by norm_num)
local notation "ep₀" => divide_pos ep

private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8 ≤ J) : 2*q+8 ≤ J := by omega
private theorem ready_age {q k:ℕ} (h:q+4+4 ≤ 3*k+2) : q+3 ≤ 3*k+2 := by omega

include history scroll chamber warm top cal hospital in
theorem original (simple:G.Simple) (cut:i₁<N) (cap:∀t,‖value A t‖≤1)
    {τ:ℝ} (pos:0<τ) (bounded:τ≤1) (pass:Pass D Q₀ R.alloy R.kit)
    (live:WilsonMeasuredSemesterSubpower.onset R 1 (half_pos (show (0:ℝ)<1 by norm_num)) ≤ i₁)
    (printed:∀z:child,∃ T:slate, (∑k,T.fare k) ≤ βhat^((1:ℝ)/2)*(salary z) ∧
      WilsonOlderFreshGraphDatedSalary.Published R L a depth (i₁+1) w ⟨⟨N,cut⟩,testAt z⟩ T)
    (seats:1≤op.count) (shape:op.count=school.pieces) (phase:school.order+1 ≤ op.stage)
    (enrolled:Q ≤ school.order) (within:d ≤ school.horizon) (budget:school.order+d ≤ Burn.horizon k+2)
    (high:ℕ) (space:Sycamore.Boot.need high school ≤ R.alloy.B.a.clock.J (i₁+1))
    (path:PlanV.Path D R.alloy Q₀ (Burn.horizon k) N m π Γ)
    (month:Scholar.Month R.rolls D Q₀ R.alloy.delay)
    (narrow:school.horizon≤R.alloy.B.a.clock.J i₁)
    (M₀:WilsonMeasuredRankedMenu.Menu R d) (office:M₀.onset ≤ i₁) (way : WayStation R.kit) 
    (slow : ∀ n, ((R.family.S.block n).val:ℝ) ≤ Real.log (Lambda R.family.path.levels n))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget i₁).supportExponent ≤ 100)
    (date : R.t d ≤ i₁) (late : WilsonCenteredCaptureClock.first R simple ≤ i₁)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ i₁)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i₁)
    (ready : q₁+1+6 ≤ R.alloy.B.a.clock.J i₁) (deep : 2*(q₁+4+1)+8 ≤ school.order)
    (aged : q₁+4+4 ≤ 3*k+2) 
    (opened : WilsonFirstReceivedEarnedFee.opening R simple school.pieces (q₁+4) school.order k deep aged
      (tolerance_pos R d q₁ (WilsonMeasuredRankedMenu.fee_positive R d M₀ ep₀)) ≤ i₁)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple school.order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R d q₁ (WilsonMeasuredRankedMenu.fee_positive R d M₀ ep₀)) ≤ i₁)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (school.order+school.horizon+2) q₁ 102
      (show 0 < WilsonMeasuredRankedMenu.fee R d M₀ (ε/16)/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R d M₀ ep₀) (by norm_num)) ≤ i₁)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q₁ (WilsonMeasuredRankedMenu.fee_positive R d M₀ ep₀) ≤ i₁)

    (lowerDate:school.horizon≤R.alloy.B.a.clock.J j)
    (money:WilsonMeasuredLandedCurrency.first R simple≤j)
    (booked:WilsonReceivedMeasuredStampPrice.opening R simple q₁ school.order k
      (ready_order deep) (ready_age aged) ep₀ ≤ i₁)
    (test:Wallet A) {next:ℝ} (positive:0<next) (small:next≤1) :

    ∃(T:child → slate)(c amp:child → ℝ),∀z:child,
      0<c z ∧ 0<amp z ∧ (amp z)⁻¹ ≤ 2*βhat*(salary z) ∧
      WilsonOlderFreshGraphDatedSalary.Published R L a depth (i₁+1) w ⟨⟨N,cut⟩,testAt z⟩ (T z) ∧
      WilsonEmittedLandedReceipt.paid (N:=N) (inputRank:=d) R hk D Q₀ π Γ Ψ books ahead school
        floor A ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) d τ (c z) (amp z)
        high (ε*g₀^p*(salary z)):=by
  let sales (z:child):=WilsonEmittedLandedGraphField.original R hk D Q₀ π Γ Ψ history scroll books chamber floor
    warm top school op lesson cal ahead hospital (place z) A L a depth w (testAt z) p ep simple
    cut cap pos bounded pass live (printed z) seats shape phase enrolled within budget high space path month
    narrow M₀ office way slow prepared fixed date late grossDate fareDate ready deep aged opened recalled masks soft
    lowerDate money booked test positive small
  choose T c amp cert using sales
  exact ⟨T,c,amp,cert⟩

end YM.Integration.WilsonMeasuredEmittedChildren
end
