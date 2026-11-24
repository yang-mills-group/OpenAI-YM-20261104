import YM.Integration.WilsonEmittedLandedReceipt
import YM.Integration.WilsonMeasuredRankedOnDate
import YM.Integration.WilsonMeasuredLandedReceipt
import YM.Integration.WilsonMeasuredLandedCurrency
import YM.Integration.WilsonOlderFreshGraphPhysicalSalary

/-! The nonbare emitted graph field and its authentic lower expense come from the same marked post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedLandedGraphField
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
variable (y:Site (R.family.side ((j+1)+1) per))
local notation "S"=>WilsonOlderFreshGraphPointWallet.point y
local notation "letterPost"=>Earn.Passport.point (fun _:Unit=>y)

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

local notation "pieces" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => d)
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G d Q σ₀
local notation "birth" => (fun (T:slate) (x:Wallet A) (U:Config G (R.family.side (i₁+1) per)) =>
  ((Ψ (i₁+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows S A) (Coat.gStep (Ψ (i₁+1)).beta) x U))
local notation "down" => (fun (T:slate) (x:Wallet A) => LocalComparison.actualPush R.family N per i₁ (birth T x))
local notation "upper" => (fun (T:slate) => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A pieces grades school.order school.horizon school.pieces i₁ hi (birth T))
local notation "lower" => (fun (T:slate) => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A pieces grades school.order school.horizon school.pieces j floor (down T))
local notation "origin₁" => ((letterPost).coarser (R.family.path.levels.clock.op i₁ per).ratio).origin ()
local notation "u" => (Stock.census Unit).fire ()
local notation "p₁" => Ψ i₁
local notation "d₁" => R.family.labels.level d
local notation "κ" => LocalComparison.forcedDivisor R.family i₁
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
variable (p:ℕ) {ε:ℝ} (ep:0 < ε)
local notation "q₁" => (p+2)
private theorem divide_pos {ε:ℝ} (ep:0 < ε) : 0 < ε/16 := div_pos ep (by norm_num)
local notation "ep₀" => divide_pos ep

def Outcome (T:WilsonOlderFreshGraphSlate.Copy G d Q
    (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))))
    (c amp τ:ℝ) (shelf:ℕ) (lim:ℝ) : Prop :=
  WilsonEmittedLandedReceipt.paid (N:=N) (inputRank:=d) R hk D Q₀ π Γ Ψ books ahead
    school floor A (T.rows (WilsonOlderFreshGraphPointWallet.point y) A) d τ c amp shelf lim

private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8 ≤ J) : 2*q+8 ≤ J := by omega
private theorem ready_age {q k:ℕ} (h:q+4+4 ≤ 3*k+2) : q+3 ≤ 3*k+2 := by omega

include history scroll chamber warm top cal hospital in
theorem original (simple:G.Simple) (cut:i₁<N) (cap:∀t,‖value A t‖≤1)
    {τ:ℝ} (pos:0<τ) (bounded:τ≤1) (pass:Pass D Q₀ R.alloy R.kit)
    (live:WilsonMeasuredSemesterSubpower.onset R 1 (half_pos (show (0:ℝ)<1 by norm_num)) ≤ i₁)
    (printed:∃ T:slate, (∑k,T.fare k) ≤ βhat^((1:ℝ)/2)*(1+massF) ∧
      WilsonOlderFreshGraphDatedSalary.Published R L a depth (i₁+1) w ⟨⟨N,cut⟩,f⟩ T)
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
    ∃ (T:slate) (c amp:ℝ), 0<c ∧ 0<amp ∧ amp⁻¹≤2*βhat*(1+massF) ∧
      WilsonOlderFreshGraphDatedSalary.Published R L a depth (i₁+1) w ⟨⟨N,cut⟩,f⟩ T ∧
      Outcome (N:=N) (R:=R) (hk:=hk) (D:=D) (Q₀:=Q₀) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (books:=books)
        (floor:=floor) (school:=school) (ahead:=ahead) (y:=y) (A:=A) T c amp τ high (ε*g₀^p*(1+massF)) := by
  obtain ⟨T,c,amp,cp,ap,rad,named,land⟩:=WilsonOlderFreshGraphPhysicalSalary.original R hk D Q₀ π Γ Ψ
    history scroll books chamber hi warm top school op lesson cal ahead hospital y A L a depth w f simple
    cut cap pos bounded (show (0:ℝ)<1 by norm_num) pass live printed seats shape phase enrolled within budget high space test
  have invoice:amp⁻¹≤2*βhat*(1+massF):=by simpa only [Real.rpow_one] using rad
  obtain ⟨H,F,hp,names,hm,weights,cost,rent,regular,force,file,funded,_⟩:=
    WilsonMeasuredLandedAdvance.original R hk D Q₀ π Γ Ψ books ahead school floor A (T.rows S A)
      history path cut pass month narrow d land M₀ office way simple slow prepared fixed date late grossDate
      fareDate scroll chamber hospital warm top q₁ ready deep aged ep₀ opened recalled masks soft space
      lowerDate booked test positive small
  obtain ⟨h,C,E,hp₀,cp₀,_,fw,fc,_⟩:=funded
  refine ⟨T,c,amp,cp,ap,invoice,named,H,F,hp,names,hm,weights,cost,rent,regular,force,file,⟨h,C,hp₀,cp₀,fw,fc⟩,?_⟩
  intro x
  have load:school.pieces≤Burn.horizon k+2 := by obtain ⟨_,_,_,v,_,_⟩:=school;exact v
  have fits:school.order≤Burn.horizon k+1 := by obtain ⟨_,_,_,_,v,_⟩:=school;exact v
  have packed:school.order+school.horizon≤Burn.horizon k+2 := by obtain ⟨_,_,_,_,_,v⟩:=school;exact v
  have active:WilsonFirstReceivedEarnedFee.opening R simple H.op.count (q₁+4) school.order k deep aged
      (tolerance_pos R d q₁ (WilsonMeasuredRankedMenu.fee_positive R d M₀ ep₀)) ≤ i₁ := by simpa [H.capacity] using opened
  obtain ⟨E,b,fmt,rem,exactEval,paid⟩:=WilsonMeasuredRankedOnDate.original R hk D Q₀ π Γ Ψ books ahead
    A pieces grades school.order school.horizon school.pieces floor (birth T) H F file history cut pass month
    fits narrow x d M₀ office way simple slow prepared fixed date late grossDate fareDate scroll chamber
    hospital warm top load packed high space q₁ ready deep aged ep₀ active recalled masks soft ()
  have same:=WilsonOlderFreshWordReversion.same H.model (T.rows S A) hp names hm
  have gp:=WilsonMeasuredLandedCurrency.native R simple per cut.le money
  refine ⟨E,b,?_,?_,?_,?_⟩
  · simpa only [hp] using fmt
  · simpa only [hp] using rem
  · simpa only [same,hp] using exactEval
  · exact WilsonMeasuredLandedCurrency.normalized ap gp.2.1 gp.2.2.1 (by positivity) invoice ep.le (by simpa only [weights] using paid)

end YM.Integration.WilsonEmittedLandedGraphField
end
