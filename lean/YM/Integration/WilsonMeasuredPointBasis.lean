import YM.Integration.WilsonMeasuredPointBilinear
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointBasis
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k Q:ℕ}
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

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:(4:ℕ)<dmax)
    (pivot:(R.family.labels.level 4).Index) (f:Studio dmax)
local notation "w₄" => WilsonNeutralBilinearLetters.plain (R.family.labels.level 4) pivot
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖f‖

local notation "pieces" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => (4:ℕ))
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G (4:ℕ) Q σ₀
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
local notation "d₁" => R.family.labels.level (4:ℕ)
local notation "κ" => LocalComparison.forcedDivisor R.family i₁
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
variable (p:ℕ) {ε:ℝ} (ep:0 < ε)
local notation "q₁" => (p+2)
private theorem divide_pos {ε:ℝ} (ep:0 < ε) : 0 < ε/16 := div_pos ep (by norm_num)
local notation "ep₀" => divide_pos ep

private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8 ≤ J) : 2*q+8 ≤ J := by omega
private theorem ready_age {q k:ℕ} (h:q+4+4 ≤ 3*k+2) : q+3 ≤ 3*k+2 := by omega

variable (digit:∀h,Site (R.family.S.block h))

include history scroll chamber warm top cal hospital in
theorem original (simple:G.Simple) (cut:i₁<N) (cap:∀t,‖value A t‖≤1)
    {τ:ℝ} (pos:0<τ) (bounded:τ≤1) (pass:Pass D Q₀ R.alloy R.kit)
    (live:WilsonMeasuredSemesterSubpower.onset R 1 (half_pos (show (0:ℝ)<1 by norm_num)) ≤ i₁)
    (T:slate)(salary:(∑k,T.fare k) ≤ βhat^((1:ℝ)/2)*(1+massF))
    (source:WilsonOlderFreshPointCommission.Published R L a depth (i₁+1) w₄ (⟨N,cut,digit⟩,f) T)
    (seats:1≤op.count) (shape:op.count=school.pieces) (phase:school.order+1 ≤ op.stage)
    (enrolled:Q ≤ school.order) (within:(4:ℕ) ≤ school.horizon)
    (high:ℕ) (space:Sycamore.Boot.need high school ≤ R.alloy.B.a.clock.J (i₁+1))
    (path:PlanV.Path D R.alloy Q₀ (Burn.horizon k) N m π Γ)
    (month:Scholar.Month R.rolls D Q₀ R.alloy.delay)
    (narrow:school.horizon≤R.alloy.B.a.clock.J i₁)
    (M₀:WilsonMeasuredRankedMenu.Menu R (4:ℕ)) (office:M₀.onset ≤ i₁) (way : WayStation R.kit) 
    (slow : ∀ n, ((R.family.S.block n).val:ℝ) ≤ Real.log (Lambda R.family.path.levels n))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget i₁).supportExponent ≤ 100)
    (date : R.t (4:ℕ) ≤ i₁) (late : WilsonCenteredCaptureClock.first R simple ≤ i₁)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ i₁)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i₁)
    (ready : q₁+1+6 ≤ R.alloy.B.a.clock.J i₁) (deep : 2*(q₁+4+1)+8 ≤ school.order)
    (aged : q₁+4+4 ≤ 3*k+2) 
    (opened : WilsonFirstReceivedEarnedFee.opening R simple school.pieces (q₁+4) school.order k deep aged
      (tolerance_pos R (4:ℕ) q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀)) ≤ i₁)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple school.order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R (4:ℕ) q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀)) ≤ i₁)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (school.order+school.horizon+2) q₁ 102
      (show 0 < WilsonMeasuredRankedMenu.fee R (4:ℕ) M₀ (ε/16)/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀) (by norm_num)) ≤ i₁)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀) ≤ i₁)

    (lowerDate:school.horizon≤R.alloy.B.a.clock.J j)
    (money:WilsonMeasuredLandedCurrency.first R simple≤j)
    (booked:WilsonReceivedMeasuredStampPrice.opening R simple q₁ school.order k
      (ready_order deep) (ready_age aged) ep₀ ≤ i₁)
    (hardOrder:q₁+6*school.pieces≤R.alloy.B.a.clock.J i₁)
    (fiscal:WilsonMeasuredSemesterSubpower.onset R 6 zero_lt_one≤ i₁)
    (threshold:WilsonMeasuredNeutralFiledStock.onset R simple≤ i₁)
    (light:(ε/16)*(Coat.gStep (R.family.path.rep N per (i₁+1)).beta)^q₁≤1)
    (test:Wallet A) :
    ∃ (c amp:ℝ), 0<c ∧ 0<amp ∧ amp⁻¹≤2*βhat*(1+massF) ∧
      WilsonOriginalPrimerStampedRay.Matched T (WilsonOlderFreshPointChart.chart R L a depth (i₁+1) w₄ (⟨N,cut,digit⟩,f)) ∧
      WilsonMeasuredPointBilinear.Receipt (N:=N) R hk D Q₀ π Γ Ψ books floor school ahead y A T amp c τ
        ((ε/16)*(Coat.gStep (R.family.path.rep N per (i₁+1)).beta)^q₁)
        (ε*g₀^p*(1+massF)) (1+massF) high q₁ := by
  obtain ⟨c,amp,cp,ap,rad,named,land⟩:=WilsonOlderFreshPointLanded.original R hk D Q₀ π Γ Ψ
    history scroll books chamber hi warm top school op lesson cal ahead hospital y A L a depth w₄ f digit
    simple cut cap pos bounded (half_pos (show (0:ℝ)<1 by norm_num)) pass live T salary source
    seats shape phase enrolled within high space test
  have base:1≤βhat:=(R.alloy.B.a.fits.delayed (i₁+1)).le
  let z:=βhat^((1:ℝ)/2)
  have z1:1≤z:=Real.one_le_rpow base (by norm_num)
  have one:1≤1+massF:=by linarith [norm_nonneg f]
  have enough:1≤z*(1+massF):=one_le_mul_of_one_le_of_one_le z1 one
  have square:z*z=βhat:=by
    dsimp only [z];rw [←Real.rpow_add (by linarith:0<βhat)];norm_num
  have invoice:amp⁻¹≤2*βhat*(1+massF):=rad.trans (calc
    z*(1+z*(1+massF)) ≤ z*(z*(1+massF)+z*(1+massF)) :=
       mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans z1)
    _ = 2*βhat*(1+massF):=by rw [←square];ring)
  have matched:=WilsonOlderFreshPointChart.original R L a depth (i₁+1) w₄ (⟨N,cut,digit⟩,f) T named
  obtain ⟨H,hp,weights,cost,rent,names,hm,regular,force⟩:=land
  have load:school.pieces≤Burn.horizon k+2 := by obtain ⟨_,_,_,v,_,_⟩:=school;exact v
  have fits:school.order≤Burn.horizon k+1 := by obtain ⟨_,_,_,_,v,_⟩:=school;exact v
  have packed:school.order+school.horizon≤Burn.horizon k+2 := by obtain ⟨_,_,_,_,_,v⟩:=school;exact v
  have available:(H.w ())⁻¹≤2*βhat*(1+massF):=by simpa only [weights] using invoice
  obtain ⟨F,stored,fee,h,C,E,h₀,price,_,_,wallet,stocks⟩:=WilsonMeasuredNeutralRestamp.original
    R hk D Q₀ π Γ Ψ books ahead A pieces school.order school.horizon school.pieces floor (birth T)
    H history path cut pass scroll chamber month hospital way simple fits lowerDate load packed q₁
    (ready_order deep) (ready_age aged) ep₀ light booked fiscal threshold hardOrder test
    (1+massF) (zero_lt_one.trans_le one) available
  have file:=stored.1
  refine ⟨c,amp,cp,ap,invoice,matched,H,F,hp,names,hm,weights,cost,rent,regular,force,
    ?_,?_,⟨h,C,h₀,price,wallet,stocks⟩,?_⟩
  · simpa only [rent] using stored
  · simpa only [rent] using fee
  intro x
  have active:WilsonFirstReceivedEarnedFee.opening R simple H.op.count (q₁+4) school.order k deep aged
      (tolerance_pos R (4:ℕ) q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀)) ≤ i₁ := by simpa [H.capacity] using opened
  obtain ⟨E,b,fmt,rem,exactEval,paid⟩:=WilsonMeasuredRankedOnDate.original R hk D Q₀ π Γ Ψ books ahead
    A pieces grades school.order school.horizon school.pieces floor (birth T) H F file history cut pass month
    fits narrow x (4:ℕ) M₀ office way simple slow prepared fixed date late grossDate fareDate scroll chamber
    hospital warm top load packed high space q₁ ready deep aged ep₀ active recalled masks soft ()
  have same:=WilsonOlderFreshWordReversion.same H.model (T.rows S A) hp names hm
  have gp:=WilsonMeasuredLandedCurrency.native R simple per cut.le money
  refine ⟨E,b,?_,?_,?_,?_⟩
  · simpa only [hp] using fmt
  · simpa only [hp] using rem
  · simpa only [same,hp] using exactEval
  · exact WilsonMeasuredLandedCurrency.normalized ap gp.2.1 gp.2.2.1 (by positivity) invoice ep.le (by simpa only [weights] using paid)

end YM.Integration.WilsonMeasuredPointBasis
end
