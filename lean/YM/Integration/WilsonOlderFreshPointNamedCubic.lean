import YM.Integration.WilsonOlderFreshPointOriginalReturn
import YM.Integration.WilsonOlderFreshPointCubicDebit
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointNamedCubic
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

abbrev reporter (Q:ℕ):WilsonOlderFreshGraphAllStages.Query:=⟨⟨0,3,6,by decide,by decide⟩,Q⟩

variable {G:Gauge} (R:Run G){m j N per k:ℕ} (Qwork:ℕ)
variable
  (hk:Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (floor:m  ≤  j)

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
  {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
  (house:QuadraticLocal.Advent.Sycamore.Treehouse.VariableHouse R D Q₀ scroll books ZΘ ahead profile)
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

local notation "families" => (fun u:ℕ=>Flat.routes (R.family.path.levels.clock.op u 0).patch)
variable {dmax:ℕ} (a:hue G) (depth:(6:ℕ)<dmax)
    (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖f‖


variable (base:Site (R.family.side (j+1) per))
local notation "child" => Site (R.family.path.levels.S.block (j+1))
local notation "place" => fun z:child=>(R.family.path.levels.clock.op (j+1) per).ratio.assemble (base,z)
local notation "testAt" => fun z:child=>Dawn.throughW z dmax (Elm.growL R.family.path.levels (j+1)) f
local notation "salary" => fun z:child=>1+‖testAt z‖
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G (6:ℕ) Qwork σ₀
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
variable (p:ℕ) {ε:ℝ} (ep:0 < ε)
local notation "q₁" => (p+2+2)
private theorem divide_pos {ε:ℝ} (ep:0 < ε) : 0 < ε/16 := div_pos ep (by norm_num)
local notation "ep₀" => divide_pos ep

private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8  ≤  J) : 2*q+8  ≤  J := by omega
private theorem ready_age {q k:ℕ} (h:q+4+4  ≤  3*k+2) : q+3  ≤  3*k+2 := by omega

local notation "upperSide" => R.family.side ((j+1)+1) per
local notation "lowerSide" => R.family.side (j+1) per
local notation "stock" => Stock.census Unit
local notation "u" => (Stock.census Unit).fire ()
local notation "kernel" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => (6:ℕ))
local notation "birth" => fun (z:child) (T:slate) (t:Wallet A) (U:Config G upperSide) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A)
    (Coat.gStep (Ψ ((j+1)+1)).beta) t U)
local notation "down" => fun z (T:slate) (t:Wallet A)=>LocalComparison.actualPush R.family N per (j+1) (birth z T t)
local notation "lower" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces j floor (down z T)
local notation "origin" => fun z:child=>((Earn.Passport.point (fun _:Unit=>place z)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "rp" => Ψ (j+1)
local notation "F₁" => R.family.labels.level (6:ℕ)
local notation "section₁" => R.family.localSection (6:ℕ)
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "gl" => Coat.gStep (Ψ (j+1)).beta


local notation "passports" => fun z:child=>Earn.Passport.point (fun _:Unit=>place z)
local notation "upper" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces (j+1) (floor.trans (Nat.le_succ j)) (birth z T)



local notation "blockSide" => R.family.path.levels.S.block (j+1)
local notation "rate" => (((blockSide).val:ℝ)^(6:ℕ)/((blockSide).val:ℝ)^4)

local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "material" => fun (z:child) (T:slate) (t:Wallet A) (U:Config G upperSide)=>
  (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) gu t U).part u
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages

open WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion WilsonEmittedFiledGerm
open QuadraticLocal.Earn
local notation "letter" => Letter F₁
local notation "S₀" => (WilsonOlderFreshGraphPointWallet.point base)
local notation "unitMark" => (WilsonNeutralRenderedColumn.submitted S₀)
local notation "pinDigits" => (fun i:ℕ=>(0:Site (R.family.S.block i)))
local notation "pin" => pinDigits i₁
local notation "g₁" => (((blockSide).val:ℝ)^(6:ℕ))
local notation "Idx" => (R.family.labels.level 6).Index
local notation "atom" => fun b:Idx=>(WilsonNeutralCutoffAlphabet.filed (F₁)).symm (WilsonNeutralCopiedField.point (F₁) b)
local notation "coef" => fun(b:Idx)(v:letter)(ν:ℕ)=>PowerSeries.coeff ν
  (WilsonNeutralPointCourse.transfer R families a depth pinDigits N i₁ v (atom b))
variable (station:WilsonPositionThermometerCapStation.Group R.family 6) (phaseTest:ℂ→ₗ[ℝ]ℝ)
local notation "named" => WilsonNeutralOffsetCutoff.named R station N per (0:Fin 3)
local notation "coin" => fun b:Idx=>((WilsonOlderFreshPointDatedCoin.coin R (i₁+1) N per named phaseTest b):ℂ)
local notation "bookedMass" => Next.Rank.Spindle.paid R.family 6 (i₁+1) N per named
local notation "prior" T₀:max => fun v:letter=>(T₀ v).rows S₀ A
local notation "pole₁" => Launch.index stock grades u + 1


local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i₁)
open WilsonMeasuredJointCensusCash
variable (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums
local notation "target" d:max q:max=>2*4+(d+1)+1+(q+3)
local notation "account" H:max => Oak.figureReal R hk D Q₀ π Γ books hi (H).op (H).lesson ahead school.order school.horizon


private theorem eighth {ε:ℝ}(pos:0<ε):0<(ε/8)/16:=div_pos (div_pos pos (by norm_num)) (by norm_num)
private theorem rearrange (c x p y:ℂ): c*(x-p*y)=c*x-p*(c*y):=by ring

include history scroll chamber warm top cal in
set_option backward.isDefEq.respectTransparency false in
theorem original (q:ℕ) (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay) (cut:i₁<N) (cap:∀t,‖value A t‖≤1)
    {τ:ℝ} (pos:0<τ) (bounded:τ≤1) (pass:Pass D Q₀ R.alloy R.kit)
    (live:WilsonMeasuredSemesterSubpower.onset R 1 (half_pos (show (0:ℝ)<1 by norm_num)) ≤ i₁)
    (T:Idx→slate)(wage:∀b,(∑k,(T b).fare k) ≤ βhat^((1:ℝ)/2)*(salary pin))
    (source:∀b,WilsonOlderFreshPointCommission.Published R families a depth (i₁+1) (atom b) (⟨N,cut,pinDigits⟩,testAt pin) (T b))
    (seats:1≤op.count) (shape:op.count=school.pieces) (phase:school.order+1 ≤ op.stage)
    (enrolled:Qwork ≤ school.order) (within:(6:ℕ) ≤ school.horizon)
    (high:ℕ) (space:Sycamore.Boot.need high school ≤ R.alloy.B.a.clock.J (i₁+1))
    (path:PlanV.Path D R.alloy Q₀ (Burn.horizon k) N m π Γ)
    (month:Scholar.Month R.rolls D Q₀ R.alloy.delay)
    (narrow:school.horizon≤R.alloy.B.a.clock.J i₁)
    (M₀:WilsonMeasuredRankedMenu.Menu R (6:ℕ)) (office:M₀.onset ≤ i₁) (way : WayStation R.kit) 
    
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget i₁).supportExponent ≤ 100)
    (date : R.t (6:ℕ) ≤ i₁) (late : WilsonCenteredCaptureClock.first R simple ≤ i₁)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ i₁)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow.2 prepared ≤ i₁)
    (ready : (q+4)+1+6 ≤ R.alloy.B.a.clock.J i₁) (deep : 2*((q+4)+4+1)+8 ≤ school.order)
    (aged : (q+4)+4+4 ≤ 3*k+2) 
    (opened : WilsonFirstReceivedEarnedFee.opening R simple school.pieces ((q+4)+4) school.order k deep aged
      (tolerance_pos R (6:ℕ) (q+4) (WilsonMeasuredRankedMenu.fee_positive R (6:ℕ) M₀ (eighth ep))) ≤ i₁)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple school.order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R (6:ℕ) (q+4) (WilsonMeasuredRankedMenu.fee_positive R (6:ℕ) M₀ (eighth ep))) ≤ i₁)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (school.order+school.horizon+2) (q+4) 102
      (show 0 < WilsonMeasuredRankedMenu.fee R (6:ℕ) M₀ ((ε/8)/16)/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R (6:ℕ) M₀ (eighth ep)) (by norm_num)) ≤ i₁)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple (q+4) (WilsonMeasuredRankedMenu.fee_positive R (6:ℕ) M₀ (eighth ep)) ≤ i₁)

    (lowerDate:school.horizon≤R.alloy.B.a.clock.J j)
    (money:WilsonMeasuredLandedCurrency.first R simple≤j)
    (booked:WilsonReceivedMeasuredStampPrice.opening R simple (q+4) school.order k
      (ready_order deep) (ready_age aged) (eighth ep) ≤ i₁)

    (tube:LinkTube G) (programPaid:Covered (program tube) R)
    (strength:∀i,(R.family.path.levels.budget i).supportExponent≤100)
    (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (enough:3*(target (6:ℕ) q) ≤ Qwork)
    (gradeDate:WilsonMeasuredCourseGradeReturn.first R (reporter Qwork) simple slow tube programPaid strength q enough ep ≤ j)
    (issued:WilsonOlderFreshGraphReceivingFigure.first R simple ≤ i₁)
    (stride:WilsonOlderFreshPointLagPower.start R simple slow (6:ℕ) ≤ j)
    (later:WilsonOlderFreshPointEmittedWallet.activation (inputRank:=(6:ℕ)) R simple slow ≤ i₁)
    (load:school.pieces ≤ Burn.horizon k+2)
    (ℓ:ℕ) (inGrade:ℓ≤Qwork) (T₀:letter→WilsonOlderFreshGraphSlate.Copy G (6:ℕ) Qwork σ)
    (o:Loc G 1)(active:(6:ℕ) ≤ R.family.path.levels.clock.J (i₁+1))
    (fits:school.order≤Burn.horizon k+1)(width:0<σ₀)
    (budget:∀v:letter,(∑k',(T₀ v).fare k')≤R.alloy.B.a.clock.hatBeta i₁*(1+massF))
    (forward:∀b,∑v:letter,∑ν:Fin (Qwork+1),|coef b v ν.val|≤R.alloy.B.a.clock.hatBeta i₁)
    (issuedT:∀v:letter,WilsonOlderFreshPointCommission.Published R families a depth i₁ v (⟨N,cut.le,pinDigits⟩,f) (T₀ v))
    {U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)
    (v:ℕ→WilsonCoeffUV.Bank.Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)(paths:FundedOriginalVacuumPaths.prices R.kit)
    (opening:WilsonOriginalPrimerPostCover.opening R simple v funded paths k ≤ m)
    (t:Wallet A):

    ∃(E:Coefficient F₁ lowerSide)(bill:ℝ),E.Format base R.family.params rp ∧ E.remBound base rp κ bill ∧
      (∀U,E.density base section₁ rp U =
        (∑b:Idx,coin b * (((gl^ℓ:ℝ):ℂ)*(((g₁:ℝ):ℂ)*(down pin (T b) t U).part u)))-
        ((rp).eval U:ℂ)*(∑b:Idx,coin b*(((gl^ℓ:ℝ):ℂ)*
          (∑v:letter,(∑ν:Fin (Qwork-ℓ+1), (coef b v ν.val)*gl^ν.val) •
            (Spill.Foundry.uncut ((prior T₀) v) gl t U).part u)))) ∧
      bill+(F₁).coeffSize E.x ≤ 320*‖phaseTest.toContinuousLinearMap‖*bookedMass*
        ε*g₀^q*(1+massF):=by
  let up (b:Idx)(U:Config G lowerSide):= ((gl^ℓ:ℝ):ℂ)*(((g₁:ℝ):ℂ)*(down pin (T b) t U).part u)
  let low(b:Idx)(U:Config G lowerSide):= ((gl^ℓ:ℝ):ℂ)*(∑v:letter,
    (∑ν:Fin (Qwork-ℓ+1), (coef b v ν.val)*gl^ν.val) • (Spill.Foundry.uncut ((prior T₀) v) gl t U).part u)
  have col (b:Idx) := WilsonOlderFreshPointOriginalReturn.original (N:=N) (R:=R) (query:=(reporter Qwork))
    (hk:=hk) (D:=D) (Q₀:=Q₀) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (history:=history) (scroll:=scroll) (books:=books)
    (chamber:=chamber) (floor:=floor) (warm:=warm) (top:=top) (school:=school) (op:=op) (lesson:=lesson)
    (cal:=cal) (ahead:=ahead) (A:=A) (a:=a) (depth:=depth) (w:=atom b) (f:=f) (base:=base) (ep:=ep)
    (digit:=pinDigits) (simple:=simple) (slow:=slow) q hospital cut cap pos bounded pass live
    (T b) (wage b) (source b) seats shape phase enrolled within high space path month narrow M₀ office way prepared
    fixed date late grossDate fareDate ready deep aged opened recalled masks soft lowerDate money booked
    tube programPaid strength protection enough gradeDate issued stride later load ℓ inGrade T₀ o active fits width
    budget (forward b) issuedT grant v funded paths opening t
  have lawful:=(history.1.walk i₁ hi cut.le).truep.valid
  have κpos:0<κ:=Real.sqrt_pos.mpr (Push.Local.allowance_pos R.family.path.levels.clock i₁)
  have gp:0<g₀:=(WilsonMeasuredLandedCurrency.native R simple per cut.le money).2.1
  obtain ⟨E,bill,formed,paid,physical,wallet⟩:=WilsonOlderFreshPointCubicDebit.original R (i₁+1) N per
    station phaseTest cut lawful κpos up low (5*ε*g₀^q*(1+massF)) (by positivity) (fun b=>by
      obtain ⟨z,price,fmt,rem,fee,read⟩:=col b
      refine ⟨z,price,fmt,rem,?_,fee⟩
      intro U
      apply (read U).trans
      dsimp only [up,low,reporter]
      rw [rearrange])
  refine ⟨E,bill,formed,paid,?_,?_⟩
  · exact physical
  · convert wallet using 1
    ring

end YM.Integration.WilsonOlderFreshPointNamedCubic
