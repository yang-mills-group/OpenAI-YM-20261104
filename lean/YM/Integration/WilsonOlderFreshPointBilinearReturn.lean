import YM.Integration.WilsonOlderFreshPointGradeReturn
import YM.Integration.WilsonOlderFreshPointFiledValue
import YM.Integration.WilsonMeasuredPointGradeFourLocal
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointBilinearReturn
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

abbrev reporter (Qwork:ℕ):WilsonOlderFreshGraphAllStages.Query:=⟨⟨0,2,4,by decide,by decide⟩,Qwork⟩
variable (Qwork:ℕ)

variable {G:Gauge} (R:Run G){m j N per k:ℕ}
  (hk:Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (floor:m  ≤  j)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "i₁" => (j+1)
variable
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
variable {dmax:ℕ} (a:hue G) (depth:(4:ℕ)<dmax)
    (w:Letter (R.family.labels.level (4:ℕ))) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖f‖


variable (base:Site (R.family.side (j+1) per))
local notation "child" => Site (R.family.path.levels.S.block (j+1))
local notation "place" => fun z:child=>(R.family.path.levels.clock.op (j+1) per).ratio.assemble (base,z)
local notation "testAt" => fun z:child=>Dawn.throughW z dmax (Elm.growL R.family.path.levels (j+1)) f
local notation "salary" => fun z:child=>1+‖testAt z‖
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G (4:ℕ) Qwork σ₀
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
local notation "grades" => (fun _ : Unit => (4:ℕ))
local notation "birth" => fun (z:child) (T:slate) (t:Wallet A) (U:Config G upperSide) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A)
    (Coat.gStep (Ψ ((j+1)+1)).beta) t U)
local notation "down" => fun z (T:slate) (t:Wallet A)=>LocalComparison.actualPush R.family N per (j+1) (birth z T t)
local notation "lower" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces j floor (down z T)
local notation "origin" => fun z:child=>((Earn.Passport.point (fun _:Unit=>place z)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "rp" => Ψ (j+1)
local notation "F₁" => R.family.labels.level (4:ℕ)
local notation "section₁" => R.family.localSection (4:ℕ)
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "gl" => Coat.gStep (Ψ (j+1)).beta


local notation "passports" => fun z:child=>Earn.Passport.point (fun _:Unit=>place z)
local notation "upper" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces (j+1) (floor.trans (Nat.le_succ j)) (birth z T)



local notation "blockSide" => R.family.path.levels.S.block (j+1)
local notation "rate" => (((blockSide).val:ℝ)^(4:ℕ)/((blockSide).val:ℝ)^4)

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
variable (digit:∀i,Site (R.family.S.block i))
local notation "pin" => digit i₁
local notation "g₁" => (((blockSide).val:ℝ)^(4:ℕ))
local notation "coef" => fun(v:letter)(ν:ℕ)=>PowerSeries.coeff ν
  (WilsonNeutralPointCourse.transfer R families a depth digit N i₁ v w)
local notation "prior" T₀:max => fun v:letter=>(T₀ v).rows S₀ A
local notation "pole₁" => Launch.index stock grades u + 1


local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i₁)
open WilsonMeasuredJointCensusCash
variable (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums Extra.Histories Extra.Histories.Relay
local notation "target" d:max q:max=>2*4+(d+1)+1+(q+3)
local notation "account" H:max => Oak.figureReal R hk D Q₀ π Γ books hi (H).op (H).lesson ahead school.order school.horizon

include history in
theorem original (tube:LinkTube G) (programPaid:Covered (program tube) R)
    (strength:∀i,(R.family.path.levels.budget i).supportExponent ≤ 100)
    (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (q:ℕ) (enough:3*(target (4:ℕ) q) ≤ Qwork) (licensed:(4:ℕ) ≤ school.horizon)
    (late:WilsonMeasuredCourseGradeReturn.first R (reporter Qwork) simple slow tube programPaid strength q enough ep  ≤  j)
    (issued:WilsonOlderFreshGraphReceivingFigure.first R simple ≤ i₁)
    (cut:i₁<N) (pass:Pass D Q₀ R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
    (later:WilsonOlderFreshPointEmittedWallet.activation (inputRank:=(4:ℕ)) R simple slow ≤ i₁)
    (shelved:school.horizon≤R.alloy.B.a.clock.J i₁)(load:school.pieces≤Burn.horizon k+2)
    (T:slate)(T₀:letter→WilsonOlderFreshGraphSlate.Copy G 4 Qwork σ)
    (amp c τ expense lim:ℝ)(high depth₀:ℕ)
    (bought:0<amp ∧ amp⁻¹ ≤ 2*βhat*(salary pin))
    (receipt:WilsonMeasuredPointBilinear.Receipt (N:=N) R hk D Q₀ π Γ Ψ books floor school ahead (place pin) A
      T amp c τ expense lim (1+‖testAt pin‖) high depth₀)
    (tender:lim≤(ε/8)*g₀^(q+2)*(1+massF))
    (awake:WilsonMeasuredLandedCurrency.first R simple ≤ j)
    (stride:WilsonOlderFreshGraphPreimageFee.first R simple slow 4 ≤ i₁)
    (o:Loc G 1)(active:(4:ℕ) ≤ R.family.path.levels.clock.J (i₁+1))
    (room:Qwork≤ school.order)(one:1≤ school.pieces)
    (budget:∀v:letter,(∑k',(T₀ v).fare k')≤R.alloy.B.a.clock.hatBeta i₁*(1+massF))
    (forward:∑v:letter,∑ν:Fin (Qwork+1),|coef v ν.val|≤R.alloy.B.a.clock.hatBeta i₁)
    (issuedT:∀v:letter,WilsonOlderFreshPointCommission.Published R families a depth i₁ v (⟨N,cut.le,digit⟩,f) (T₀ v))
    (currency:∀t:Wallet A,‖WilsonOlderFreshGraphArmada.value A t‖≤1)
    (read:∀t:Wallet A,∀e≤Qwork,∀B₁:Stationary.Link G lowerSide,
      (((blockSide).val:ℂ)^(4:ℕ))*
        (peek dvd_rfl receipt.choose_spec.choose.model grades (π i₁) (Step.tape (Burn.horizon k+2)) t e B₁).part (unitMark).val=
      WilsonOlderFreshGraphArmada.value A t*(MvPolynomial.eval
        (FreeResolvent.flatten (Stationary.arm G lowerSide 1 B₁) ∘ Lotus.tint (S₀).center)
        (PowerSeries.coeff e (WilsonOlderFreshPointConvolution.after (N:=N) (i:=i₁)
          R families a depth digit w f lowerSide)):ℝ))
  (t:Wallet A):
    ∃(z:Coefficient F₁ lowerSide)(b:ℝ),z.Format base R.family.params rp ∧ z.remBound base rp κ b ∧
      b+(F₁).coeffSize z.x ≤ 5*ε*g₀^q*(1+massF) ∧
      ∀U,z.density base section₁ rp U=((g₁:ℝ):ℂ)*(down pin T t U).part u -
        ((rp).eval U:ℂ)*(∑v:letter,(∑ν:Fin (Qwork+1),(coef v ν.val)*gl^ν.val) •
              (Spill.Foundry.uncut ((T₀ v).rows S₀ A) gl t U).part u):=by
  classical
  let H:=receipt.choose
  let F:=receipt.choose_spec.choose
  obtain ⟨hp,_,_,hw,_,_,_,_,stocked,_,⟨h,C,hp₀,Kc,wr,cost⟩,columns⟩:=receipt.choose_spec.choose_spec
  have file:=stocked.1
  have location:((Earn.Passport.point (fun _:Unit=>place pin)).coarser
      (R.family.path.levels.clock.op i₁ per).ratio).origin ()=base:=
    (R.family.path.levels.clock.op i₁ per).ratio.assemble_parent (base,pin)
  have same:F.passport.origin ()=base:=by
    rw [show F.passport=H.passport.coarser (R.family.path.levels.clock.op i₁ per).ratio from file.passport,hp]
    exact location
  have earned:∃h C:ℝ,1≤h ∧ C≤budgetR R i₁ ∧ (∀v,F.w v=amp/((Oak.expenseReal R hk D Q₀ π Γ books hi H.op
        H.lesson ahead school.order school.horizon)^6*h)) ∧ F.cost=h⁻¹*C:= by
    refine ⟨h,C,hp₀,Kc,?_,cost⟩
    intro v
    simpa only [hw,H,F] using wr v
  obtain ⟨P,fmtP,remP,sizeP,phase⟩:=WilsonOlderFreshPointGradeReturn.original (R:=R) (query:=reporter Qwork)
    (hk:=hk) (D:=D) (Q₀:=Q₀) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (history:=history) (books:=books)
    (floor:=floor) (school:=school) (ahead:=ahead) (A:=A) (a:=a) (depth:=depth) (w:=w) (f:=f)
    (base:=base) (ep:=ep) (digit:=digit) (simple:=simple) (slow:=slow) tube programPaid strength protection
    q enough licensed late issued j (Nat.le_succ j) cut pass hospital later shelved load 0 (Nat.zero_le _)
    T H F T₀ amp bought earned same o active room one budget forward issuedT currency (by simpa only [Nat.sub_zero,F,reporter] using read) t
  have phased(U:Config G lowerSide):
      P.density base section₁ rp U=((rp).eval U:ℂ)*(g₁ • (Spill.Foundry.uncut F.model gl t U).part u -
        ∑v:letter,(∑ν:Fin (Qwork+1),(coef v ν.val)*gl^ν.val) •
              (Spill.Foundry.uncut ((T₀ v).rows S₀ A) gl t U).part u):=by
    rw [show P.density base section₁ rp U=_ from phase U]
    simp only [Nat.sub_zero,zero_add,reporter]
    congr 1
    simpa only [Fintype.sum_unique] using WilsonMeasuredOriginalCatalogueUnion.field (D:=Qwork)
      (fun _:Unit=>F.model) (prior T₀) g₁ coef gl u t U
  obtain ⟨E,b,fmtE,remE,measured,small⟩:=columns t
  have paid:=WilsonMeasuredPointGradeFourLocal.paid (N:=N) R hk D Q₀ π Γ Ψ books floor school ahead
    (place pin) A simple slow cut.le awake stride T F t E q ep.le (show 0≤1+massF by positivity)
    fmtE remE measured (small.trans tender)
  rcases paid with ⟨form,hard,values,price⟩
  rw [location] at form hard values
  have law:=(history.1.walk i₁ hi cut.le).truep.valid
  let Z:=Extra.Histories.stretch ((g₁:ℝ):ℂ) E
  change Z.Format base R.family.params rp at form
  change Z.remBound base rp κ (g₁*b) at hard
  obtain ⟨formats,rents⟩:=Extra.Histories.Relay.presentation form hard fmtP remP
  refine ⟨Extra.Histories.Relay.beside Z P,_,formats,rents,?_,?_⟩
  · rw [Extra.Histories.Relay.reckon]
    have cash:=(Extra.Histories.Size.add (F₁) Z.x P.x)
    change g₁*b+(F₁).coeffSize Z.x≤ε*g₀^q*(1+massF) at price
    dsimp only [Pert.Asymptotics.regulatorRun] at sizeP price ⊢
    linarith only [cash,sizeP,price]
  · intro U
    calc
      _ = Z.density base section₁ rp U+P.density base section₁ rp U:=
        congrFun (Extra.Histories.Relay.plus law hard remP section₁) U
      _ = _ :=by
        rw [show Z.density base section₁ rp U=_ from values U,phased U]
        simp only [Complex.real_smul]
        ring
end YM.Integration.WilsonOlderFreshPointBilinearReturn
end
