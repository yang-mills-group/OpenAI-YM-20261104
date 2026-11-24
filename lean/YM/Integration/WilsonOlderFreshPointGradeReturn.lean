import YM.Integration.WilsonOlderFreshPointCatalogue
import YM.Integration.WilsonOlderFreshPointBasisWallet
import YM.Integration.WilsonOlderFreshPointEmittedWallet
import YM.Integration.WilsonMeasuredCourseGradeReturn
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointGradeReturn
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k:ℕ} (query:WilsonOlderFreshGraphAllStages.Query)
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
variable {dmax:ℕ} (a:hue G) (depth:query.letter.toll<dmax)
    (w:Letter (R.family.labels.level query.letter.toll)) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖f‖


variable (base:Site (R.family.side (j+1) per))
local notation "child" => Site (R.family.path.levels.S.block (j+1))
local notation "place" => fun z:child=>(R.family.path.levels.clock.op (j+1) per).ratio.assemble (base,z)
local notation "testAt" => fun z:child=>Dawn.throughW z dmax (Elm.growL R.family.path.levels (j+1)) f
local notation "salary" => fun z:child=>1+‖testAt z‖
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G query.letter.toll query.order σ₀
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
local notation "grades" => (fun _ : Unit => query.letter.toll)
local notation "birth" => fun (z:child) (T:slate) (t:Wallet A) (U:Config G upperSide) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A)
    (Coat.gStep (Ψ ((j+1)+1)).beta) t U)
local notation "down" => fun z (T:slate) (t:Wallet A)=>LocalComparison.actualPush R.family N per (j+1) (birth z T t)
local notation "lower" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces j floor (down z T)
local notation "origin" => fun z:child=>((Earn.Passport.point (fun _:Unit=>place z)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "rp" => Ψ (j+1)
local notation "F₁" => R.family.labels.level query.letter.toll
local notation "section₁" => R.family.localSection query.letter.toll
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "gl" => Coat.gStep (Ψ (j+1)).beta


local notation "passports" => fun z:child=>Earn.Passport.point (fun _:Unit=>place z)
local notation "upper" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces (j+1) (floor.trans (Nat.le_succ j)) (birth z T)



local notation "blockSide" => R.family.path.levels.S.block (j+1)
local notation "rate" => (((blockSide).val:ℝ)^query.letter.toll/((blockSide).val:ℝ)^4)

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
local notation "g₁" => (((blockSide).val:ℝ)^query.letter.toll)
local notation "coef" => fun(v:letter)(ν:ℕ)=>PowerSeries.coeff ν
  (WilsonNeutralPointCourse.transfer R families a depth digit N i₁ v w)
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

include history in
theorem original (tube:LinkTube G) (programPaid:Covered (program tube) R)
    (strength:∀i,(R.family.path.levels.budget i).supportExponent ≤ 100)
    (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (q:ℕ) (enough:3*(target query.letter.toll q) ≤ query.order) (licensed:query.letter.toll ≤ school.horizon)
    (late:WilsonMeasuredCourseGradeReturn.first R query simple slow tube programPaid strength q enough ep  ≤  j)
    (issued:WilsonOlderFreshGraphReceivingFigure.first R simple ≤ i₁)
    (probe:ℕ) (report:probe ≤ i₁) (cut:i₁<N) (pass:Pass D Q₀ R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
    (later:WilsonOlderFreshPointEmittedWallet.activation (inputRank:=query.letter.toll) R simple slow ≤ i₁)
    (shelved:school.horizon≤R.alloy.B.a.clock.J i₁)(load:school.pieces≤Burn.horizon k+2)
    (ℓ:ℕ) (inGrade:ℓ ≤ query.order) (T:slate) (H:upper pin T) (F:lower pin T)
    (T₀:letter→WilsonOlderFreshGraphSlate.Copy G query.letter.toll query.order σ)
    (amp:ℝ)(bought:0<amp ∧ amp⁻¹ ≤ 2*βhat*(salary pin))
    (earned:∃h C:ℝ,1≤h ∧ C≤budgetR R i₁ ∧ (∀v,F.w v=amp/((Oak.expenseReal R hk D Q₀ π Γ books hi H.op
        H.lesson ahead school.order school.horizon)^6*h)) ∧ F.cost=h⁻¹*C)
    (same:F.passport.origin ()=base)(o:Loc G 1)(active:query.letter.toll ≤ R.family.path.levels.clock.J (i₁+1))
    (room:query.order≤ school.order)(one:1≤ school.pieces)
    (budget:∀v:letter,(∑k',(T₀ v).fare k')≤R.alloy.B.a.clock.hatBeta i₁*(1+massF))
    (forward:∑v:letter,∑ν:Fin (query.order+1),|coef v ν.val|≤R.alloy.B.a.clock.hatBeta i₁)
    (issuedT:∀v:letter,WilsonOlderFreshPointCommission.Published R families a depth i₁ v (⟨N,cut.le,digit⟩,f) (T₀ v))
    (currency:∀t:Wallet A,‖WilsonOlderFreshGraphArmada.value A t‖≤1)
    (read:∀t:Wallet A,∀e≤query.order-ℓ,∀B₁:Stationary.Link G lowerSide,
      (((blockSide).val:ℂ)^query.letter.toll)*
        (peek dvd_rfl F.model grades (π i₁) (Step.tape (Burn.horizon k+2)) t e B₁).part (unitMark).val=
      WilsonOlderFreshGraphArmada.value A t*(MvPolynomial.eval
        (FreeResolvent.flatten (Stationary.arm G lowerSide 1 B₁) ∘ Lotus.tint (S₀).center)
        (PowerSeries.coeff e (WilsonOlderFreshPointConvolution.after (N:=N) (i:=i₁)
          R families a depth digit w f lowerSide)):ℝ))
  (t:Wallet A):
    ∃z:Coefficient F₁ lowerSide,z.Format base R.family.params rp ∧
      z.remBound base rp κ (3*(ε*(regulatorRun R.family N per probe)^q)*(1+massF)) ∧
      (F₁).coeffSize z.x  ≤  (ε*(regulatorRun R.family N per probe)^q)*(1+massF) ∧
      ∀U,z.density base section₁ rp U=((rp).eval U:ℂ)*
        (∑a₀:Names Unit letter (query.order-ℓ),weight g₁ coef a₀ •
          (gl^(ℓ+lag a₀) • (Spill.Foundry.uncut (rows (fun _:Unit=>F.model) (prior T₀) a₀) gl t U).part u)):=by
  classical
  let cap:=query.order-ℓ
  let space:=Names Unit letter cap
  have geom:=WilsonOlderFreshGraphFixedFigure.original R query hk D Q₀ π Γ Ψ history books floor school
    ahead A base simple cut issued query.letter.toll licensed pin T H
  have widths:=WilsonMeasuredIssuedCensusWallet.aperture (R:=R) (hk:=hk) (D:=D) (floor:=floor) (simple:=simple) protection
  have W₁:1≤R.alloy.B.a.clock.hatBeta i₁:=(R.alloy.B.a.fits.delayed i₁).le
  have width₁:0<σ:=Poetry.Agenda.stem ..
  obtain ⟨w₀,priorWallet,priorCash⟩:=WilsonOlderFreshPointBasisWallet.original R families a depth digit w f T₀ base A
    currency width₁ school.order school.pieces room one W₁ budget forward
  have arms(a₀:space):Scene.Armada (rows (fun _:Unit=>F.model) (prior T₀) a₀)
      (radius (fun _:Unit=>F.w) (fun v _=>w₀ v) a₀) grades σ
      (cost (fun _:Unit=>F.cost) (fun _=>1) a₀) school.order school.pieces query.letter.toll:=by
    cases a₀ with
    | inl p₀=>
      have found:=WilsonOlderFreshGraphSingleShelf.original _ _ _ _ _ _ _ _ F.salary
      rw [F.capacity] at found
      exact found
    | inr av=>exact (priorWallet av.1).2.2
  have issuedCash:=WilsonOlderFreshPointEmittedWallet.original (R:=R) (hk:=hk) (D:=D) (Q:=Q₀)
    (π:=π) (Γ:=Γ) (Ψ:=Ψ) (course:=history) (books:=books) (floor:=floor) (school:=school)
    (ahead:=ahead) (actors:=A) (model:=T.rows (WilsonOlderFreshGraphPointWallet.point (place pin)) A) (cut:=cut) (pass:=pass) simple slow H F later hospital shelved load f pin
    bought.1 bought.2 earned
  have cash:=WilsonMeasuredJointCensusCash.original (D:=cap) u (fun _:Unit=>F.w) (fun v _=>w₀ v)
    (fun _:Unit=>F.cost) (fun _=>1) g₁ coef W₁ (show 0≤1+massF by positivity)
    (by simpa only [Fintype.sum_unique,abs_of_nonneg (show 0≤g₁ by positivity)] using issuedCash)
    (priorCash cap (Nat.sub_le ..))
  have source:=(eventually_atTop.mp (WilsonMeasuredAllFieldCensusReturn.original tube R simple
    programPaid strength slow query.letter.toll q query.order enough ep)).choose_spec j late
  have canonical:=history.1.walk i₁ hi cut.le
  have bp:(rp).p=R.family.path.levels.budget i₁:=canonical.truep.point
  have st:gl=(Real.sqrt (R.family.path.rep N per i₁).beta)⁻¹:=by rw [canonical.beta];rfl
  have ht:=WilsonOlderFreshGraphSchoolCapacity.original R hk j per query.order floor school
  have paid:=source m N per k probe π Γ Ψ history hi cut report space Unit stock
    (address (fun _:Unit=>F.modelIndex) (fun v:letter=>(T₀ v).Roster)) (fun _=>Wallet A)
    (passport (fun _:Unit=>F.passport) (fun _:letter=>Passport.point (fun _:Unit=>base)))
    (rows (fun _:Unit=>F.model) (prior T₀))
    (radius (fun _:Unit=>F.w) (fun v _=>w₀ v)) (fun _=>grades) (fun _=>t)
    (weight g₁ coef) (fun a₀=>ℓ+lag a₀) (fun a₀=>ℓ+lag a₀)
    (fun _=>school.order) (fun _=>school.pieces) (fun _=>query.letter.toll)
    (fun _=>school.order+school.horizon+1) (cost (fun _:Unit=>F.cost) (fun _=>1))
    (fun _=>2*(account H).mist) (fun _=>σ) unitMark () (fun _=>π i₁)
    (fun _=>Step.tape (Burn.horizon k+2)) base (1+massF)
  dsimp only at paid
  apply paid arms
  · intro a₀
    simpa only [bp,st] using geom.2.1
  · intro a₀
    have lagged:lag a₀ ≤ cap:=by
      cases a₀ with
      | inl z=>exact Nat.zero_le _
      | inr h=>exact Nat.le_of_lt_succ h.2.isLt
    have more:query.order ≤ capacity (R.family.path.levels.clock.op j per).patch query.order:=
      by unfold capacity;omega
    exact ⟨(Nat.add_le_add_right (Nat.add_le_add_left licensed school.order) 1).trans ht.1,ht.2,
      (show ℓ+lag a₀ ≤ query.order by dsimp [cap] at lagged;omega).trans more,ht.1,le_rfl⟩
  · intro a₀
    exact ⟨budget_nonneg ((arms a₀).suggests 0),Poetry.Agenda.stem ..,widths⟩
  · intro a₀
    simpa only [bp] using geom.2.2.2
  · exact by change ()∈({()}:Finset Unit);simp
  · intro q₀; cases q₀ with
    | inl z=>exact same
    | inr h=>rfl
  · positivity
  · exact cash
  · intro e cut₀ dir
    have old:=WilsonOlderFreshPointCatalogue.original R families a depth digit simple o cut.le active w f T₀ base A
      currency width₁ issuedT F.model (π i₁) (Step.tape (Burn.horizon k+2)) cap (Nat.sub_le ..) t (read t)
    apply WilsonMeasuredWholeGradeCensus.funded (rows (fun _:Unit=>F.model) (prior T₀))
      (fun _=>grades) (fun _=>t) lag unitMark (fun _=>π i₁) (fun _=>Step.tape (Burn.horizon k+2)) ℓ
      (weight g₁ coef) pole₁ query.order inGrade old e _ dir
    omega
  · intro a₀
    have toll:Launch.index stock grades (unitMark).val=query.letter.toll:=by
      change (∑i∈({()}:Finset Unit),query.letter.toll)=query.letter.toll
      simp
    rw [toll];omega

end YM.Integration.WilsonOlderFreshPointGradeReturn
end
