import YM.Integration.WilsonCapturedOpeningRaffle
import YM.Integration.WilsonOriginalSoldDatedPupils
import YM.Integration.WilsonMeasuredSemesterSubpower
import YM.Integration.WilsonReceivedClosePhysicalBirths

/-! Restore all original occupied radii on the very two-age sold pupil before the cutoffs. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace YM.Integration.WilsonCapturedSoldRadius
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology


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
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages
open WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion WilsonEmittedFiledGerm
open QuadraticLocal.Earn
open WilsonMeasuredJointCensusCash
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums
open WilsonOlderFreshPointRegistry

open MeasureTheory WilsonOlderFreshLocatedBook WilsonOlderFreshLocatedPayment
open WilsonOlderFreshLocatedRoster WilsonMeasuredPointHouseSeats
open WilsonOlderFreshGraphAllStages QuadraticLocal.Advent.Sycamore
open WilsonWindowBookPurchase WilsonWindowUniversalSchool
open scoped Classical BigOperators
open WilsonOlderFreshThermometerRoom WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash
open WilsonOlderFreshLocatedRoster WilsonOlderFreshPointRegistry

open WilsonOlderFreshThermometerCollector

open QuadraticLocal.Advent QuadraticLocal.Advent.Oak AllOrder.Floe.Step.PlanV QuadraticLocal.Affinity
open WilsonOriginalThreeCompactProduct WilsonOlderFreshThermometerSources
variable {G:Gauge}(R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q₀:D.Tab R.rolls)
    {φ:ℕ → ℕ} (L:Primer.Families R.family)(a:hue G){Q q m N j per:ℕ}
    (dmax:Fin 3 → ℕ)(depth:∀v,WilsonOlderFreshThermometerRoom.weight v<dmax v)
    (digit:Fin 3 → ∀j,Site (R.family.S.block j))
local notation "K" => WilsonOlderFreshThermometerRoom.horizon Q q
local notation "S" => WilsonOlderFreshThermometerRoom.semester Q q
local notation "σ₀" => (fun j:ℕ=>Poetry.Agenda.seed D φ (Burn.horizon (K)) (R.alloy.B.a.clock.J j))
local notation "grades" => WilsonOlderFreshThermometerRoom.weight
variable (T:WilsonOlderFreshThermometerSources.Table (m:=m) (N:=N) (Q:=Q) R dmax (fun j:ℕ=>Poetry.Agenda.seed D φ (Burn.horizon (WilsonOlderFreshThermometerRoom.horizon Q q)) (R.alloy.B.a.clock.J j)))
  (hk:Burn.horizon (WilsonOlderFreshThermometerRoom.horizon Q q)+2 ≤ R.alloy.B.a.clock.J m)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
  (Ψ:∀j,Rep G (R.family.side j per))(books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (floor:m ≤ j)(live:j+1<N)(op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Oak.Lesson (N:=N) R hk D Q₀ π Γ (floor.trans (Nat.le_succ j)))
  {I:Type}[Fintype I](owner:I→Fin 3)(sites:Fin 3→Site (R.family.side ((j+1)+1) per))
  (columns:∀z,Letter (R.family.labels.level (WilsonOlderFreshThermometerRoom.weight (owner z))))(films:∀z,Studio (dmax (owner z)))
  (A:Fin 3→Set ℂ)(charge:I→ℂ)
local notation "hi" => floor.trans (Nat.le_succ j)
local notation "T₀" => WilsonOlderFreshThermometerSources.selected (m:=m) (N:=N) (Q:=Q) (j:=(j+1)+1) R dmax (σ₀) T (Nat.le_succ_of_le (floor.trans (Nat.le_succ j))) live owner columns films
local notation "roster" => WilsonOriginalPointCompactRoster.rows owner grades sites (T₀) A charge
local notation "ρ" => Ψ ((j+1)+1)
local notation "g₀" => Coat.gStep (ρ).beta
local notation "x₁" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "blank" => (fun _:Fin 3=>(⊥:Submodule ℝ ℂ))
local notation "source" => (fun t U=>((ρ).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut roster (g₀) t U))
local notation "Ω" => Oak.expenseReal R hk D Q₀ π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead (S).order (S).horizon
local notation "net" => WilsonOriginalPointCompactCash.ceiling I (cap charge) (ticket (fun z=>‖films z‖) (x₁))
local notation "J" => Stock.census (Fin 3)

attribute [local irreducible] Poetry.Agenda.seed WilsonOlderFreshThermometerSources.selected

local notation "earlier" => (fun t:Wallet A => LocalComparison.actualPush R.family N per (j+1) ((source) t))
local notation "depth₀" => Burn.horizon (K)+2
local notation "tape₀" => AllOrder.Floe.Step.tape depth₀
local notation "nextCut" => Nat.lt_trans (Nat.lt_succ_self j) live
local notation "upper" => Post (N:=N) R hk D Q₀ π Γ Ψ books ahead A (blank) grades (S).order (S).horizon op.count (j+1) (hi) (source)
local notation "lower" => Post (N:=N) R hk D Q₀ π Γ Ψ books ahead A (blank) grades (S).order (S).horizon op.count j floor (earlier)


local notation "pole" => ((∑v:Fin 3,grades v)+1)
def openingInvoice (mass χ:ℝ)(height valence:ℕ):ℝ:=(1+mass)*(χ+10000*2^(height+valence)*χ^(valence+9))
local notation "paidUpper" => openingInvoice (net) (x₁) ((S).order+(S).horizon+1) (pole)
local notation "bill" τ:max ε:max => ((paidUpper)*x₁*max 1 (max (budgetR R j*budgetR R (j+1)) (τ+ε)))
local notation "read" P:max F:max => WilsonOriginalSoldDatedPupils.Read R D Q₀ L a dmax depth digit T hk π Γ Ψ books ahead floor live op owner sites columns films A charge P F
local notation "traced" => WilsonOriginalSoldDatedPupils.Traced R D Q₀ L a dmax depth digit T hk π Γ Ψ books ahead floor live op lesson owner sites columns films A charge

private theorem product {V:Type}[DecidableEq V] {C:Marker.Census V} (s:C.Mode) {w:V→ℝ} {Y:ℝ}
    (pos:∀v,0<w v)(control:∀v,(w v)⁻¹≤Y):
    (Poly.toll w s)⁻¹ ≤ Y^s.val.card:=by
  rw [Poly.toll,←Finset.prod_inv_distrib]
  simpa using (Finset.prod_le_prod (s:=s.val) (f:=fun v=>(w v)⁻¹) (g:=fun _=>Y)
    (fun v _=>inv_nonneg.mpr (pos v).le) (fun v _=>control v))

theorem original (simple:G.Simple)(scroll:VowsR.LawScroll G φ){Z:ℝ}{shape:PhysicalNext.ThroughLaunch.Orders}
    (house:Treehouse.VariableHouse R D Q₀ scroll books Z ahead shape)
    (path:PlanV.Path D R.alloy Q₀ (Burn.horizon (K)) N m π Γ)
    (course:Concourse R.alloy R.kit R.T π Γ m N per (K) Ψ)
    (count:op.count=(S).pieces)(test:Wallet A){τ ε:ℝ}(ep:0<ε)
    (late:WilsonOriginalThreeAgeDated.gate R simple Q q ep≤j+1)
    (stage:WilsonMeasuredSemesterSubpower.onset R 6 zero_lt_one ≤ j+1)
    (cold:(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ (j+1)+1)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ) (paid:traced τ ε):
    ∃(P:upper), P.rent=τ ∧ (∀v,(P.w v)⁻¹ ≤ paidUpper) ∧ P.passport=Passport.point sites ∧ P.modelIndex=WilsonOriginalPointCompactRoster.Index owner grades (T₀) ∧ HEq P.model (roster) ∧
    ∀η:ℝ,0<η → η≤1 → ∃F:lower,
      WilsonOriginalReceivedChain.Filed R hk D Q₀ π Γ Ψ books ahead A (blank) grades (S).order (S).horizon op.count floor (source) P F ∧
      F.rent ≤ max (τ+ε*(Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)^q) η ∧
      (∀v,(F.w v)⁻¹≤(P.w v)⁻¹*x₁*max 1 (max (budgetR R j*budgetR R (j+1)) (τ+ε))) ∧
      (∀s:(J).Mode, (Poly.toll F.w s)⁻¹ ≤ (bill τ ε)^s.val.card) ∧
      (∀r:ℕ,r≤Q → r≤(S).order → (read P F) r):=by
  obtain ⟨P,rent,_,_,site,_,event,lesson₀,keys,same,_,exactPrice,_,_,_⟩:=paid.1.2
  have fits:(S).order≤Burn.horizon (K)+1:=by
    dsimp [WilsonOlderFreshThermometerRoom.semester,WilsonOlderFreshThermometerRoom.horizon,Burn.horizon];omega
  have load:op.count≤Burn.horizon (K)+2:=count.trans_le (S).sense
  have narrow:(S).horizon ≤ R.alloy.B.a.clock.J j:=(Nat.le_add_left ..).trans ((S).tall.trans (hk.trans (R.alloy.B.a.fits.mono floor)))
  have stageBill:=WilsonMeasuredSemesterSubpower.charged R hk D Q₀ π Γ Ψ course books (hi) live ahead
    A (blank) grades (S).order (S).horizon op.count (source) P 6 zero_lt_one stage house.licence.employed.station.1
      house.licence.forecast (narrow.trans (R.alloy.B.a.fits.mono j.le_succ)) (event.symm ▸ load)
  rw [Real.rpow_one] at stageBill
  have x1:1≤x₁:=(R.alloy.B.a.fits.delayed _).le
  have sy:Burn.horizon (K)+2≤R.alloy.B.a.clock.J ((j+1)+1):=hk.trans (R.alloy.B.a.fits.mono (by omega))
  have expense: max 1 (Oak.expenseReal R hk D Q₀ π Γ books (hi) op lesson ahead (S).order (S).horizon) ≤ x₁:=by
    rw [event,lesson₀] at stageBill
    refine max_le x1 ?_
    by_cases one:1≤Oak.expenseReal R hk D Q₀ π Γ books (hi) op lesson ahead (S).order (S).horizon
    · exact (le_self_pow₀ one (by decide:(6:ℕ)≠0)).trans stageBill
    · exact (le_of_not_ge one).trans x1
  have funding:=WilsonCapturedOpeningRaffle.original R warm course (show m≤(j+1)+1 by omega)
    live ((Nat.le_add_right ..).trans sy) ((Nat.le_add_right ..).trans ((S).tall.trans sy))
    ((Nat.le_add_left ..).trans ((S).tall.trans sy)) (load.trans sy) (pole)
  have toll:0≤(net):=by
    unfold WilsonOriginalPointCompactCash.ceiling WilsonOlderFreshThermometerCollector.cap WilsonOlderFreshThermometerCollector.ticket
    positivity
  have uniform (v:Fin 3):(P.w v)⁻¹≤paidUpper:=by
    rw [exactPrice v]
    exact mul_le_mul_of_nonneg_left (add_le_add expense funding) (by linarith only [toll])
  refine ⟨P,rent,uniform,site,keys,same,?_⟩
  obtain ⟨h,C,E,l,one,_,err,each⟩:=WilsonOriginalNamedCarriedThree.original R hk D Q₀ π Γ Ψ books ahead A (blank) grades
    (S).order (S).horizon op.count floor (source) P course path live house.licence.employed.station.1 scroll
    house.licence.employed house.licence.monthly house.licence.forecast fits narrow load (S).tall
    simple q (WilsonOriginalThreeAgeDated.deep Q q) (WilsonOriginalThreeAgeDated.aged Q q)
    ep late test (Passport.point sites) (roster) site keys same
  intro η pos small
  obtain ⟨F,_,change,_,fRent,_,roof,file,_⟩:=each η pos small
  have cg := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec ((j+1)+1) cold N per (by omega)
  have smallg : Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta ≤ 1:=by
    change Pert.Asymptotics.regulatorRun R.family N per ((j+1)+1)≤1; linarith only [cg.1,cg.2]
  have posg : 0≤Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta:=cg.1.le
  have cost : h ≤ max 1 (max (budgetR R j*budgetR R (j+1)) (τ+ε)):=by
    apply roof.trans;rw [rent];gcongr
    exact mul_le_of_le_one_right ep.le (pow_le_one₀ posg smallg)
  have earned:∀v,(F.w v)⁻¹≤(P.w v)⁻¹*x₁*max 1 (max (budgetR R j*budgetR R (j+1)) (τ+ε)):=by
    intro v
    rw [change v,inv_div,div_eq_mul_inv,mul_comm _ (P.w v)⁻¹,←mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left stageBill (inv_nonneg.mpr (P.salary.positive v).le))
      cost (zero_le_one.trans one) (mul_nonneg (inv_nonneg.mpr (P.salary.positive v).le) (zero_le_one.trans x1))
  have rent0:0≤τ+ε*(Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)^q:=
    add_nonneg (rent ▸ P.active.le) (mul_nonneg ep.le (pow_nonneg posg _))
  rw [rent] at err
  refine ⟨F,file,?_,earned,?_,fun r safe kept=>paid.2 P site keys same F file r safe kept⟩
  · rw [fRent];apply max_le_max_right
    exact (mul_le_mul_of_nonneg_left err (inv_nonneg.mpr (zero_le_one.trans one))).trans
      (mul_le_of_le_one_left rent0 (inv_le_one_of_one_le₀ one))
  · intro s
    apply product s F.salary.positive
    intro v
    exact (earned v).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (uniform v) (zero_le_one.trans x1))
      (zero_le_one.trans (le_max_left ..)))

end YM.Integration.WilsonCapturedSoldRadius
end
