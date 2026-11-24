import YM.Integration.WilsonReceivedGeometricFieldPrice
import YM.Integration.WilsonThermometerUnitFilingWhole

/-! Complete amplified or erased response at the fixed older flat read on its true quiet law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedEndpoint
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonGeometricSignedCapture
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (simple : G.Simple) {m i N per k : ℕ}
  (cut : i<N)
  (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m  ≤  i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
variable {X : Fin 3 → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀v, Set (X v)) (pieces : ∀v, Submodule ℝ (X v)) (ages : Fin 3 → ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly J)
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead actors pieces ages
    order shelf seats i hi physical)
  (fired : Wallet actors)
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta

local notation "homes" => (P.passport.coarser (sheet).ratio).origin

local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "incomingAt" => LocalComparison.actualPush R.family N per i (physical fired)

local notation "debt" => (fun (ε:ℝ) (p:ℕ)=>(8*Ω^P.op.count)*P.rent+ε*g^p)
local notation "B" => ((2:ℝ)^(order+shelf+2)+4)
local notation "M" => (fun (α:ℝ)=>WilsonFullFaceSignedPower.constants (S) (Y) α B)

local notation "rel" => R.alloy.B.a.clock.forcedAllowance i
local notation "heat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "k₀" => (WilsonFullFaceSignedPower.inter*(Fintype.card (Multi.parts (J)).Mode:ℝ)*125)

include course cut in
theorem original (gradeCap : (∑j,ages j)  ≤  14) (way : WayStation R.kit) (station : WilsonCenteredCaptureClock.first R simple  ≤  i)
    (sec : R.t 0  ≤  i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ)  ≤  Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose  ≤  i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose  ≤  i)
    (pass : Pass D bank R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2)
    (deep:2*(0+1)+8 ≤ order)(aged:0+4 ≤ 3*k+2)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count 0 order k deep aged
      (by norm_num:(0:ℝ)<1/2)  ≤  i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple 0)).choose  ≤  i)
    (hired:8*Ω^P.op.count*P.rent ≤ 1/2)
    (c:(J).Mode→ℂ)(y:Site ((C).side i per))(Z:Support ((C).side i per))(center:y ∈ Z)
    (homes_in:∀j:Fin 3,homes j ∈ Z)(rad:ℕ)(near:∀j:Fin 3,separation (homes j) y ≤ rad)
    (radius:rad ≤ (Ψ i).p.B)(box:Z⊆halo (Ψ i).p.B {y})(α:ℝ)(strength:(Ψ i).p.supportExponent ≤ α)
    (ticket:TicketP R.alloy R.kit D bank){u:ℕ}(floor:m ≤ u)(ui:u ≤ i)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))  ≤  u) :
    let nominal := fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    let residual := fun U=>take c (incomingAt U)-((Ψ i).eval U:ℂ)*take c (nominal U)
    MeasureTheory.Integrable residual (prior G _) ∧
    ∀ j, u ≤ j→∀ ji:j ≤ i, ‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) residual j ji‖ ≤ 
      weightBill c P.w*(g⁻¹)^87*(testPrice (F)*k₀+15*|M α|) := by
  intro nominal residual
  have w:=course.1.walk i hi cut.le
  have head:=course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  have gp:0<g:=(congrArg Coat.gStep head.beta) ▸ P.issued.Waffle.soon.1
  have low:g ≤ 1:=(congrArg Coat.gStep head.beta) ▸ P.issued.Waffle.soon.2.1
  have shape:(Ψ i).p=R.family.path.levels.budget i:=w.truep.point
  have originalReserve:(heat)^(-((0:ℕ):ℝ))+hitWidth (Ψ i).p*rel/κ ≤ ((4:ℝ)^0+1)*g^0:=by
    rw [shape]
    exact (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple 0)).choose_spec i saved N per cut
  have reserve:(heat)^(-(0:ℝ))+hitWidth (Ψ i).p*rel/κ ≤ 2:=by
    simpa only [Nat.cast_zero,pow_zero,mul_one,one_add_one_eq_two] using originalReserve
  let e:=debt (1/2) 0
  have e₁:e ≤ 1:=by dsimp [e];simp only [pow_zero,mul_one];linarith only [hired]
  have e₀:0 ≤ e:=add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg P.issued.Waffle.paysAbove.le _)) P.active.le) (by positivity)
  let cost:=e+heat^(-(0:ℝ))+hitWidth (Ψ i).p*rel/κ
  have vpos:0 ≤ hitWidth (Ψ i).p:=by unfold hitWidth; positivity
  have hrel:=allowance_pos R.alloy.B.a.clock i
  have kpos:0<κ:=Real.sqrt_pos.mpr hrel
  have cost₀:0 ≤ cost:=add_nonneg (add_nonneg e₀ (Real.rpow_pos_of_pos
    (zero_lt_one.trans (R.alloy.B.a.fits.delayed _)) _).le)
    (div_nonneg (mul_nonneg vpos hrel.le) kpos.le)
  have costs:cost ≤ 3:=by dsimp only [cost]; linarith only [e₁,reserve]
  let bill:=weightBill c P.w
  have bp:0 ≤ bill:=sum_nonneg fun s _=>div_nonneg (norm_nonneg _) (Poly.worth P.issued.earning.positive s).le
  have xp:0 ≤ (g⁻¹)^87:=pow_nonneg (inv_nonneg.mpr gp.le) _
  obtain ⟨h,fmt,rem,out,unit,size⟩:=WilsonGeometricSignedPower.stored (d:=0) R simple cut hk D bank π Γ Ψ
    course books hi ahead order shelf seats actors pieces ages physical P fired gradeCap way station sec slow ready early late
    pass hospital narrow load 0 0 (Nat.zero_le _) deep aged (by norm_num:(0:ℝ)<1/2) opened e₁ c y Z center homes_in
    rad near radius box α strength
  let charge:=bill*(|M α| *(g⁻¹)^87*3)
  have bound:bill*(M α*(g⁻¹)^87*cost) ≤ charge:=mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) xp) costs cost₀ (mul_nonneg (abs_nonneg _) xp)) bp
  have paid:h.remBound y (Ψ i) κ charge:=by
    obtain ⟨a,b,forced,reg,pay,cover⟩:=rem
    refine ⟨a,b,forced,reg,pay.trans ?_,cover⟩
    simpa only [bill,cost,e,Nat.cast_zero] using bound
  have pos:0 ≤ charge:=mul_nonneg bp (mul_nonneg (mul_nonneg (abs_nonneg _) xp) (by norm_num))
  have x₁:1 ≤ g⁻¹:=(one_le_inv₀ gp).2 low
  have short:(g⁻¹)^6 ≤ (g⁻¹)^87:=pow_le_pow_right₀ x₁ (by decide)
  have raw0:0 ≤ k₀:=by
    have h0:=WilsonFullFaceSignedPower.bounded.choose_spec.1
    unfold WilsonFullFaceSignedPower.inter
    positivity
  have test0:0 ≤ testPrice (F):=zero_le_one.trans (probe_budget (F)).choose_spec.choose_spec.1
  have raw: bill*k₀/g^6*e ≤ bill*(g⁻¹)^87*k₀:=by
    have aux:0 ≤ bill*k₀/g^6:=div_nonneg (mul_nonneg bp raw0) (pow_nonneg gp.le _)
    calc _  ≤  (bill*k₀/g^6)*1:=mul_le_mul_of_nonneg_left e₁ aux
         _ = bill*k₀*(g⁻¹)^6:=by rw [mul_one,div_eq_mul_inv,inv_pow]
         _  ≤  bill*k₀*(g⁻¹)^87:=mul_le_mul_of_nonneg_left short (mul_nonneg bp raw0)
         _ = _ := by ring
  have sx:=WilsonGeometricSignedPrimary.unit h _ unit size
  have entry : ‖h.x 0‖  ≤  (F).coeffSize h.x :=
    single_le_sum (fun j _=>norm_nonneg (h.x j)) (mem_univ 0)
  have costX:‖h.x 0‖ ≤ testPrice (F)*(bill*(g⁻¹)^87*k₀):= by
    apply (entry.trans sx).trans
    apply mul_le_mul_of_nonneg_left _ test0
    simpa only [bill,e,mul_assoc] using raw
  have whole:=WilsonThermometerUnitFilingWhole.original R simple way D bank ticket π Γ Ψ course cut.le floor ui gate
    y h fmt paid pos
  have same:h.density y (S) (Ψ i)=residual:=funext out
  rw [←same]
  refine ⟨(WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course hi cut.le (S) (Y) y h fmt paid).2,?_⟩
  intro j uj ji
  calc _  ≤  ‖h.x 0‖+5*charge:=whole.1 j uj ji
       _  ≤  testPrice (F)*(bill*(g⁻¹)^87*k₀)+5*charge:=add_le_add costX (le_rfl : 5*charge ≤ 5*charge)
       _ = _ := by dsimp only [charge,bill];ring 
end YM.Integration.WilsonThermometerMixedEndpoint
end
