import YM.Integration.WilsonRootedTwoDateHardEarned
import YM.Integration.WilsonRootedTwoDateCoolingRows

/-! The fixed source stencil controls the full fresh hard coupon on the original running schedule. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardGeometry
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence WilsonRootedTwoDateProduct OPE.Therm
open WilsonLimitConstruction Push.AbsoluteSums.Animals RG.Shoot Pert.Asymptotics
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ}
local notation "Y" => R.family.path.rep N p (m+1)
local notation "Γ" => Stock.census V
local notation "step" => R.family.path.levels.clock.op (m+1) p
local notation "oneW" => fun _ : V=>(1:ℝ)
variable (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m) (hG : G.Simple)

local notation "tests" => (ActualOriginalQPointSetup.request R old.labels old.request).tests

open RG3.Script.Picnic WilsonLimitConstruction.FundedMarkedFieldSplit QLocalMarkedJoinedCatalogue QLocalThermalPacketDivision
local notation "newD" => (ActualOriginalQPointSetup.request R fresh.labels fresh.request).tests
local notation "raw" => ActualOriginalQInitialInput.packets R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
local notation "coupling" => regulatorRun R.family N p (m+1)

open Extra.Iteration.Comparison ActualWilsonDirtyPartners
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG fresh.labels fresh.request fresh.schedule
local notation "off₀" => ActualOriginalQInitialInput.cover R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
local notation "oldG" => regulatorRun R.family N p (m+2)
local notation "κ" => Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1))
local notation "k₀" => R.family.path.levels.clock.forcedAllowance (m+1)
local notation "B₀" => (A₀).inputNorm m
local notation "amt" => (A₀).admittedCost m
local notation "incl" => WilsonRootedTwoDateHardSource.inclusion (D:=newD) (tests)


open OriginalMarkedRunAction WilsonRootedInteriorPhysicalExponent


omit [Nonempty V] in
def stencilPrice (R : Run G) (J : Request V) (v : V → MS.Rake.Label B) : ℝ :=
  2*(Fintype.card (Stock.census V).Mode:ℝ)*(2/(3*J.inputSupport)) *
    ((2:ℝ)^ActualOriginalQLayout.rankCap R v * Real.exp (4*J.inputSupport*(ActualOriginalQPointCover.bound R v:ℝ)))

omit [Nonempty V] in
theorem charged : QLocalThermalJoinedRate.charge (raw) (B₀) (off₀) (amt) ≤
    stencilPrice R fresh.request fresh.labels * blockSites (R.family.path.levels.budget (m+1)).B * fresh.schedule.admittedCost m := by
  let p₀ := (B₀)
  have room : p₀.supportExponent=fresh.request.inputSupport := (fresh.schedule.input_norm m).reserve
  have block : p₀.B=(R.family.path.levels.budget (m+1)).B := (fresh.schedule.input_norm m).block
  have rank : (raw).rankCap=ActualOriginalQLayout.rankCap R fresh.labels := rfl
  have money : (amt)=2*fresh.schedule.admittedCost m := rfl
  have cov : (off₀)≤ActualOriginalQPointCover.bound R fresh.labels :=
    OriginalMarkedBirthStencil.covered R fresh.labels fresh.request fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree p₀
  have exp_bound : Real.exp (4*fresh.request.inputSupport*((off₀):ℝ)) ≤
      Real.exp (4*fresh.request.inputSupport*(ActualOriginalQPointCover.bound R fresh.labels:ℝ)) :=
    Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr cov) (mul_nonneg (by norm_num) fresh.request.input_support_pos.le))
  have cash := fresh.schedule.admitted_cost_nonnegative m
  have sig := fresh.request.input_support_pos
  have block0 : 0 ≤ blockSites (R.family.path.levels.budget (m+1)).B := by unfold blockSites; positivity
  change QLocalThermalJoinedRate.charge (raw) p₀ (off₀) (amt) ≤ _
  rw [QLocalThermalJoinedRate.charge,rank,room,block,money]
  unfold stencilPrice
  calc _ ≤ (Fintype.card (Γ).Mode:ℝ)*(2/(3*fresh.request.inputSupport))*blockSites (R.family.path.levels.budget (m+1)).B *
        ((2:ℝ)^ActualOriginalQLayout.rankCap R fresh.labels * Real.exp (4*fresh.request.inputSupport*(ActualOriginalQPointCover.bound R fresh.labels:ℝ)) * (2*fresh.schedule.admittedCost m)) := by gcongr
       _ = _ := by ring

end YM.Integration.WilsonRootedTwoDateHardGeometry
