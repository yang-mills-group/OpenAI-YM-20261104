import YM.Integration.WilsonRootedTwoDateHardGeometry

/-! A common printed radius chosen before the original cutoff, period and external tests. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardClock
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



def fraction (σ a b : ℝ) : ℝ := min 1 (σ/2) / (1+max a 0+max b 0)

private theorem spec (a b : ℝ) {σ : ℝ} (hσ : 0<σ) :
    0<fraction σ a b ∧ fraction σ a b≤1 ∧ fraction σ a b*a≤σ/2 ∧ fraction σ a b*b≤1 := by
  let e:=min 1 (σ/2)
  let C:=1+max a 0+max b 0
  have ep:0<e:=lt_min zero_lt_one (half_pos hσ)
  have ca:0 ≤ max a 0:=le_max_right _ _
  have cb:0 ≤ max b 0:=le_max_right _ _
  have c1:1≤C:=by dsimp [C];linarith
  have cp:=zero_lt_one.trans_le c1
  have bill:(e/C)*C=e:=div_mul_cancel₀ _ cp.ne'
  refine ⟨div_pos ep cp,(div_le_one cp).mpr ((min_le_left 1 (σ/2)).trans c1),?_,?_⟩
  · calc _ ≤ (e/C)*C:=mul_le_mul_of_nonneg_left (by dsimp [C];linarith [le_max_left a 0]) (div_pos ep cp).le
         _ ≤ σ/2:=bill.trans_le (min_le_right _ _)
  · calc _ ≤ (e/C)*C:=mul_le_mul_of_nonneg_left (by dsimp [C];linarith [le_max_left b 0]) (div_pos ep cp).le
         _ ≤ 1:=bill.trans_le (min_le_left _ _)

private theorem both {v n divisor B σ b k τ C roof : ℝ} (hσ : 0<σ) (hv : 0≤v) (hn : 0≤n) (hk : 0≤divisor) (hB : 0≤B)
    (basis : 2*k*B≤σ) (before : b≤1) (tau : τ≤1) (cash : 0≤C) (limit : C≤roof) :
    let s := fraction σ (2*v*divisor*B) (2*v*n*roof)
    0<s ∧ s≤1 ∧ 2*(k+v*(divisor*(s*b)))*B≤3*σ/2 ∧ 2*v*n*((s*τ)*C)≤1 := by
  let s := fraction σ (2*v*divisor*B) (2*v*n*roof)
  obtain ⟨positive,one,old,fee⟩:=spec (2*v*divisor*B) (2*v*n*roof) hσ
  have tag : s*(2*v*divisor*B*b) ≤ σ/2 := (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) before) positive.le).trans old
  have packet : 2*v*n*(τ*C) ≤ 2*v*n*roof := mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left cash tau).trans limit) (by positivity)
  refine ⟨positive,one,?_,?_⟩
  · calc _ = 2*k*B+s*(2*v*divisor*B*b) := by ring
         _ ≤ 3*σ/2 := by linarith only [basis,tag]
  · calc _ = s*(2*v*n*(τ*C)) := by ring
         _ ≤ s*(2*v*n*roof) := mul_le_mul_of_nonneg_left packet positive.le
         _ ≤ 1 := fee

omit [Nonempty V] in
def rate (R : Run G) (J : Request V) (v : V → MS.Rake.Label B) (A : NumericSchedule R.family J) (m : ℕ) : ℝ :=
  let blocks := blockSites (R.family.path.levels.budget (m+1)).B
  let marks := (Fintype.card V:ℝ)
  fraction J.inputSupport (2*marks*Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1))*blocks)
    (2*marks*(Fintype.card (Stock.census V).Mode:ℝ)*(WilsonRootedTwoDateHardGeometry.stencilPrice R J v * blocks * A.admittedCost m))

omit [Nonempty V] in
theorem positive (R : Run G) (J : Request V) (v : V → MS.Rake.Label B) (A : NumericSchedule R.family J) (m : ℕ) :
    0<rate R J v A m ∧ rate R J v A m≤1 :=
  ⟨(spec _ _ J.input_support_pos).1,(spec _ _ J.input_support_pos).2.1⟩

omit [Nonempty V] in
theorem purchased (A : NumericSchedule R.family fresh.request) (book : fresh.schedule.admittedCost m ≤ A.admittedCost m)
    {previous τ : ℝ} (small : previous≤1) (one : τ≤1) (basis : 2*(k₀)*blockSites (B₀).B≤(B₀).supportExponent) :
    let s := rate R fresh.request fresh.labels A m
    2*((k₀)+(Fintype.card V:ℝ)*((κ)*(s*previous)))*blockSites (B₀).B≤3*(B₀).supportExponent/2 ∧
    2*(Fintype.card V:ℝ)*(Fintype.card (Γ).Mode:ℝ)*QLocalThermalJoinedRate.charge (raw) (B₀) (off₀) (s*(τ*(amt)))≤1 := by
  let s := rate R fresh.request fresh.labels A m
  let p₀ := (B₀)
  have res : p₀.supportExponent=fresh.request.inputSupport := (fresh.schedule.input_norm m).reserve
  have blk : p₀.B=(R.family.path.levels.budget (m+1)).B := (fresh.schedule.input_norm m).block
  have hσ := fresh.request.input_support_pos
  have hcost := fresh.schedule.admitted_cost_nonnegative m
  have block0 : 0≤blockSites (R.family.path.levels.budget (m+1)).B := by unfold blockSites; positivity
  have amount : 0≤(amt) := mul_nonneg (by norm_num) hcost
  have fee0 : 0≤QLocalThermalJoinedRate.charge (raw) p₀ (off₀) (amt) := by
    have := p₀.exponent_pos
    unfold QLocalThermalJoinedRate.charge blockSites
    positivity
  have constant0 : 0 ≤ WilsonRootedTwoDateHardGeometry.stencilPrice R fresh.request fresh.labels := by
    unfold WilsonRootedTwoDateHardGeometry.stencilPrice
    positivity
  have roof := (WilsonRootedTwoDateHardGeometry.charged fresh hG).trans (mul_le_mul_of_nonneg_left book (mul_nonneg constant0 block0))
  have base : 2*(k₀)*blockSites (R.family.path.levels.budget (m+1)).B≤fresh.request.inputSupport := by simpa only [←blk,←res] using basis
  have paid := both (v:=(Fintype.card V:ℝ)) (n:=(Fintype.card (Γ).Mode:ℝ)) (divisor:=(κ)) hσ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Real.sqrt_nonneg _) block0 base small one fee0 roof
  change 2*((k₀)+(Fintype.card V:ℝ)*((κ)*(s*previous)))*blockSites p₀.B≤3*p₀.supportExponent/2 ∧ _
  refine ⟨?_,?_⟩
  · rw [blk,res]
    exact paid.2.2.1
  · have scale : QLocalThermalJoinedRate.charge (raw) p₀ (off₀) (s*(τ*(amt))) = (s*τ)*QLocalThermalJoinedRate.charge (raw) p₀ (off₀) (amt) := by unfold QLocalThermalJoinedRate.charge; ring
    change 2*(Fintype.card V:ℝ)*(Fintype.card (Γ).Mode:ℝ)*QLocalThermalJoinedRate.charge (raw) p₀ (off₀) (s*(τ*(amt)))≤1
    rw [scale]
    exact paid.2.2.2

theorem previous (R : Run G) (hG : G.Simple) (d : ℕ) : ∀ᶠm : ℕ in atTop,∀N p, m+1<N →
    (Real.sqrt 2*regulatorRun R.family N p (m+2))^(d+1)≤1 := by
  filter_upwards [(tendsto_add_atTop_nat 2).eventually (IterationFour.Currency.g_small hG R.makes (1/2) (by norm_num))] with m small N p below
  have hp := IterationFour.Currency.g_pos R.makes N p (m+2) below
  have cap := small N p below
  have two : Real.sqrt 2 ≤ (2:ℝ) := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  apply pow_le_one₀ (mul_nonneg (Real.sqrt_nonneg _) hp.le)
  exact (mul_le_mul_of_nonneg_right two hp.le).trans (by linarith only [cap])

end YM.Integration.WilsonRootedTwoDateHardClock
