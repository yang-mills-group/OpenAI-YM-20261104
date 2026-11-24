import YM.Integration.WilsonRetainedPaidCourse
import YM.Integration.QLocalThermalTokenTariff
import YM.RG01.Slack

/-! The original scalar Wilson gas leaves fixed support room at the acquired incoming numerical norm. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardHeadroom
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
open Overlay QuadraticLocal Extra.Iteration.Comparison
open PhysicalNext.Repeat.Daisy.Charity.RG12
open Pert.Asymptotics
universe u

open ActualWilsonDirtyPartners
variable {G : Gauge}

private theorem radius (R : Run G) (k : ℕ) :
    ((R.family.path.levels.budget k).B:ℝ)≤2*(R.family.path.levels.clock.hatBeta k)^2 := by
  let y := R.family.path.levels.clock.hatBeta k
  have hy : 1≤y := (R.family.path.levels.fits.delayed k).le
  have hl := pow_le_pow_left₀ (Real.log_nonneg hy) (Real.log_le_self (zero_le_one.trans hy)) 2
  have hc : ((R.family.path.levels.budget k).B:ℝ)≤(Real.log y)^2+1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have h₂ : 1≤y^2 := one_le_pow₀ hy
  change ((R.family.path.levels.budget k).B:ℝ)≤2*y^2
  linarith

private theorem block (R : Run G) (k : ℕ) :
    blockSites (R.family.path.levels.budget k).B≤625*(R.family.path.levels.clock.hatBeta k)^8 := by
  let b := R.family.path.levels.clock.hatBeta k
  have h : ((R.family.path.levels.budget k).B:ℝ)≤2*b^2 := radius R k
  have one : 1≤b^2 := one_le_pow₀ (R.family.path.levels.fits.delayed k).le
  unfold blockSites
  push_cast
  calc _≤(5*b^2)^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
       _=625*b^8 := by ring

theorem presold (R : Run G) (hG : G.Simple) {σ : ℝ} (hσ : 0<σ) : ∀ᶠm : ℕ in atTop,
    2*R.family.path.levels.clock.forcedAllowance (m+1)*blockSites (R.family.path.levels.budget (m+1)).B≤σ := by
  let T := R.family.path.levels
  have decay : Tendsto (fun k : ℕ=>(1250:ℝ)*(T.clock.hatBeta k^8*T.clock.forcedAllowance k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (RG01.Physical.shrink hG T 8).const_mul (1250:ℝ)
  obtain ⟨m,bought⟩ := eventually_atTop.mp (decay.eventually (gt_mem_nhds hσ))
  filter_upwards [eventually_ge_atTop m] with j hj
  calc _≤(2*T.clock.forcedAllowance (j+1))*(625*T.clock.hatBeta (j+1)^8) :=
           mul_le_mul_of_nonneg_left (block R (j+1)) (mul_nonneg (by norm_num) (Real.exp_pos _).le)
       _=1250*(T.clock.hatBeta (j+1)^8*T.clock.forcedAllowance (j+1)) := by ring
       _≤σ := (bought (j+1) (hj.trans (Nat.le_succ _))).le

private theorem lower {n:Side} (E:Activities G n) {p q : BudgetPoint} (fit : HasBudget p q)
    {k : ℝ} (bank:E.KBound p k) : E.KBound q k := by
  obtain ⟨b,sup,all⟩ := bank
  refine ⟨b,sup,fun x=>?_⟩
  apply Push.AbsoluteSums.budget_mono (all x)
  · intro i
    split
    next => exact (sup i).1.trans (q.loMass _ _ (sup i).1)
    next => exact le_rfl
  · intro i
    split
    next => exact fit.mass _ (sup i).1
    next => exact le_rfl

theorem selected {R : Run G} {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G} (hG : G.Simple)
    (fund : R2I.Funded Δ R T) (orders : ∀j,j≤(R.metals.p.profile j).order ∧ j≤(R.metals.p.profile j).power)
    {V : Type} (J : Request V) (reserve : J.inputSupport≤100) : ∀ᶠm : ℕ in atTop,
    ∀ N p (_ : m<N) (A : NumericSchedule R.family J),
      (R.family.path.rep N p (m+1)).activities.KBound (A.inputNorm m) (R.family.path.levels.clock.forcedAllowance (m+1)) ∧
      2*R.family.path.levels.clock.forcedAllowance (m+1)*blockSites (A.inputNorm m).B≤(A.inputNorm m).supportExponent := by
  filter_upwards [presold R hG J.input_support_pos,WilsonRetainedPaidCourse.selected_norm fund orders J reserve] with m headroom feasible N p below A
  have valid := (R.makes.wilson.represents N p (m+1) below).good.labels.boundK
  refine ⟨lower _ (feasible N p below A) valid,?_⟩
  simpa only [(A.input_norm m).block,(A.input_norm m).reserve] using headroom

end YM.Integration.WilsonRootedTwoDateHardHeadroom
