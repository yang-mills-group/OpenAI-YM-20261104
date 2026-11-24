import YM.Integration.WilsonRootedTwoDateHardClock
import YM.Integration.FullQLocalCostSubpower

/-! The selected radius costs a subpower of the actual next coupling for each fixed filled schedule. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardClockCost
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
open FullQLocal.PreRun.CostProfile ActualRunSubpowerShift ActualWilsonDirtyPartners WilsonRootedTwoDateHardClock
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {D : MS.Local.Physical.Deck G}

private theorem dominated (R : Run G) {f g : ℕ → ℝ} (pr : Subpower R g) (cap : ∀m,f m≤g m) :
    Subpower R f := by
  intro ε hε
  filter_upwards [pr ε hε] with m earned N p h
  exact (cap m).trans (earned N p h)

omit [DecidableEq V] [Fintype V] in
private theorem cover (R : Run G) {J : Request V} (A : NumericSchedule R.family J) (m : ℕ) :
    ((R.family.path.levels.budget (m+1)).B:ℝ) ≤ A.admittedCost m := by
  let L := R.family.path.levels
  have loop (k : ℕ) : 0≤L.clock.loopCap k := by
    change 0≤2*L.clock.monitor k^L.clock.theta (L.clock.J k)
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  have hp := (L.params m).paths_pos
  have hp' := (L.params (m+1)).paths_pos
  have hc := (L.params m).columns_ge
  have hc' := (L.params (m+1)).columns_ge
  have hr := (L.params m).clip.radius_pos
  have hr' := (L.params (m+1)).clip.radius_pos
  have bill := A.cost_covers_geometry m
  change 1+(L.clock.coverSize m:ℝ)+(L.clock.coverSize (m+1):ℝ)+L.clock.monitor m+L.clock.monitor (m+1)+
    L.clock.loopCap m+L.clock.loopCap (m+1)+(L.params m).paths+(L.params (m+1)).paths+
    (L.params m).columns+(L.params (m+1)).columns+(L.params m).clip.relaxation+(L.params (m+1)).clip.relaxation≤A.admittedCost m at bill
  change (L.clock.coverSize (m+1):ℝ)≤A.admittedCost m
  have mon (k:ℕ) : 0≤L.clock.monitor k := Real.exp_nonneg _
  linarith [loop m,loop (m+1),mon m,mon (m+1),Nat.cast_nonneg (α:=ℝ) (L.clock.coverSize m)]

omit [DecidableEq V] [Fintype V] in
private theorem block (R : Run G) (hG : G.Simple) {J : Request V} (A : NumericSchedule R.family J) :
    Subpower R (fun m=>blockSites (R.family.path.levels.budget (m+1)).B) := by
  have bill := scalar_subpower_of_schedule R A
  have twice := scalar_subpower_add R hG A _ _ bill bill
  have upper := scalar_subpower_add R hG A _ _ twice (scalar_subpower_constant R hG A 1)
  have nonneg m : 0≤A.admittedCost m+A.admittedCost m+1 := by have h:=A.admitted_cost_nonnegative m; linarith
  apply dominated R (scalar_subpower_pow R hG A _ nonneg upper 4)
  intro m
  unfold blockSites
  push_cast
  apply pow_le_pow_left₀ (by positivity) (add_le_add (add_le_add (cover R A m) (cover R A m)) (le_refl 1)) 4

theorem inverse (R : Run G) (hG : G.Simple) (J : Request V) (v : V → MS.Rake.Label D) (A : NumericSchedule R.family J) :
    Subpower R (fun m=>(rate R J v A m)⁻¹) := by
  let blocks := fun m=>blockSites (R.family.path.levels.budget (m+1)).B
  let root := fun m=>Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1))
  let c := 2*(Fintype.card V:ℝ)
  let d := c*(Fintype.card (Stock.census V).Mode:ℝ)*WilsonRootedTwoDateHardGeometry.stencilPrice R J v
  let base := min 1 (J.inputSupport/2)
  have base0 : 0<base := lt_min zero_lt_one (half_pos J.input_support_pos)
  have root0 m : 0≤root m := Real.sqrt_nonneg _
  have root1 m : root m≤1 := Real.sqrt_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_nonneg _) _)))
  have blocks0 m : 0≤blocks m := by unfold blocks blockSites;positivity
  have ex : 0≤WilsonRootedTwoDateHardGeometry.stencilPrice R J v := by
    unfold WilsonRootedTwoDateHardGeometry.stencilPrice
    have h:=J.input_support_pos
    positivity
  have c0 : 0≤c := by dsimp [c];positivity
  have d0 : 0≤d := mul_nonneg (mul_nonneg c0 (Nat.cast_nonneg _)) ex
  have x0 m : 0≤c*root m*blocks m := mul_nonneg (mul_nonneg c0 (root0 m)) (blocks0 m)
  have y0 m : 0≤d*blocks m*A.admittedCost m := mul_nonneg (mul_nonneg d0 (blocks0 m)) (A.admitted_cost_nonnegative m)
  have rsub := dominated R (scalar_subpower_constant R hG A 1) root1
  have bsub := block R hG A
  have one := scalar_subpower_constant R hG A 1
  have first := scalar_subpower_mul R _ blocks blocks0 (scalar_subpower_mul R (fun _=>c) root root0 (scalar_subpower_constant R hG A c) rsub) bsub
  have second := scalar_subpower_mul R _ A.admittedCost A.admitted_cost_nonnegative
    (scalar_subpower_mul R (fun _=>d) blocks blocks0 (scalar_subpower_constant R hG A d) bsub) (scalar_subpower_of_schedule R A)
  have sum := scalar_subpower_add R hG A _ _ (scalar_subpower_add R hG A _ _ one first) second
  have price := scalar_subpower_mul R _ (fun _=>base⁻¹) (fun _=>inv_nonneg.mpr base0.le) sum (scalar_subpower_constant R hG A base⁻¹)
  apply dominated R price
  intro m
  have term : c*(Fintype.card (Stock.census V).Mode:ℝ)*(WilsonRootedTwoDateHardGeometry.stencilPrice R J v*blocks m*A.admittedCost m)=d*blocks m*A.admittedCost m := by dsimp [d];ring
  change (base/(1+max (c*root m*blocks m) 0+max (c*(Fintype.card (Stock.census V).Mode:ℝ)*(WilsonRootedTwoDateHardGeometry.stencilPrice R J v*blocks m*A.admittedCost m)) 0))⁻¹≤(1+c*root m*blocks m+d*blocks m*A.admittedCost m)*base⁻¹
  rw [inv_div,div_eq_mul_inv,term,max_eq_left (x0 m),max_eq_left (y0 m)]

theorem graded (R : Run G) (hG : G.Simple) (J : Request V) (v : V → MS.Rake.Label D) (A : NumericSchedule R.family J) (j : ℕ) :
    Subpower R (fun m=>((rate R J v A m)^j)⁻¹) := by
  simpa only [inv_pow] using scalar_subpower_pow R hG A _ (fun m=>(inv_pos.mpr (positive R J v A m).1).le) (inverse R hG J v A) j

end YM.Integration.WilsonRootedTwoDateHardClockCost
